(* Normative-vector + composition harness for ManifestAuthentication.

   F.3 named components linked here for real:
     - SHA-256   : the `sha` library (Sha256)
     - Ed25519   : a pure-OCaml RFC 8032 verify (below), on zarith

   Checked:
     - frozen pcfw.campaign_manifest.v1 digest vector  0714f76c...
     - render_manifest byte-exact canonical form
     - official Ed25519 verify vector (RFC 8032 TEST 1, empty message)
     - Ed25519 rejects a tampered signature
     - parse_commitment_impl: wrong digest length / uppercase / non-hex /
       wrong signature length / non-hex signature
     - parse_manifest_impl: canonical roundtrip; malformed rejected
     - signature_valid_impl: digest mismatch rejected; missing key rejected;
       message is exactly utf8(mc.digest) -- NOT the decoded digest bytes,
       NOT a trailing-newline message, NOT the manifest bytes

   validate_campaign's SignerNotAuthorised-before-SignatureInvalid ordering and
   fuel accounting are unchanged Coq control flow (Orchestration.validate_campaign
   + validation_fuel_obstructed_unreachable_when_sufficient) and are not re-tested
   here. *)

module A = Extracted_manifest_auth

(* ---------- hex ---------- *)
let unhex s =
  let n = String.length s / 2 in
  String.init n (fun i -> Char.chr (int_of_string ("0x" ^ String.sub s (2*i) 2)))
let hex b =
  String.concat "" (List.init (String.length b)
    (fun i -> Printf.sprintf "%02x" (Char.code b.[i])))

(* ---------- SHA-256 (real) ---------- *)
let sha256_hex (b : string) : string = Sha256.to_hex (Sha256.string b)

(* ---------- Ed25519 verify (pure OCaml, RFC 8032) ---------- *)
module Ed25519 = struct
  let p = Z.(sub (pow (of_int 2) 255) (of_int 19))
  let el = Z.(add (pow (of_int 2) 252)
                  (of_string "27742317777372353535851937790883648493"))
  let d =
    Z.(erem (mul (sub p (of_int 121665)) (invert (of_int 121666) p)) p)  (* -121665/121666 *)
  let ( %! ) a b = Z.erem a b
  let modp a = a %! p
  let inv a = Z.invert a p

  let le_of_string s =
    let r = ref Z.zero in
    for i = String.length s - 1 downto 0 do
      r := Z.(add (shift_left !r 8) (of_int (Char.code s.[i])))
    done; !r

  (* recover x from y and sign bit *)
  let x_recover y sign =
    let y2 = modp Z.(mul y y) in
    let u = modp Z.(sub y2 one) in
    let v = modp Z.(add (mul d y2) one) in
    let xx = modp Z.(mul u (inv v)) in
    let exp = Z.(div (add p (of_int 3)) (of_int 8)) in
    let x = ref (Z.powm xx exp p) in
    if not (Z.equal (modp Z.(sub (mul !x !x) xx)) Z.zero) then begin
      let sq = Z.powm (Z.of_int 2) (Z.div (Z.sub p Z.one) (Z.of_int 4)) p in
      x := modp Z.(mul !x sq)
    end;
    if not (Z.equal (modp Z.(sub (mul !x !x) xx)) Z.zero) then None
    (* RFC 8032 5.1.3: if x = 0 and the sign bit is 1, decoding fails *)
    else if Z.equal !x Z.zero && sign = 1 then None
    else begin
      if Z.(equal (!x %! of_int 2) one) <> (sign = 1) then x := modp (Z.sub p !x);
      Some !x
    end

  let decompress (b : string) =
    if String.length b <> 32 then None else begin
      let n = le_of_string b in
      let sign = Z.(to_int (shift_right n 255)) in
      let y = Z.(logand n (sub (pow (of_int 2) 255) one)) in
      if Z.geq y p then None
      else match x_recover y sign with
        | None -> None
        | Some x -> Some (x, y)
      end

  (* twisted Edwards a = -1 affine addition *)
  let add (x1,y1) (x2,y2) =
    let dxy = modp Z.(mul (mul d (mul x1 x2)) (mul y1 y2)) in
    let x3 = modp Z.(mul (add (mul x1 y2) (mul y1 x2)) (inv (add one dxy))) in
    let y3 = modp Z.(mul (add (mul y1 y2) (mul x1 x2)) (inv (sub one dxy))) in
    (x3, y3)

  let scalar k pt =
    let acc = ref (Z.zero, Z.one) and base = ref pt and n = ref k in
    while Z.gt !n Z.zero do
      if Z.(equal (!n %! of_int 2) one) then acc := add !acc !base;
      base := add !base !base;
      n := Z.shift_right !n 1
    done; !acc

  let base =
    let by = modp Z.(mul (of_int 4) (inv (of_int 5))) in
    match x_recover by 0 with Some bx -> (bx, by) | None -> assert false

  let is_identity (x, y) = Z.equal x Z.zero && Z.equal y Z.one
  (* a point has order dividing the cofactor 8 iff [8]P is the identity *)
  let low_order pt = is_identity (scalar (Z.of_int 8) pt)

  (* trust-anchor key validation: 64 lowercase hex, decodes to a canonical,
     non-small-order edwards25519 point *)
  let valid_pubkey_hex (h : string) : bool =
    String.length h = 64
    && String.for_all (fun c -> (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')) h
    && (match decompress (unhex h) with
        | Some a -> not (low_order a)
        | None -> false)

  let byte_at z i = Z.to_int (Z.logand (Z.shift_right z (8 * i)) (Z.of_int 255))

  let compress (x, y) =
    let s = Bytes.create 32 in
    for i = 0 to 31 do Bytes.set s i (Char.chr (byte_at y i)) done;
    if Z.(equal (x %! of_int 2) one) then
      Bytes.set s 31 (Char.chr (Char.code (Bytes.get s 31) lor 128));
    Bytes.to_string s

  let le_to_string n z = String.init n (fun i -> Char.chr (byte_at z i))

  let clamp32 (b : string) =
    let a = Bytes.of_string b in
    Bytes.set a 0 (Char.chr (Char.code (Bytes.get a 0) land 248));
    Bytes.set a 31 (Char.chr ((Char.code (Bytes.get a 31) land 127) lor 64));
    Bytes.to_string a

  let sign ~sk ~msg =
    let h = Sha512.to_bin (Sha512.string sk) in
    let a = le_of_string (clamp32 (String.sub h 0 32)) in
    let prefix = String.sub h 32 32 in
    let bigA = compress (scalar a base) in
    let r = Z.erem (le_of_string (Sha512.to_bin (Sha512.string (prefix ^ msg)))) el in
    let bigR = compress (scalar r base) in
    let k = Z.erem (le_of_string (Sha512.to_bin (Sha512.string (bigR ^ bigA ^ msg)))) el in
    let s = Z.erem (Z.add r (Z.mul k a)) el in
    bigR ^ le_to_string 32 s

  let pubkey ~sk =
    let h = Sha512.to_bin (Sha512.string sk) in
    compress (scalar (le_of_string (clamp32 (String.sub h 0 32))) base)

  let verify ~pub ~sig_ ~msg =
    if String.length pub <> 32 || String.length sig_ <> 64 then false
    else match decompress pub, decompress (String.sub sig_ 0 32) with
    | Some a, Some r ->
      let s = le_of_string (String.sub sig_ 32 32) in
      if Z.geq s el then false
      else begin
        let h = Sha512.to_bin (Sha512.string
                  (String.sub sig_ 0 32 ^ pub ^ msg)) in
        let k = Z.erem (le_of_string h) el in
        let lhs = scalar s base in
        let rhs = add r (scalar k a) in
        Z.equal (fst lhs) (fst rhs) && Z.equal (snd lhs) (snd rhs)
      end
    | _ -> false
end

let ed25519_verify (pub : string) (sig_ : string) (msg : string) : bool =
  Ed25519.verify ~pub ~sig_ ~msg
let ed25519_pubkey_valid (k : string) : bool = Ed25519.valid_pubkey_hex (hex k)

(* ---------- views ---------- *)
let cd : A.context_descriptor =
  { A.cd_model_artifact_digest = "mm"; A.cd_preprocessing_digest = "pp";
    A.cd_inference_spec_digest = "ii" }
let frozen : A.campaign_manifest_view =
  { A.cm_audit_instance_id = "ai-0001"; A.cm_campaign_id = "cmp-1";
    A.cm_context_digests = cd; A.cm_policy_hash = "fb0105";
    A.cm_submission_digests = ["d1"; "d2"] }

let wire ~d ~s ~sg : A.manifest_commitment_wire =
  { A.cw_digest = d; A.cw_signer = s; A.cw_signature = sg }

let ta signers keys : A.trust_anchor =
  { A.ta_authorised_signers = signers; A.ta_keys = keys }
let cfg tanchor : A.verifier_config =
  { A.max_candidates = 0; A.max_wire_bytes = 0; A.max_transcript_bytes = 0;
    A.max_fuel = 0; A.model_call_fuel = 0; A.max_fuel_per_candidate = 0;
    A.schedule = { A.commitment_parse_fuel = 0; A.signature_verify_fuel = 0;
      A.manifest_bind_fuel = 0; A.record_bind_fuel = 0; A.preflight_fuel = 0;
      A.stage1_base_fuel = 0; A.stage1_per_byte_fuel = 0 };
    A.config_trust_anchor = tanchor }


let ed25519_sign ~sk ~msg = Ed25519.sign ~sk ~msg
let ed25519_pubkey ~sk = Ed25519.pubkey ~sk

let d64 c = String.make 64 c
let schema_valid : A.campaign_manifest_view =
  { A.cm_audit_instance_id = "ai-0001"; A.cm_campaign_id = "cmp-1";
    A.cm_context_digests =
      { A.cd_model_artifact_digest = d64 'a';
        A.cd_preprocessing_digest  = d64 'b';
        A.cd_inference_spec_digest = d64 'c' };
    A.cm_policy_hash = d64 'd';
    A.cm_submission_digests = [d64 'e'; d64 'f'] }

let () =
  (* frozen canonical bytes + digest (short placeholder digests, per 2.2.5) *)
  let canon = A.render_manifest frozen in
  assert (canon =
    {|{"audit_instance_id":"ai-0001","campaign_id":"cmp-1","context_digests":{"inference_spec_digest":"ii","model_artifact_digest":"mm","preprocessing_digest":"pp"},"policy_hash":"fb0105","submission_digests":["d1","d2"]}|});
  assert (A.campaign_manifest_digest sha256_hex frozen
          = "0714f76c7269b6e5eaa6e8348a0e84e527db842ffd0552653d49263a452bbe80");

  (* ----- Ed25519 : RFC 8032 TEST 1 (empty message) ----- *)
  let pub1 = unhex "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a" in
  let sig1 = unhex ("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555f" ^
                    "b8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b") in
  assert (ed25519_verify pub1 sig1 "" = true);
  (* Ed25519 verify here matches the RFC 8032 normative vector; the SIGN side is
     exercised by the real signed-digest end-to-end test below (sign -> verify
     via signature_valid_impl).  A fully independent signing vector would need
     the exact RFC 8032 7.1 secret key and is not reproduced here. *)
  let bad = Bytes.of_string sig1 in
  Bytes.set bad 10 (Char.chr (Char.code (Bytes.get bad 10) lxor 1));
  assert (ed25519_verify pub1 (Bytes.to_string bad) "" = false);
  (* invalid-point vectors *)
  let all_ff = String.make 32 '\xff' in              (* y >= p *)
  assert (ed25519_verify all_ff (String.make 64 '\x00') "x" = false);
  (* non-canonical identity encoding with the sign bit set: y=1, x0=1 -> reject *)
  let id_signed = "\x01" ^ String.make 30 '\x00' ^ "\x80" in
  assert (ed25519_verify id_signed (id_signed ^ String.make 32 '\x00') "x" = false);
  (* degenerate trust-anchor key rejected by key validation *)
  assert (Ed25519.valid_pubkey_hex (hex pub1) = true);
  assert (Ed25519.valid_pubkey_hex (hex ("\x01" ^ String.make 31 '\x00')) = false);
  assert (Ed25519.valid_pubkey_hex "zz" = false);

  (* ----- parse_commitment_impl rejections ----- *)
  let g64 = d64 'a' and g128 = String.make 128 'a' in
  let parsed w = match A.parse_commitment_impl w with
    | A.CommitmentParsed _ -> true | A.CommitmentParseError _ -> false in
  assert (parsed (wire ~d:g64 ~s:"s" ~sg:g128));
  assert (not (parsed (wire ~d:(String.make 63 'a') ~s:"s" ~sg:g128)));
  assert (not (parsed (wire ~d:(String.make 64 'A') ~s:"s" ~sg:g128)));
  assert (not (parsed (wire ~d:(String.make 63 'a' ^ "g") ~s:"s" ~sg:g128)));
  assert (not (parsed (wire ~d:g64 ~s:"s" ~sg:(String.make 127 'a'))));
  assert (not (parsed (wire ~d:g64 ~s:"s" ~sg:(String.make 127 'a' ^ "x"))));

  (* ----- parse_manifest_impl : schema conformance ----- *)
  assert (A.parse_manifest_impl (A.render_manifest schema_valid) = Some schema_valid);
  assert (A.parse_manifest_impl canon = None);                (* short digests *)
  assert (A.parse_manifest_impl "{}" = None);
  assert (A.parse_manifest_impl
            ({|{"audit_instance_id":"ai-0001",|} ^ {|"campaign_id":"x"}|}) = None);
  (* string replace-first helper (no Str dependency) *)
  let repl old rep s =
    let n = String.length old and m = String.length s in
    let rec go i =
      if i + n > m then s
      else if String.sub s i n = old
      then String.sub s 0 i ^ rep ^ String.sub s (i + n) (m - i - n)
      else go (i + 1) in
    go 0 in
  let sv_bytes = A.render_manifest schema_valid in
  (* trailing comma in the digest array *)
  let tc = repl ("\"" ^ d64 'f' ^ "\"]") ("\"" ^ d64 'f' ^ "\",]") sv_bytes in
  assert (A.parse_manifest_impl tc = None);
  (* raw control byte in a value *)
  assert (A.parse_manifest_impl (repl "ai-0001" "ai\x01001" sv_bytes) = None);
  (* invalid UTF-8 *)
  assert (A.parse_manifest_impl (repl "ai-0001" "ai\xff001" sv_bytes) = None);
  (* escape decoding: a value carrying a quote and backslash round-trips *)
  let esc_view = { schema_valid with A.cm_audit_instance_id = "a\"b\\c" } in
  assert (A.parse_manifest_impl (A.render_manifest esc_view) = Some esc_view);

  (* ----- signature_valid_impl : real end-to-end + composition ----- *)
  let signer = "release" in
  let sk = unhex "9d61b19deffdefff1c95bf2be5aa39d8a0b52e5e6a1d81e7e60a5f4b0d0c8b3a1" in
  let pk = ed25519_pubkey ~sk in
  let good_digest = A.campaign_manifest_digest sha256_hex schema_valid in
  let real_sig = ed25519_sign ~sk ~msg:good_digest in
  let mc ~dg ~sig_ : A.manifest_commitment =
    { A.commitment_digest = dg; A.commitment_signer = signer;
      A.commitment_signature = sig_ } in
  let c_real = cfg (ta [signer] [(signer, pk)]) in
  let sv_bytes' = A.render_manifest schema_valid in
  (* REAL positive: digest recomputed, key found, signature verifies over utf8(digest) *)
  assert (A.signature_valid_impl sha256_hex ed25519_verify ed25519_pubkey_valid c_real
            (mc ~dg:good_digest ~sig_:real_sig) sv_bytes' = true);
  (* signature over the wrong message form -> rejected *)
  assert (A.signature_valid_impl sha256_hex ed25519_verify ed25519_pubkey_valid c_real
            (mc ~dg:good_digest ~sig_:(ed25519_sign ~sk ~msg:(good_digest ^ "\n")))
            sv_bytes' = false);
  assert (A.signature_valid_impl sha256_hex ed25519_verify ed25519_pubkey_valid c_real
            (mc ~dg:good_digest ~sig_:(ed25519_sign ~sk ~msg:(unhex good_digest)))
            sv_bytes' = false);
  (* composition: digest mismatch -> false with NO verify call *)
  let calls = ref [] in
  let spy _k _s msg = calls := msg :: !calls; false in
  let ok_pk _k = true in
  assert (A.signature_valid_impl sha256_hex spy ok_pk c_real
            (mc ~dg:(d64 '0') ~sig_:real_sig) sv_bytes' = false);
  assert (!calls = []);
  (* digest agrees -> spy called with EXACTLY the digest string *)
  calls := [];
  ignore (A.signature_valid_impl sha256_hex spy ok_pk c_real
            (mc ~dg:good_digest ~sig_:real_sig) sv_bytes');
  assert (!calls = [good_digest]);
  assert (not (List.mem (good_digest ^ "\n") !calls));
  assert (not (List.mem (unhex good_digest) !calls));
  assert (not (List.mem sv_bytes' !calls));
  (* missing key -> false *)
  assert (A.signature_valid_impl sha256_hex ed25519_verify ed25519_pubkey_valid (cfg (ta [signer] []))
            (mc ~dg:good_digest ~sig_:real_sig) sv_bytes' = false);
  (* a degenerate (identity) trust-anchor key is rejected on the actual
     validation path -- signature_valid_impl runs ed25519_pubkey_valid k *)
  let id_key = "\x01" ^ String.make 31 '\x00' in
  assert (A.signature_valid_impl sha256_hex (fun _ _ _ -> true) ed25519_pubkey_valid
            (cfg (ta [signer] [(signer, id_key)]))
            (mc ~dg:good_digest ~sig_:real_sig) sv_bytes' = false);
  (* signer authorisation *)
  assert (A.signer_authorised_impl c_real (mc ~dg:good_digest ~sig_:real_sig) = true);
  assert (A.signer_authorised_impl (cfg (ta ["other"] []))
            (mc ~dg:good_digest ~sig_:real_sig) = false);

  (* ----- op_ledger_mismatch : ld_mismatch on the raw digest lists ----- *)
  let deq = (fun (a : string) b -> a = b) in
  let d1 = d64 'e' and d2 = d64 'f' and d3 = d64 'g' in
  (* equal -> None *)
  assert (A.ld_mismatch deq [d1; d2] [d1; d2] = None);
  assert (A.ld_mismatch deq [] [] = None);
  (* reorder -> least differing index 0 *)
  assert (A.ld_mismatch deq [d1; d2] [d2; d1] = Some 0);
  (* one element changed mid-list -> that index, not a later one *)
  assert (A.ld_mismatch deq [d1; d2; d3] [d1; d3; d3] = Some 1);
  (* add (manifest longer) -> first length-divergence index *)
  assert (A.ld_mismatch deq [d1; d2; d3] [d1; d2] = Some 2);
  (* remove (manifest shorter) -> first length-divergence index *)
  assert (A.ld_mismatch deq [d1; d2] [d1; d2; d3] = Some 2);
  (* duplicate where a distinct digest was expected *)
  assert (A.ld_mismatch deq [d1; d1] [d1; d2] = Some 1);
  (* least index reported: agree on a 2-element prefix, diverge at 2 *)
  assert (A.ld_mismatch deq [d1; d2; d1; d2] [d1; d2; d3; d1] = Some 2);

  (* ----- op_ledger_mismatch : end-to-end through parse_manifest_impl ----- *)
  let mk_sub d : A.candidate_submission =
    { A.submission_wire = ""; A.submission_wire_length = 0;
      A.submission_digest = d } in
  let m_bytes = A.render_manifest schema_valid in         (* digests [d64 'e'; d64 'f'] *)
  let subs_ok = [mk_sub (d64 'e'); mk_sub (d64 'f')] in
  assert (A.ledger_mismatch_impl deq A.parse_manifest_impl m_bytes subs_ok = None);
  (* reorder the submission list *)
  assert (A.ledger_mismatch_impl deq A.parse_manifest_impl m_bytes
            [mk_sub (d64 'f'); mk_sub (d64 'e')] = Some 0);
  (* drop the last submission -> length divergence at index 1 *)
  assert (A.ledger_mismatch_impl deq A.parse_manifest_impl m_bytes
            [mk_sub (d64 'e')] = Some 1);
  (* append an extra submission -> length divergence at index 2 *)
  assert (A.ledger_mismatch_impl deq A.parse_manifest_impl m_bytes
            (subs_ok @ [mk_sub (d64 'g')]) = Some 2);
  (* duplicate the first submission -> mismatch at index 1 *)
  assert (A.ledger_mismatch_impl deq A.parse_manifest_impl m_bytes
            [mk_sub (d64 'e'); mk_sub (d64 'e')] = Some 1);
  (* manifest fails to decode -> mismatch at index 0 (no ledger to compare) *)
  assert (A.ledger_mismatch_impl deq A.parse_manifest_impl "{}" subs_ok = Some 0);

  (* ----- op_manifest_audit_matches (step 5): exact-string identity ----- *)
  let mk_ti ~policy : A.trusted_inputs =
    { A.ti_commitment_wire = wire ~d:"" ~s:"" ~sg:"";
      A.ti_manifest = ""; A.ti_submissions = []; A.ti_record = "";
      A.ti_completeness = A.CompletenessUnknown;
      A.ti_config = cfg (ta [] []); A.ti_policy_document = "";
      A.ti_policy = policy; A.ti_policy_digest = "" } in
  let ti0 = mk_ti ~policy:"p" in
  (* schema_valid.cm_audit_instance_id = "ai-0001" *)
  let const_id s = (fun (_ : string) -> s) in
  (* matching identity *)
  assert (A.manifest_audit_matches_impl A.parse_manifest_impl (const_id "ai-0001")
            m_bytes ti0 = true);
  (* differing identity *)
  assert (A.manifest_audit_matches_impl A.parse_manifest_impl (const_id "ai-9999")
            m_bytes ti0 = false);
  (* case difference -> not equal (exact string equality, case-sensitive) *)
  assert (A.manifest_audit_matches_impl A.parse_manifest_impl (const_id "AI-0001")
            m_bytes ti0 = false);
  (* non-decoding manifest -> false *)
  assert (A.manifest_audit_matches_impl A.parse_manifest_impl (const_id "ai-0001")
            "{}" ti0 = false);
  (* the id is read from policy_audit_instance_id_of (ti_policy ti) *)
  assert (A.manifest_audit_matches_impl A.parse_manifest_impl (fun p -> p)
            m_bytes (mk_ti ~policy:"ai-0001") = true);
  assert (A.manifest_audit_matches_impl A.parse_manifest_impl (fun p -> p)
            m_bytes (mk_ti ~policy:"ai-0002") = false);

  (* ----- op_record_identity_mismatch (step 8): 5 identity fields, frozen order ----- *)
  (* a record view whose 5 identity fields match schema_valid + good_digest *)
  let rec_cd : A.context_descriptor =
    { A.cd_model_artifact_digest = d64 'a'; A.cd_preprocessing_digest = d64 'b';
      A.cd_inference_spec_digest = d64 'c' } in
  let rv_ok : A.campaign_record_view =
    { A.crv_campaign_id = "cmp-1"; A.crv_audit_instance_id = "ai-0001";
      A.crv_policy_hash = d64 'd'; A.crv_context_digests = rec_cd;
      A.crv_manifest_digest = good_digest } in
  let mc8 = mc ~dg:good_digest ~sig_:real_sig in
  let rim rv rbytes mbytes =
    A.record_identity_mismatch_impl A.parse_record_impl A.parse_manifest_impl
      (match rbytes with Some b -> b | None -> A.render_campaign_record rv)
      mc8 mbytes in
  (* complete matching case -> None *)
  assert (rim rv_ok None sv_bytes' = None);
  (* each identity field, individually mismatched -> Some <that field> *)
  assert (rim { rv_ok with A.crv_campaign_id = "other" } None sv_bytes'
          = Some "campaign_id");
  assert (rim { rv_ok with A.crv_audit_instance_id = "ai-9999" } None sv_bytes'
          = Some "audit_instance_id");
  assert (rim { rv_ok with A.crv_policy_hash = d64 'f' } None sv_bytes'
          = Some "policy_hash");
  assert (rim { rv_ok with A.crv_context_digests =
                 { rec_cd with A.cd_preprocessing_digest = d64 'f' } } None sv_bytes'
          = Some "context_digests");
  assert (rim { rv_ok with A.crv_manifest_digest = d64 'e' } None sv_bytes'
          = Some "manifest_digest");
  (* multiple mismatches -> earliest field in the frozen order *)
  assert (rim { rv_ok with A.crv_campaign_id = "x"; A.crv_policy_hash = d64 'f' }
            None sv_bytes' = Some "campaign_id");
  assert (rim { rv_ok with A.crv_policy_hash = d64 'f';
                A.crv_manifest_digest = d64 'e' } None sv_bytes' = Some "policy_hash");
  (* case-only identifier difference is a mismatch *)
  assert (rim { rv_ok with A.crv_audit_instance_id = "AI-0001" } None sv_bytes'
          = Some "audit_instance_id");
  assert (rim { rv_ok with A.crv_campaign_id = "CMP-1" } None sv_bytes'
          = Some "campaign_id");
  (* record decoder failure -> deterministic sentinel, distinct from field names *)
  assert (rim rv_ok (Some "{}") sv_bytes' = Some A.sentinel_record_undecodable);
  assert (A.sentinel_record_undecodable = "!record_undecodable");
  (* manifest decoder failure -> its own sentinel *)
  assert (rim rv_ok None "{}" = Some A.sentinel_manifest_undecodable);
  assert (A.sentinel_manifest_undecodable = "!manifest_undecodable");
  (* both decoders fail -> record sentinel (record checked first) *)
  assert (rim rv_ok (Some "{}") "{}" = Some A.sentinel_record_undecodable);
  (* neither sentinel can be mistaken for a field name *)
  assert (not (List.mem A.sentinel_record_undecodable
                 ["campaign_id";"audit_instance_id";"policy_hash";
                  "context_digests";"manifest_digest"]));
  assert (not (List.mem A.sentinel_manifest_undecodable
                 ["campaign_id";"audit_instance_id";"policy_hash";
                  "context_digests";"manifest_digest"]));
  (* the record view round-trips through parse_record_impl *)
  assert (A.parse_record_impl (A.render_campaign_record rv_ok) = Some rv_ok);

  (* ----- end-to-end: a NORMATIVE FULL campaign record ----- *)
  (* canonical 8-key record; `completeness` is the payload-carrying
     {"k":"complete","v":{"body":...,"scheme":...}}; `recorded_results` has a
     no-payload ("valid_witness") entry and a payload-carrying
     ({"k":"not_a_witness","v":"inputs_equal"}) entry; `resource_budget` is
     populated.  Every nested object's keys are strictly byte-ascending.
     `parse_record_impl` skips those three and extracts the five identity fields *)
  let cds =
    "\"context_digests\":{\"inference_spec_digest\":\"" ^ d64 'c' ^
      "\",\"model_artifact_digest\":\"" ^ d64 'a' ^
      "\",\"preprocessing_digest\":\"" ^ d64 'b' ^ "\"}" in
  let full_rec ~budget =
    "{\"audit_instance_id\":\"ai-0001\",\"campaign_id\":\"cmp-1\"," ^
    "\"completeness\":{\"k\":\"complete\",\"v\":" ^
      "{\"body\":\"b\",\"scheme\":\"registry-v0\"}}," ^
    cds ^ "," ^
    "\"manifest_digest\":\"" ^ good_digest ^ "\"," ^
    "\"policy_hash\":\"" ^ d64 'd' ^ "\"," ^
    "\"recorded_results\":[" ^
      "{\"findings\":[]," ^
       "\"outcome\":{\"k\":\"accepted\",\"v\":\"valid_witness\"}," ^
       "\"submission_digest\":\"" ^ d64 'e' ^ "\",\"submission_index\":0}," ^
      "{\"findings\":[{\"check_id\":\"C1\",\"outcome\":\"fail\",\"reason\":\"inputs_equal\"}]," ^
       "\"outcome\":{\"k\":\"accepted\",\"v\":{\"k\":\"not_a_witness\",\"v\":\"inputs_equal\"}}," ^
       "\"submission_digest\":\"" ^ d64 'f' ^ "\",\"submission_index\":1}]," ^
    "\"resource_budget\":" ^ budget ^ "}" in
  (* a record with a caller-supplied recorded_results array + budget *)
  let mk_record ~rr ~budget =
    "{\"audit_instance_id\":\"ai-0001\",\"campaign_id\":\"cmp-1\"," ^
    "\"completeness\":\"unknown\"," ^ cds ^ "," ^
    "\"manifest_digest\":\"" ^ good_digest ^ "\"," ^
    "\"policy_hash\":\"" ^ d64 'd' ^ "\"," ^
    "\"recorded_results\":" ^ rr ^ ",\"resource_budget\":" ^ budget ^ "}" in
  let fr = full_rec ~budget:"{\"max_candidates\":10,\"max_memory_bytes\":1048576}" in
  (* the five identity fields decode; the three skipped fields do not block it *)
  assert (A.parse_record_impl fr = Some rv_ok);
  (* and the wired comparison passes against the matching manifest *)
  assert (rim rv_ok (Some fr) sv_bytes' = None);
  (* a full record whose recorded `campaign_id` disagrees -> Some "campaign_id" *)
  assert (rim rv_ok
            (Some (repl "\"campaign_id\":\"cmp-1\"" "\"campaign_id\":\"cmp-2\"" fr))
            sv_bytes' = Some "campaign_id");
  (* the identity-only mini-form is REJECTED -- a full record is required *)
  let identity_only =
    "{\"audit_instance_id\":\"ai-0001\",\"campaign_id\":\"cmp-1\"," ^ cds ^ "," ^
    "\"manifest_digest\":\"" ^ good_digest ^ "\"," ^
    "\"policy_hash\":\"" ^ d64 'd' ^ "\"}" in
  assert (A.parse_record_impl identity_only = None);
  assert (rim rv_ok (Some identity_only) sv_bytes' = Some A.sentinel_record_undecodable);
  (* ----- skip_value enforces canonical syntax in skipped objects ----- *)
  assert (A.parse_record_impl (full_rec ~budget:"{\"max_candidates\":01}") = None);   (* leading zero *)
  assert (A.parse_record_impl (full_rec ~budget:"{\"max_candidates\":-0}") = None);   (* -0 *)
  assert (A.parse_record_impl                                                        (* duplicate key *)
            (full_rec ~budget:"{\"max_candidates\":1,\"max_candidates\":2}") = None);
  assert (A.parse_record_impl                                                        (* descending keys *)
            (full_rec ~budget:"{\"max_memory_bytes\":1,\"max_candidates\":2}") = None);
  assert (A.parse_record_impl (full_rec ~budget:"{\"max_candidates\":0}") = Some rv_ok); (* lone 0 ok *)
  assert (A.parse_record_impl (full_rec ~budget:"{\"max_candidates\":-7}") = Some rv_ok); (* -7 ok *)

  (* ----- op_record_crosscheck: fully typed submission_check_result ----- *)
  let fnd cid oc rsn off : A.finding =
    { A.finding_check_id = cid; A.finding_outcome = oc;
      A.finding_reason = rsn; A.finding_offending = off } in
  (match A.parse_record_full_impl fr with
   | None -> assert false
   | Some rf ->
       assert (rf.A.rf_identity = rv_ok);
       assert (List.map (fun e -> e.A.scr_index) rf.A.rf_recorded = [0; 1]);
       assert (List.map (fun e -> e.A.scr_digest) rf.A.rf_recorded = [d64 'e'; d64 'f']);
       assert (List.map (fun e -> e.A.scr_candidate_id) rf.A.rf_recorded = [None; None]);
       assert (List.map (fun e -> e.A.scr_outcome) rf.A.rf_recorded
               = [A.ScrValidWitness; A.ScrNotAWitness A.InputsEqual]);
       assert (List.map (fun e -> e.A.scr_findings) rf.A.rf_recorded
               = [ []; [ fnd "C1" A.Fail (Some "inputs_equal") None ] ]);
       assert (rf.A.rf_budget.A.rb_max_candidates = Some 10);
       assert (A.parse_record_impl fr = Some rf.A.rf_identity));   (* forward projection *)
  (* the typed finding decoder captures `offending` and enforces the check_id set *)
  (match A.parse_record_full_impl
     (mk_record
        ~rr:("[{\"findings\":[{\"check_id\":\"C1\",\"offending\":[1,2]," ^
              "\"outcome\":\"fail\",\"reason\":\"inputs_equal\"}]," ^
              "\"outcome\":{\"k\":\"accepted\",\"v\":\"valid_witness\"}," ^
              "\"submission_digest\":\"" ^ d64 'e' ^ "\",\"submission_index\":0}]")
        ~budget:"{}") with
   | Some rf -> assert (List.map (fun e -> e.A.scr_findings) rf.A.rf_recorded
                        = [ [ fnd "C1" A.Fail (Some "inputs_equal") (Some "[1,2]") ] ])
   | None -> assert false);
  assert (A.parse_record_full_impl                                (* invalid check_id -> reject *)
            (mk_record
               ~rr:("[{\"findings\":[{\"check_id\":\"ZZ\",\"outcome\":\"pass\"}]," ^
                     "\"outcome\":{\"k\":\"accepted\",\"v\":\"valid_witness\"}," ^
                     "\"submission_digest\":\"" ^ d64 'e' ^ "\",\"submission_index\":0}]")
               ~budget:"{}") = None);
  assert (A.parse_scr_outcome "{\"k\":\"rejected\",\"v\":\"not_a_real_reason\"}" = None);
  (* parse_budget_object canonicality *)
  assert (A.parse_budget_object "{\"max_candidates\":10}" <> None);
  assert (A.parse_budget_object "{}" <> None);
  assert (A.parse_budget_object "{\"max_memory_bytes\":1,\"max_candidates\":2}" = None);
  assert (A.parse_budget_object "{\"max_candidates\":01}" = None);
  assert (A.parse_budget_object "{\"max_candidates\":1,\"max_candidates\":2}" = None);
  assert (A.parse_budget_object "{\"max_wobble\":1}" = None);
  (* crosscheck_budget_impl: rec.resource_budget is ADVISORY vs verifier_config *)
  let cfg_mc n : A.verifier_config = { (cfg (ta [] [])) with A.max_candidates = n } in
  let b0 = A.empty_budget in
  assert (A.crosscheck_budget_impl { b0 with A.rb_max_candidates = Some 10 } (cfg_mc 10) = []);
  assert (List.exists (fun f -> f.A.finding_outcome = A.Fail)
            (A.crosscheck_budget_impl { b0 with A.rb_max_candidates = Some 5 } (cfg_mc 10)));
  assert (List.for_all (fun f -> f.A.finding_outcome = A.NotEvaluated)
            (A.crosscheck_budget_impl { b0 with A.rb_max_wall_clock_seconds = Some 3 } (cfg_mc 10)));
  (* crosscheck_impl vs the replay-derived expectation -- crosscheck_impl_nil_iff *)
  let rf_of rs : A.campaign_record_full_view =
    { A.rf_identity = rv_ok; A.rf_recorded = rs; A.rf_budget = b0 } in
  let mm l = List.exists (fun f -> f.A.finding_check_id = "campaign_record_mismatch") l in
  let s1r i sd cid sem v fs : A.stage1_slot =
    { A.stage1_slot_index = i;
      A.stage1_slot_result = A.Done
        { A.s1_index = i; A.s1_submission_digest = sd;
          A.s1_candidate_id = cid; A.s1_semantic_digest = sem;
          A.s1_verdict = v; A.s1_findings = fs } } in
  let scr i sd cid sem oc fs : A.scr_view =
    { A.scr_index = i; A.scr_digest = sd; A.scr_candidate_id = cid;
      A.scr_semantic = sem; A.scr_outcome = oc; A.scr_findings = fs } in
  (* --- REJECTED (not parsed): candidate_id / semantic = None; a B-finding with `offending` --- *)
  let bf = fnd "B4" A.Fail (Some "input_structure_error") (Some "[3]") in
  assert (A.crosscheck_impl
            (rf_of [ scr 0 (d64 'e') None None (A.ScrRejected A.InputStructureError) [bf] ])
            [ s1r 0 (d64 'e') None None (A.S1Rejected A.InputStructureError) [bf] ] [] = []);
  assert (mm (A.crosscheck_impl                                          (* offending value mutated *)
                (rf_of [ scr 0 (d64 'e') None None (A.ScrRejected A.InputStructureError)
                           [ { bf with A.finding_offending = Some "[9]" } ] ])
                [ s1r 0 (d64 'e') None None (A.S1Rejected A.InputStructureError) [bf] ] []));
  assert (mm (A.crosscheck_impl                                          (* offending dropped *)
                (rf_of [ scr 0 (d64 'e') None None (A.ScrRejected A.InputStructureError)
                           [ { bf with A.finding_offending = None } ] ])
                [ s1r 0 (d64 'e') None None (A.S1Rejected A.InputStructureError) [bf] ] []));
  (* --- PARSED NOT-A-WITNESS: candidate_id / semantic digest are Some --- *)
  let naw = A.S1NotAWitness A.InputsEqual in
  assert (A.crosscheck_impl
            (rf_of [ scr 0 (d64 'e') (Some "c-1") (Some (d64 'a')) (A.ScrNotAWitness A.InputsEqual) [] ])
            [ s1r 0 (d64 'e') (Some "c-1") (Some (d64 'a')) naw [] ] [] = []);
  assert (mm (A.crosscheck_impl                                          (* candidate_id mutated *)
                (rf_of [ scr 0 (d64 'e') (Some "c-2") (Some (d64 'a')) (A.ScrNotAWitness A.InputsEqual) [] ])
                [ s1r 0 (d64 'e') (Some "c-1") (Some (d64 'a')) naw [] ] []));
  assert (mm (A.crosscheck_impl                                          (* semantic digest for a parsed non-witness mutated *)
                (rf_of [ scr 0 (d64 'e') (Some "c-1") (Some (d64 'b')) (A.ScrNotAWitness A.InputsEqual) [] ])
                [ s1r 0 (d64 'e') (Some "c-1") (Some (d64 'a')) naw [] ] []));
  assert (mm (A.crosscheck_impl                                          (* semantic digest omitted *)
                (rf_of [ scr 0 (d64 'e') (Some "c-1") None (A.ScrNotAWitness A.InputsEqual) [] ])
                [ s1r 0 (d64 'e') (Some "c-1") (Some (d64 'a')) naw [] ] []));
  (* --- isolated wrong submission_digest --- *)
  assert (mm (A.crosscheck_impl
                (rf_of [ scr 0 (d64 'x') None None (A.ScrRejected A.InputStructureError) [bf] ])
                [ s1r 0 (d64 'e') None None (A.S1Rejected A.InputStructureError) [bf] ] []));
  (* --- reorder / count / wrong outcome --- *)
  assert (mm (A.crosscheck_impl
                (rf_of [ scr 1 (d64 'e') None None (A.ScrRejected A.InvalidUtf8) [];
                         scr 0 (d64 'f') None None (A.ScrRejected A.InvalidUtf8) [] ])
                [ s1r 0 (d64 'e') None None (A.S1Rejected A.InvalidUtf8) [];
                  s1r 1 (d64 'f') None None (A.S1Rejected A.InvalidUtf8) [] ] []));
  assert (mm (A.crosscheck_impl (rf_of [])
                [ s1r 0 (d64 'e') None None (A.S1Rejected A.InvalidUtf8) [] ] []));
  (* --- stage-1 NotRun: NO submission_check_result is derived (filtered out); a
         recorded claim for that slot is an extra entry -> mismatch --- *)
  let s1nr i : A.stage1_slot = { A.stage1_slot_index = i; A.stage1_slot_result = A.NotRun } in
  let s2nr i : A.stage2_slot = { A.stage2_slot_index = i; A.stage2_slot_result = A.NotRun } in
  assert (A.derive_expected [ s1nr 0 ] [] = []);
  assert (mm (A.crosscheck_impl
                (rf_of [ scr 0 (d64 'e') None None A.ScrValidWitness [] ]) [ s1nr 0 ] []));
  assert (A.crosscheck_impl (rf_of []) [ s1nr 0 ] [] = []);   (* no claim, no slot -> ok *)
  (* --- VALID_WITNESS via stage 2 --- *)
  let pc : A.parsed_candidate = { A.pc_candidate_id = "c-1"; A.candidate_x = []; A.candidate_y = [] } in
  let s1pend i sd sem : A.stage1_slot =
    s1r i sd (Some "c-1") (Some sem)
      (A.S1Pending { A.pending_index = i; A.pending_submission_digest = sd;
                     A.pending_semantic_digest = sem; A.pending_candidate = pc;
                     A.pending_findings = [] }) [] in
  let s2valid i sd sem : A.stage2_slot =
    { A.stage2_slot_index = i;
      A.stage2_slot_result = A.Done
        { A.s2_index = i;
          A.s2_verdict = A.ValidWitness
            { A.witness_index = i; A.witness_submission_digest = sd;
              A.witness_semantic_digest = sem; A.witness_x = []; A.witness_y = [];
              A.witness_o_x = []; A.witness_o_y = []; A.witness_findings = [] };
          A.s2_findings = [] } } in
  assert (A.crosscheck_impl
            (rf_of [ scr 0 (d64 'e') (Some "c-1") (Some (d64 'a')) A.ScrValidWitness [] ])
            [ s1pend 0 (d64 'e') (d64 'a') ] [ s2valid 0 (d64 'e') (d64 'a') ] = []);
  assert (mm (A.crosscheck_impl
                (rf_of [ scr 0 (d64 'e') (Some "c-1") (Some (d64 'a'))
                           (A.ScrNotAWitness A.InputsEqual) [] ])
                [ s1pend 0 (d64 'e') (d64 'a') ] [ s2valid 0 (d64 'e') (d64 'a') ]));
  (* --- S1Pending whose stage-2 slot is NotRun: also filtered out --- *)
  assert (A.derive_expected [ s1pend 0 (d64 'e') (d64 'a') ] [ s2nr 0 ] = []);
  assert (mm (A.crosscheck_impl
                (rf_of [ scr 0 (d64 'e') (Some "c-1") (Some (d64 'a')) A.ScrValidWitness [] ])
                [ s1pend 0 (d64 'e') (d64 'a') ] [ s2nr 0 ]));

  (* ----- mutation tests THROUGH the decoder (parse_record_full_impl), not
     hand-built views: positive, wrong submission_digest, wrong submission_index,
     and NotRun alignment ----- *)
  let rr_one ~sd ~si =
    "[{\"candidate_id\":\"c-1\",\"findings\":[]," ^
     "\"outcome\":{\"k\":\"accepted\",\"v\":\"valid_witness\"}," ^
     "\"semantic_candidate_digest\":\"" ^ d64 'a' ^ "\"," ^
     "\"submission_digest\":\"" ^ sd ^ "\",\"submission_index\":" ^ si ^ "}]" in
  let dec_cc rr s1 s2 =
    match A.parse_record_full_impl (mk_record ~rr ~budget:"{}") with
    | Some rf -> A.crosscheck_impl rf s1 s2
    | None -> assert false in
  let rpl = [ s1pend 0 (d64 'e') (d64 'a') ] and rp2 = [ s2valid 0 (d64 'e') (d64 'a') ] in
  assert (dec_cc (rr_one ~sd:(d64 'e') ~si:"0") rpl rp2 = []);          (* positive, via decoder *)
  assert (mm (dec_cc (rr_one ~sd:(d64 'f') ~si:"0") rpl rp2));          (* wrong submission_digest *)
  assert (mm (dec_cc (rr_one ~sd:(d64 'e') ~si:"1") rpl rp2));          (* wrong submission_index *)
  assert (mm (dec_cc (rr_one ~sd:(d64 'e') ~si:"0") [ s1nr 0 ] []));    (* NotRun alignment *)

  (* record_crosscheck_impl end-to-end: a full record whose recorded results match
     the replay -> no mismatch finding *)
  let ac_of rec_str : A.authenticated_campaign =
    { A.authenticated_commitment = mc ~dg:good_digest ~sig_:real_sig;
      A.authenticated_manifest = ""; A.authenticated_submissions = [];
      A.authenticated_record = rec_str;
      A.authenticated_completeness = A.CompletenessUnknown } in
  let ee_rec =
    mk_record
      ~rr:("[{\"candidate_id\":\"c-1\",\"findings\":[]," ^
            "\"outcome\":{\"k\":\"accepted\",\"v\":\"valid_witness\"}," ^
            "\"semantic_candidate_digest\":\"" ^ d64 'a' ^ "\"," ^
            "\"submission_digest\":\"" ^ d64 'e' ^ "\",\"submission_index\":0}]")
      ~budget:"{\"max_candidates\":10}" in
  assert (not (mm (A.record_crosscheck_impl A.parse_record_full_impl (ac_of ee_rec)
                     [ s1pend 0 (d64 'e') (d64 'a') ]
                     [ s2valid 0 (d64 'e') (d64 'a') ] (cfg_mc 10))));
  assert (A.record_crosscheck_impl A.parse_record_full_impl (ac_of "{}") [] [] (cfg_mc 10)
          = [ fnd "campaign_record_undecodable" A.Fail None None ]);
  (* every advisory finding record_crosscheck_impl emits is in the closed
     3-element identifier family (record_crosscheck_impl_ids) *)
  let adv_ids = [ "budget_advisory"; "campaign_record_mismatch"; "campaign_record_undecodable" ] in
  assert (A.advisory_finding_ids = adv_ids);
  assert (List.for_all (fun f -> List.mem f.A.finding_check_id A.advisory_finding_ids)
            (A.record_crosscheck_impl A.parse_record_full_impl
               (ac_of (mk_record ~rr:(rr_one ~sd:(d64 'f') ~si:"0")
                         ~budget:"{\"max_candidates\":3,\"max_memory_bytes\":9}"))
               rpl rp2 (cfg_mc 10)));

  (* op_completeness_wellformed_impl (VERDICT_SEMANTICS.md 5 step 9): a pure
     structural check on the already-typed completeness_status.  Unknown /
     Incomplete carry no certificate -> unconditionally well-formed. *)
  assert (A.op_completeness_wellformed_impl A.CompletenessUnknown);
  assert (A.op_completeness_wellformed_impl A.CompletenessIncomplete);
  let cert scheme body =
    A.CompletenessComplete { A.completeness_scheme = scheme; A.completeness_body = body } in
  (* well-formed: a non-empty scheme (any decoded bytes -- see below) + a body
     that is exactly one ASCII-wire canonical value *)
  assert (A.op_completeness_wellformed_impl (cert "scheme-v1" "{\"a\":1}"));
  assert (A.op_completeness_wellformed_impl (cert "scheme-v1" "true"));
  assert (A.op_completeness_wellformed_impl (cert "scheme-v1" "\"x\""));
  (* revision-2 fix: a quote, a backslash, and a raw high byte in a DECODED
     scheme string are all legitimate data, NOT malformed -- scheme:<string>
     imposes no further wire grammar (reviewer HOLD on revision 1, blocker 1) *)
  assert (A.op_completeness_wellformed_impl (cert "sch\"eme" "{\"a\":1}"));
  assert (A.op_completeness_wellformed_impl (cert "sch\\eme" "{\"a\":1}"));
  assert (A.op_completeness_wellformed_impl
            (cert (String.make 1 (Char.chr 233)) "{\"a\":1}"));
  assert (A.op_completeness_wellformed_impl (cert (String.make 1 (Char.chr 127)) "{\"a\":1}"));
  (* every remaining failure class: empty scheme (the only scheme-side
     rejection there is); empty body; body with trailing garbage after one
     value; body with a leading-zero integer (skip_value's canonical-number
     grammar); body with duplicate object keys (skip_value's
     strict-ascending-key grammar); body that isn't JSON at all; a body string
     containing a raw high byte (still out of v0's ASCII-wire subset -- unlike
     a bare scheme string, a body STRING still goes through the canonical
     string grammar) *)
  assert (not (A.op_completeness_wellformed_impl (cert "" "{\"a\":1}")));
  assert (not (A.op_completeness_wellformed_impl (cert "scheme-v1" "")));
  assert (not (A.op_completeness_wellformed_impl (cert "scheme-v1" "5x")));
  assert (not (A.op_completeness_wellformed_impl (cert "scheme-v1" "01")));
  assert (not (A.op_completeness_wellformed_impl (cert "scheme-v1" "{\"a\":1,\"a\":2}")));
  assert (not (A.op_completeness_wellformed_impl (cert "scheme-v1" "not-json")));
  assert (not (A.op_completeness_wellformed_impl
                 (cert "scheme-v1" ("\"" ^ String.make 1 (Char.chr 233) ^ "\""))));
  (* the two structural checks in isolation, matching the Coq normative vectors *)
  assert (A.wellformed_scheme "scheme-v1");
  assert (not (A.wellformed_scheme ""));
  assert (A.wellformed_scheme "sch\"eme");
  assert (A.wellformed_scheme (String.make 1 (Char.chr 127)));
  assert (A.wellformed_body "{\"a\":1,\"b\":2}");
  assert (not (A.wellformed_body ""));
  assert (not (A.wellformed_body "5x"));
  assert (not (A.wellformed_body "01"));
  assert (not (A.wellformed_body "{\"a\":1,\"a\":2}"));

  (* ----- reviewer HOLD on revision 1, blocker 2: the checked value is not
     bound to `ti.rec.completeness` -----

     parse_record_full_impl NEVER surfaces `completeness` (CampaignRecord.
     skip_value only syntactically CONSUMES it): two records differing ONLY in
     their completeness payload decode to the IDENTICAL typed view, and
     op_completeness_wellformed_impl is evaluated on a SEPARATE value
     (authenticated_completeness / ti_completeness) with no decoder-level
     connection to either record's actual bytes.  This is exactly the gap
     ManifestPipeline.record_completeness_load_validated now states as an
     explicit F.3 premise (a concrete decoder remains future work). *)
  let mk_record_c ~completeness ~rr ~budget =
    "{\"audit_instance_id\":\"ai-0001\",\"campaign_id\":\"cmp-1\"," ^
    "\"completeness\":" ^ completeness ^ "," ^ cds ^ "," ^
    "\"manifest_digest\":\"" ^ good_digest ^ "\"," ^
    "\"policy_hash\":\"" ^ d64 'd' ^ "\"," ^
    "\"recorded_results\":" ^ rr ^ ",\"resource_budget\":" ^ budget ^ "}" in
  let rec_unknown =
    mk_record_c ~completeness:"\"unknown\"" ~rr:"[]" ~budget:"{}" in
  let rec_complete =
    mk_record_c
      ~completeness:"{\"k\":\"complete\",\"v\":{\"body\":\"1\",\"scheme\":\"s\"}}"
      ~rr:"[]" ~budget:"{}" in
  (* record says Unknown vs record says Complete -- the typed view is
     IDENTICAL either way; completeness never reaches it *)
  assert (A.parse_record_full_impl rec_unknown = A.parse_record_full_impl rec_complete);
  (* yet a load path could hand op_completeness_wellformed_impl EITHER
     ti_completeness value for either record's bytes above, and it would
     accept both -- nothing here ties the accepted typed value to the record
     it purportedly came from *)
  assert (A.op_completeness_wellformed_impl A.CompletenessUnknown);       (* for rec_complete's bytes *)
  assert (A.op_completeness_wellformed_impl (cert "s" "1"));              (* for rec_unknown's bytes *)
  (* differing schemes / bodies for the SAME "complete" record shape: distinct
     ti_completeness values are each independently accepted or rejected on
     their own terms, again with no reference to what any record contains *)
  assert (A.op_completeness_wellformed_impl (cert "s" "1"));
  assert (not (A.op_completeness_wellformed_impl (cert "" "1")));
  assert (not (A.op_completeness_wellformed_impl (cert "s" "not-json")));

  print_endline
    "PASS: manifest authentication -- frozen digest 0714f76c; canonical bytes; \
     Ed25519 RFC-8032 TEST 1 + tamper/invalid-point/degenerate-key rejects; \
     parse_commitment rejects; parse_manifest schema conformance + escape decode + \
     short-digest/control/utf8 rejects; REAL signed-digest end-to-end verify; \
     signature_valid message-form = utf8(digest); \
     op_ledger_mismatch least-index / length-divergence over reorder/add/remove/duplicate; \
     op_manifest_audit_matches exact-id match / mismatch / case / non-decoding; \
     op_record_identity_mismatch 5 identity fields in frozen order + earliest-of-many + \
     case + distinct decoder-failure sentinels + NORMATIVE full record decode \
     (completeness/recorded_results/resource_budget skipped, canonical syntax enforced: \
     leading-zero / -0 / dup-key / descending-key rejected) + identity-only form rejected; \
     op_record_crosscheck FULLY TYPED submission_check_result (4-way outcome \
     constructor, no not_run + typed findings) + forward projection coherence + \
     replay-derived crosscheck over scr_agrees (index / mandatory digest / candidate_id / \
     semantic_candidate_digest / typed outcome / findings incl. offending; check_id \
     domain enforced) -- every field mutation (incl. isolated submission_digest / index) \
     produces a campaign_record_mismatch; stage-1 NotRun and pending+stage-2-NotRun slots \
     are filtered from derive_expected (a recorded claim for one -> mismatch); mutation + \
     NotRun-alignment tests run THROUGH parse_record_full_impl; advisory findings lie in \
     the closed 3-id family + advisory budget crosscheck + matching end-to-end \
     record_crosscheck_impl; op_completeness_wellformed_impl Unknown/Incomplete \
     unconditional + Complete certificate scheme/body well-formedness (revision 2: \
     quote/backslash/high-byte schemes ACCEPTED, only empty rejected; body still scoped \
     to the ASCII-wire canonical subset) + every failure class (empty scheme; \
     empty/trailing-garbage/leading-zero/dup-key/non-JSON/high-byte-string body) + the \
     record-completeness binding gap demonstrated (identical typed view for differing \
     completeness payloads)"
