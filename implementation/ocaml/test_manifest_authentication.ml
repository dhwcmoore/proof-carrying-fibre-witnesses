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
     leading-zero / -0 / dup-key / descending-key rejected) + identity-only form rejected"
