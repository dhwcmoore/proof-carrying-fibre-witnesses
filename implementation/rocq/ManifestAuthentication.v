(** Concrete AUDIT_POLICY_AND_EVIDENCE.md 2.4.1 commitment scheme:

      commitment wire -> parsed commitment -> authorised signer
      -> manifest digest agreement -> Ed25519 verification -> authenticated manifest

    Wires [op_parse_commitment] / [op_signer_authorised] / [op_signature_valid].
    Leaves ledger / record / completeness / cross-check / transcript-digest
    abstract (a later unit).

    F.3 NAMED COMPONENTS (not implemented or proved here; the OCaml harness links
    real implementations and checks them against normative vectors):
      - sha256_hex   : SHA-256, lowercase hex   (via CanonicalV1.digest_v1)
      - ed25519_verify : PureEdDSA Ed25519, RFC 8032, verify
      - ed25519_pubkey_valid : canonical, non-small-order public-key decoding
        (rejects the identity / cofactor-torsion keys the bare group equation
        accepts for S = 0); run by signature_valid_impl on the looked-up key

    CONCRETE HERE (pure Coq, no crypto):
      - hex validation and decoding
      - parse_commitment_impl (2.4.1 wire checks)
      - parse_manifest_impl : a STRICT decoder for the canonical ASCII-wire
        subset of the campaign_manifest form.  parse_manifest_impl_roundtrip is
        proved only for manifests satisfying manifest_roundtrip_wf, which requires
        64-lowercase-hex digest fields and identifiers whose bytes are all ASCII
        0x20..0x7E except the two JSON metacharacters 0x22 and 0x5C; canonical key
        order is supplied by CanonicalV1.render_manifest, not by
        manifest_roundtrip_wf.  On that subset parse_manifest_impl decodes exactly
        the byte sequence render_manifest produces.  A key-order-tolerant /
        re-canonicalising / non-ASCII-identifier decoder is future work; the audit
        publishes canonical manifest bytes.
      - signer_authorised_impl / signature_valid_impl / manifest_authenticated_by_impl
        (the 2.4.1 authenticate_manifest composition)

    TRUST BOUNDARY: SHA-256 and Ed25519 SOUNDNESS are NOT proved.  Retrieval
    integrity (that the retrieved commitment/manifest is the intended audit
    object) is NOT established by authentication and stays an explicit F.3
    premise where used downstream. *)

From Coq Require Import String Ascii List Bool Arith PeanoNat Lia.
From PCFW Require Import Orchestration CanonicalV1 ValidationBinding.
Import ListNotations.
Open Scope string_scope.

(* ================= hex ================= *)

Definition hexval (c : ascii) : option nat :=
  let n := nat_of_ascii c in
  if andb (Nat.leb 48 n) (Nat.leb n 57) then Some (n - 48)
  else if andb (Nat.leb 97 n) (Nat.leb n 102) then Some (n - 87)
  else None.

Definition is_lower_hex (c : ascii) : bool :=
  match hexval c with Some _ => true | None => false end.

Fixpoint all_lower_hex (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c r => is_lower_hex c && all_lower_hex r
  end.

Fixpoint hex_decode (s : string) : option bytes :=
  match s with
  | EmptyString => Some EmptyString
  | String _ EmptyString => None
  | String c1 (String c2 rest) =>
      match hexval c1, hexval c2, hex_decode rest with
      | Some hi, Some lo, Some b => Some (String (ascii_of_nat (hi * 16 + lo)) b)
      | _, _, _ => None
      end
  end.

(* ================= parse_commitment ================= *)

Definition parse_commitment_impl (w : manifest_commitment_wire)
  : parse_commitment_result :=
  if negb (Nat.eqb (String.length (cw_digest w)) 64)
  then CommitmentParseError "digest_not_64"
  else if negb (all_lower_hex (cw_digest w))
  then CommitmentParseError "digest_not_lower_hex"
  else if negb (Nat.eqb (String.length (cw_signature w)) 128)
  then CommitmentParseError "signature_not_128"
  else if negb (all_lower_hex (cw_signature w))
  then CommitmentParseError "signature_not_lower_hex"
  else match hex_decode (cw_signature w) with
       | None => CommitmentParseError "signature_hex_decode"
       | Some sig =>
           CommitmentParsed (mkManifestCommitment (cw_digest w) (cw_signer w) sig)
       end.

Theorem parse_commitment_impl_sound :
  forall w mc,
    parse_commitment_impl w = CommitmentParsed mc ->
    String.length (cw_digest w) = 64 /\
    all_lower_hex (cw_digest w) = true /\
    String.length (cw_signature w) = 128 /\
    all_lower_hex (cw_signature w) = true /\
    commitment_digest mc = cw_digest w /\
    commitment_signer mc = cw_signer w /\
    hex_decode (cw_signature w) = Some (commitment_signature mc).
Proof.
  intros w mc H. unfold parse_commitment_impl in H.
  destruct (Nat.eqb (String.length (cw_digest w)) 64) eqn:E1; cbn [negb] in H;
    [| discriminate].
  destruct (all_lower_hex (cw_digest w)) eqn:E2; cbn [negb] in H; [| discriminate].
  destruct (Nat.eqb (String.length (cw_signature w)) 128) eqn:E3; cbn [negb] in H;
    [| discriminate].
  destruct (all_lower_hex (cw_signature w)) eqn:E4; cbn [negb] in H; [| discriminate].
  destruct (hex_decode (cw_signature w)) as [sig|] eqn:E5; [| discriminate].
  injection H as <-. cbn.
  apply Nat.eqb_eq in E1, E3.
  repeat split; assumption.
Qed.

Theorem parse_commitment_impl_reject_not_parsed :
  forall w msg, parse_commitment_impl w = CommitmentParseError msg ->
    Nat.eqb (String.length (cw_digest w)) 64 = false \/
    all_lower_hex (cw_digest w) = false \/
    Nat.eqb (String.length (cw_signature w)) 128 = false \/
    all_lower_hex (cw_signature w) = false \/
    hex_decode (cw_signature w) = None.
Proof.
  intros w msg H. unfold parse_commitment_impl in H.
  destruct (Nat.eqb (String.length (cw_digest w)) 64) eqn:E1; cbn [negb] in H;
    [| now left].
  destruct (all_lower_hex (cw_digest w)) eqn:E2; cbn [negb] in H; [| now right;left].
  destruct (Nat.eqb (String.length (cw_signature w)) 128) eqn:E3; cbn [negb] in H;
    [| right;right;now left].
  destruct (all_lower_hex (cw_signature w)) eqn:E4; cbn [negb] in H;
    [| right;right;right;now left].
  destruct (hex_decode (cw_signature w)) eqn:E5; [ discriminate |].
  right;right;right;right;reflexivity.
Qed.

(* ================= schema-conforming canonical manifest decoder =================

   Accepts ONLY the canonical wire form (AUDIT_POLICY 2.2.2: no whitespace, object
   keys in byte-ascending order).  A key-order-tolerant decoder is future work;
   the audit publishes canonical bytes.  Within that form the decoder is strict:

   - whole input must be valid UTF-8 (RFC 3629 structural, with overlong /
     surrogate / range guards -- [CanonicalV1.valid_utf8]);
   - string values decode the 2.2.2 escapes and REJECT a raw control byte
     (< 0x20) or a lone / unknown backslash escape;
   - every digest-typed field (context digests, policy_hash, each
     submission_digest) must be exactly 64 lowercase-hex characters;
   - the submission-digest array rejects a trailing comma;
   - a duplicate key or an unknown / extra field is bytes that do not match the
     fixed template, so it is rejected. *)

Fixpoint starts_with (p s : string) : option string :=
  match p, s with
  | EmptyString, _ => Some s
  | String pc pr, String sc sr =>
      if Ascii.eqb pc sc then starts_with pr sr else None
  | String _ _, EmptyString => None
  end.

Lemma starts_with_app : forall p x, starts_with p (p ++ x) = Some x.
Proof.
  induction p as [| c p IH]; intros x; [ reflexivity |].
  cbn. now rewrite Ascii.eqb_refl, IH.
Qed.

Lemma starts_with_1_match : forall c x,
  starts_with (String c "") (String c x) = Some x.
Proof. intros. cbn. now rewrite Ascii.eqb_refl. Qed.

Lemma starts_with_1_ne : forall c c' x,
  Ascii.eqb c c' = false -> starts_with (String c "") (String c' x) = None.
Proof. intros c c' x H. cbn. now rewrite H. Qed.

Notation dq := CanonicalV1.a_dquote.   (* 34 *)
Notation bs := CanonicalV1.a_bslash.   (* 92 *)

(* value chars after an opening quote: decode escapes, reject raw control bytes
   and lone / unknown escapes, until the closing quote. *)
Fixpoint parse_str_body (s : string) (acc : string) : option (string * string) :=
  match s with
  | EmptyString => None
  | String c rest =>
      let n := nat_of_ascii c in
      if Nat.eqb n 34 then Some (acc, rest)
      else if Nat.eqb n 92 then
        match rest with
        | EmptyString => None
        | String e rest2 =>
            let en := nat_of_ascii e in
            if Nat.eqb en 34 then parse_str_body rest2 (acc ++ String (ascii_of_nat 34) "")
            else if Nat.eqb en 92 then parse_str_body rest2 (acc ++ String (ascii_of_nat 92) "")
            else if Nat.eqb en 98 then parse_str_body rest2 (acc ++ String (ascii_of_nat 8) "")
            else if Nat.eqb en 116 then parse_str_body rest2 (acc ++ String (ascii_of_nat 9) "")
            else if Nat.eqb en 110 then parse_str_body rest2 (acc ++ String (ascii_of_nat 10) "")
            else if Nat.eqb en 102 then parse_str_body rest2 (acc ++ String (ascii_of_nat 12) "")
            else if Nat.eqb en 114 then parse_str_body rest2 (acc ++ String (ascii_of_nat 13) "")
            else if Nat.eqb en 117 then
              match rest2 with
              | String z0 (String z1 (String h0 (String h1 rest3))) =>
                  if andb (Nat.eqb (nat_of_ascii z0) 48) (Nat.eqb (nat_of_ascii z1) 48)
                  then match hexval h0, hexval h1 with
                       | Some hi, Some lo =>
                           let u := hi * 16 + lo in
                           (* 2.2.2: \u00xx is canonical ONLY for control code
                              points with no named escape:
                              U+0000..U+0007, U+000B, U+000E..U+001F. *)
                           if andb (Nat.ltb u 32)
                                   (andb (negb (Nat.eqb u 8))
                                    (andb (negb (Nat.eqb u 9))
                                     (andb (negb (Nat.eqb u 10))
                                      (andb (negb (Nat.eqb u 12)) (negb (Nat.eqb u 13))))))
                           then parse_str_body rest3 (acc ++ String (ascii_of_nat u) "")
                           else None
                       | _, _ => None
                       end
                  else None
              | _ => None
              end
            else None
        end
      else if Nat.ltb n 32 then None
      (* 2.2.2: characters >= U+0020 appear as raw UTF-8; this bounded decoder
         restricts identifiers to raw ASCII (32..127).  Non-ASCII UTF-8
         identifiers are future work -- the audit's ids (ai-0001, cmp-1) are
         ASCII. *)
      else if Nat.ltb 127 n then None
      else parse_str_body rest (acc ++ String c "")
  end.

Definition parse_json_string (s : string) : option (string * string) :=
  match s with
  | String c rest => if Nat.eqb (nat_of_ascii c) 34 then parse_str_body rest "" else None
  | EmptyString => None
  end.

Fixpoint take_n_hex (k : nat) (s : string) (acc : string) : option (string * string) :=
  match k with
  | 0 => Some (acc, s)
  | S k' =>
      match s with
      | String c rest =>
          if CanonicalV1.is_lower_hex_digit c
          then take_n_hex k' rest (acc ++ String c "")
          else None
      | EmptyString => None
      end
  end.

(* parse  "<64 lowercase hex>"  -> (digest, rest after closing quote) *)
Definition parse_digest_field (s : string) : option (string * string) :=
  match s with
  | String c1 rest1 =>
      if Nat.eqb (nat_of_ascii c1) 34 then
        match take_n_hex 64 rest1 "" with
        | Some (d, String c2 rest2) =>
            if Nat.eqb (nat_of_ascii c2) 34 then Some (d, rest2) else None
        | _ => None
        end
      else None
  | EmptyString => None
  end.

Fixpoint parse_dig_array_elems (fuel : nat) (s : string) (acc : list string)
  : option (list string * string) :=
  match fuel with
  | 0 => None
  | S f =>
      match parse_digest_field s with
      | None => None
      | Some (d, s1) =>
          match s1 with
          | String c rest =>
              let n := nat_of_ascii c in
              if Nat.eqb n 93 then Some (List.rev (d :: acc), rest)
              else if Nat.eqb n 44 then parse_dig_array_elems f rest (d :: acc)
              else None
          | EmptyString => None
          end
      end
  end.

Definition parse_dig_array (s : string) : option (list string * string) :=
  match s with
  | String c rest =>
      if Nat.eqb (nat_of_ascii c) 91 then
        match starts_with (String "]"%char "") rest with
        | Some rest2 => Some ([], rest2)
        | None => parse_dig_array_elems (S (String.length rest)) rest []
        end
      else None
  | EmptyString => None
  end.

Definition parse_manifest_impl (m : manifest) : option campaign_manifest_view :=
  let s := manifest_token m in
  if negb (CanonicalV1.valid_utf8 s) then None else
  match starts_with "{""audit_instance_id"":" s with None => None | Some s1 =>
  match parse_json_string s1 with None => None | Some (aid, s2) =>
  match starts_with ",""campaign_id"":" s2 with None => None | Some s3 =>
  match parse_json_string s3 with None => None | Some (cid, s4) =>
  match starts_with ",""context_digests"":{""inference_spec_digest"":" s4
  with None => None | Some s5 =>
  match parse_digest_field s5 with None => None | Some (idig, s6) =>
  match starts_with ",""model_artifact_digest"":" s6 with None => None | Some s7 =>
  match parse_digest_field s7 with None => None | Some (mdig, s8) =>
  match starts_with ",""preprocessing_digest"":" s8 with None => None | Some s9 =>
  match parse_digest_field s9 with None => None | Some (pdig, s10) =>
  match starts_with "},""policy_hash"":" s10 with None => None | Some s11 =>
  match parse_digest_field s11 with None => None | Some (ph, s12) =>
  match starts_with ",""submission_digests"":" s12 with None => None | Some s13 =>
  match parse_dig_array s13 with None => None | Some (subs, s14) =>
  match starts_with "}" s14 with
  | Some EmptyString =>
      Some (mkCampaignManifestView aid cid
              (mkContextDescriptor mdig pdig idig) ph subs)
  | _ => None
  end end end end end end end end end end end end end end end.

(* escape decoding is exercised: an escaped quote then a char decode correctly. *)
Lemma parse_str_body_escape_example :
  parse_str_body (String bs (String dq (String "a"%char (String dq EmptyString)))) ""
  = Some (String dq (String "a"%char EmptyString), EmptyString).
Proof. vm_compute. reflexivity. Qed.

(* the short-digest frozen 2.2.5 vector is NOT schema-valid: rejected. *)
Lemma parse_manifest_impl_rejects_short_digests :
  parse_manifest_impl (mkManifest (render_manifest frozen_manifest_vector)) = None.
Proof. vm_compute. reflexivity. Qed.

(* schema-valid full-length vector: round-trips. *)
Lemma parse_manifest_impl_schema_valid_vector :
  parse_manifest_impl (mkManifest (render_manifest schema_valid_manifest))
  = Some schema_valid_manifest.
Proof. vm_compute. reflexivity. Qed.

(* ----- string append helpers ----- *)
Lemma sar : forall s, (s ++ "")%string = s.
Proof. induction s as [| c s IH]; cbn; congruence. Qed.
Lemma saa : forall a b c, ((a ++ b) ++ c)%string = (a ++ (b ++ c))%string.
Proof. induction a as [| x a IH]; cbn; intros; congruence. Qed.

(* ----- general round-trip under an explicit well-formedness predicate ----- *)

(* wf ids: printable ASCII (>= 0x20), no raw quote or backslash -- so [render]
   escapes nothing; the parser's escape decoding is still implemented and
   separately exercised above. *)
(* printable ASCII 0x20..0x7E, excluding the two JSON metacharacters (34, 92).
   Audit / campaign ids like ai-0001 satisfy this; a broader id character set
   is future work. *)
Definition printable_ascii_char (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (andb (Nat.leb 32 n) (Nat.leb n 126))
       (andb (negb (Nat.eqb n 34)) (negb (Nat.eqb n 92))).

Fixpoint printable_ascii_id (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c r => printable_ascii_char c && printable_ascii_id r
  end.

Definition manifest_roundtrip_wf (m : campaign_manifest_view) : Prop :=
  CanonicalV1.is_hex64 (cm_policy_hash m) = true /\
  CanonicalV1.is_hex64 (cd_model_artifact_digest (cm_context_digests m)) = true /\
  CanonicalV1.is_hex64 (cd_preprocessing_digest (cm_context_digests m)) = true /\
  CanonicalV1.is_hex64 (cd_inference_spec_digest (cm_context_digests m)) = true /\
  forallb CanonicalV1.is_hex64 (cm_submission_digests m) = true /\
  printable_ascii_id (cm_audit_instance_id m) = true /\
  printable_ascii_id (cm_campaign_id m) = true.

Lemma printable_char_props : forall c, printable_ascii_char c = true ->
  32 <= nat_of_ascii c /\ nat_of_ascii c <= 126 /\
  nat_of_ascii c <> 34 /\ nat_of_ascii c <> 92.
Proof.
  intros c H. unfold printable_ascii_char in H.
  apply Bool.andb_true_iff in H as [A B].
  apply Bool.andb_true_iff in A as [A1 A2].
  apply Bool.andb_true_iff in B as [B1 B2].
  apply Nat.leb_le in A1, A2.
  apply Bool.negb_true_iff, Nat.eqb_neq in B1, B2.
  auto.
Qed.

Lemma esc_char_id_of : forall c,
  32 <= nat_of_ascii c -> nat_of_ascii c <> 34 -> nat_of_ascii c <> 92 ->
  CanonicalV1.esc_char c = String c "".
Proof.
  intros c A N34 N92. unfold CanonicalV1.esc_char.
  set (n := nat_of_ascii c) in *.
  repeat (match goal with
          | |- context [Nat.eqb n ?k] =>
              replace (Nat.eqb n k) with false by (symmetry; apply Nat.eqb_neq; lia)
          end).
  replace (Nat.ltb n 32) with false by (symmetry; apply Nat.ltb_ge; lia).
  reflexivity.
Qed.

Lemma is_lower_hex_props : forall c,
  CanonicalV1.is_lower_hex_digit c = true ->
  48 <= nat_of_ascii c <= 57 \/ 97 <= nat_of_ascii c <= 102.
Proof.
  intros c H. unfold CanonicalV1.is_lower_hex_digit in H.
  apply Bool.orb_true_iff in H as [H | H];
    apply Bool.andb_true_iff in H as [A B];
    apply Nat.leb_le in A, B; [ left | right ]; lia.
Qed.

Lemma is_lower_hex_no_esc : forall c,
  CanonicalV1.is_lower_hex_digit c = true -> CanonicalV1.esc_char c = String c "".
Proof.
  intros c H. destruct (is_lower_hex_props c H) as [[A B] | [A B]];
  apply esc_char_id_of; lia.
Qed.

Lemma all_lower_hex_esc_id : forall s,
  CanonicalV1.all_lower_hex s = true -> CanonicalV1.esc_str s = s.
Proof.
  induction s as [| c s IH]; intros H; [ reflexivity |].
  cbn in H. apply Bool.andb_true_iff in H as [Hc Hs].
  cbn. rewrite (is_lower_hex_no_esc c Hc), (IH Hs). reflexivity.
Qed.

Lemma printable_esc_id : forall s,
  printable_ascii_id s = true -> CanonicalV1.esc_str s = s.
Proof.
  induction s as [| c s IH]; intros H; [ reflexivity |].
  cbn in H. apply Bool.andb_true_iff in H as [Hc Hs].
  destruct (printable_char_props c Hc) as (A & _ & N34 & N92).
  cbn. rewrite (IH Hs), (esc_char_id_of c A N34 N92). reflexivity.
Qed.

Lemma parse_str_body_printable : forall s rest acc,
  printable_ascii_id s = true ->
  parse_str_body (s ++ String dq rest) acc = Some ((acc ++ s)%string, rest).
Proof.
  induction s as [| c s IH]; intros rest acc H.
  - cbn. rewrite Nat.eqb_refl, sar. reflexivity.
  - cbn in H. apply Bool.andb_true_iff in H as [Hc Hs].
    destruct (printable_char_props c Hc) as (A & U & N34 & N92).
    cbn [String.append parse_str_body].
    destruct (Nat.eqb (nat_of_ascii c) 34) eqn:D34;
      [ apply Nat.eqb_eq in D34; lia |].
    destruct (Nat.eqb (nat_of_ascii c) 92) eqn:D92;
      [ apply Nat.eqb_eq in D92; lia |].
    destruct (Nat.ltb (nat_of_ascii c) 32) eqn:Dlt;
      [ apply Nat.ltb_lt in Dlt; lia |].
    destruct (Nat.ltb 127 (nat_of_ascii c)) eqn:Dgt;
      [ apply Nat.ltb_lt in Dgt; lia |].
    cbn [String.append].
    rewrite IH by exact Hs. rewrite saa. reflexivity.
Qed.

Lemma parse_json_string_printable : forall s rest,
  printable_ascii_id s = true ->
  parse_json_string (CanonicalV1.json_string s ++ rest) = Some (s, rest).
Proof.
  intros s rest H. unfold CanonicalV1.json_string, parse_json_string.
  rewrite (printable_esc_id s H).
  cbn [String.append].
  change (nat_of_ascii CanonicalV1.a_dquote) with 34. cbn [Nat.eqb].
  rewrite saa. cbn [String.append].
  rewrite (parse_str_body_printable s rest "" H). reflexivity.
Qed.

Lemma take_n_hex_exact : forall k d rest acc,
  CanonicalV1.all_lower_hex d = true ->
  String.length d = k ->
  take_n_hex k (d ++ rest) acc = Some ((acc ++ d)%string, rest).
Proof.
  induction k as [| k IHk]; intros d rest acc Hhex Hlen.
  - destruct d; [ cbn; now rewrite sar | cbn in Hlen; discriminate ].
  - destruct d as [| c d]; cbn in Hlen; [ discriminate |].
    cbn in Hhex. apply Bool.andb_true_iff in Hhex as [Hc Hd].
    cbn [String.append take_n_hex]. rewrite Hc.
    rewrite (IHk d rest (acc ++ String c "")%string Hd ltac:(lia)).
    now rewrite saa.
Qed.

Lemma parse_digest_field_hex64 : forall d rest,
  CanonicalV1.is_hex64 d = true ->
  parse_digest_field (CanonicalV1.json_string d ++ rest) = Some (d, rest).
Proof.
  intros d rest H. unfold CanonicalV1.is_hex64 in H.
  apply Bool.andb_true_iff in H as [Hlen Hhex].
  apply Nat.eqb_eq in Hlen.
  unfold CanonicalV1.json_string. rewrite (all_lower_hex_esc_id d Hhex).
  cbn [String.append parse_digest_field].
  change (nat_of_ascii CanonicalV1.a_dquote) with 34. cbn [Nat.eqb].
  rewrite saa. cbn [String.append].
  rewrite (take_n_hex_exact 64 d
             (String CanonicalV1.a_dquote rest) "" Hhex Hlen).
  cbn [String.append].
  change (nat_of_ascii CanonicalV1.a_dquote) with 34. cbn [Nat.eqb]. reflexivity.
Qed.

Lemma json_string_first : forall s,
  exists r, CanonicalV1.json_string s = String dq r.
Proof. intros s. unfold CanonicalV1.json_string. eexists. reflexivity. Qed.

(* a clean fixpoint for the rendered digest list, matching String.concat *)
Fixpoint render_dig_list (subs : list string) : string :=
  match subs with
  | [] => ""
  | d :: rest =>
      match rest with
      | [] => CanonicalV1.json_string d
      | _ => CanonicalV1.json_string d ++ String ","%char (render_dig_list rest)
      end
  end.

Lemma rdl_cons2 : forall d d2 subs,
  render_dig_list (d :: d2 :: subs)
  = CanonicalV1.json_string d ++ String ","%char (render_dig_list (d2 :: subs)).
Proof. reflexivity. Qed.

Lemma rdl_single : forall d, render_dig_list [d] = CanonicalV1.json_string d.
Proof. reflexivity. Qed.

Lemma str_len_app : forall a b,
  String.length (a ++ b) = (String.length a + String.length b)%nat.
Proof. induction a as [| c a IH]; cbn; intros; [ reflexivity | now rewrite IH ]. Qed.

Lemma json_string_len_ge1 : forall s, (1 <= String.length (CanonicalV1.json_string s))%nat.
Proof. intros s. unfold CanonicalV1.json_string. cbn [String.length]. lia. Qed.

Lemma length_le_str_render : forall subs,
  (length subs <= String.length (render_dig_list subs))%nat.
Proof.
  induction subs as [| d subs IH]; [ cbn; lia |].
  destruct subs as [| d2 subs].
  - rewrite rdl_single. cbn [length].
    pose proof (json_string_len_ge1 d). lia.
  - rewrite rdl_cons2. rewrite str_len_app. cbn [String.length length].
    cbn [length] in IH. lia.
Qed.

Lemma concat_map_render : forall subs,
  String.concat "," (List.map CanonicalV1.json_string subs) = render_dig_list subs.
Proof.
  induction subs as [| d subs IH]; [ reflexivity |].
  destruct subs as [| d2 subs]; [ reflexivity |].
  cbn [List.map String.concat render_dig_list].
  cbn [List.map String.concat] in IH. rewrite IH. reflexivity.
Qed.

Lemma parse_dig_array_elems_ok : forall subs fuel s acc,
  forallb CanonicalV1.is_hex64 subs = true ->
  subs <> [] ->
  (length subs <= fuel)%nat ->
  parse_dig_array_elems fuel (render_dig_list subs ++ String "]"%char s) acc
  = Some ((List.rev acc ++ subs)%list, s).
Proof.
  induction subs as [| d subs IH]; intros fuel s acc Hall Hne Hf; [ contradiction |].
  cbn [forallb] in Hall. apply Bool.andb_true_iff in Hall as [Hd Hsubs].
  destruct fuel as [| fuel]; [ cbn in Hf; lia |].
  destruct subs as [| d2 subs].
  - rewrite rdl_single. cbn [parse_dig_array_elems].
    rewrite (parse_digest_field_hex64 d (String "]"%char s) Hd).
    change (nat_of_ascii "]"%char) with 93. cbn [Nat.eqb].
    cbn [List.rev]. reflexivity.
  - rewrite rdl_cons2. cbn [parse_dig_array_elems].
    rewrite saa.
    rewrite (parse_digest_field_hex64 d
              (String ","%char (render_dig_list (d2 :: subs)) ++ String "]"%char s) Hd).
    cbn [String.append].
    change (nat_of_ascii ","%char) with 44. cbn [Nat.eqb].
    rewrite (IH fuel s (d :: acc) Hsubs ltac:(discriminate)
              ltac:(cbn [length] in Hf |- *; lia)).
    cbn [List.rev]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma parse_dig_array_hex : forall subs s,
  forallb CanonicalV1.is_hex64 subs = true ->
  parse_dig_array (CanonicalV1.render_string_array subs ++ s) = Some (subs, s).
Proof.
  intros subs s Hall.
  unfold CanonicalV1.render_string_array. rewrite concat_map_render.
  assert (Hpeel : (("[" ++ render_dig_list subs ++ "]") ++ s)%string
                  = String "["%char (render_dig_list subs ++ String "]"%char s))
    by (rewrite !saa; cbn [String.append]; reflexivity).
  rewrite Hpeel. unfold parse_dig_array.
  change (nat_of_ascii "["%char) with 91. cbn [Nat.eqb].
  destruct subs as [| d subs].
  - cbn [render_dig_list]. cbn [String.append].
    rewrite starts_with_1_match. reflexivity.
  - assert (Hfst : exists r, render_dig_list (d :: subs) = String dq r).
    { destruct subs as [| d2 subs].
      - rewrite rdl_single. exact (json_string_first d).
      - rewrite rdl_cons2. destruct (json_string_first d) as [r Hr].
        rewrite Hr. eexists. reflexivity. }
    destruct Hfst as [rr Hrr].
    replace (starts_with (String "]"%char "")
               (render_dig_list (d :: subs) ++ String "]"%char s))
      with (@None string)
      by (rewrite Hrr; symmetry; apply starts_with_1_ne; reflexivity).
    rewrite (parse_dig_array_elems_ok (d :: subs)
              (S (String.length (render_dig_list (d :: subs) ++ String "]"%char s)))
              s [] Hall ltac:(discriminate)).
    + cbn [List.rev List.app]. reflexivity.
    + pose proof (length_le_str_render (d :: subs)) as HL.
      rewrite str_len_app. lia.
Qed.

(* ----- render output is valid UTF-8 ----- *)

Fixpoint all_ascii (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c r => Nat.ltb (nat_of_ascii c) 128 && all_ascii r
  end.

Lemma all_ascii_app : forall a b, all_ascii (a ++ b) = all_ascii a && all_ascii b.
Proof.
  induction a as [| c a IH]; cbn; intros b; [ reflexivity |].
  rewrite IH. now rewrite Bool.andb_assoc.
Qed.

Lemma valid_utf8_aux_ascii : forall f s,
  all_ascii s = true -> (String.length s <= f)%nat ->
  CanonicalV1.valid_utf8_aux f s = true.
Proof.
  induction f as [| f IHf]; intros s Ha Hlen.
  - destruct s; [ reflexivity | cbn in Hlen; lia ].
  - destruct s as [| c s]; [ reflexivity |].
    cbn [all_ascii] in Ha. apply Bool.andb_true_iff in Ha as [Hc Hs].
    assert (Hc' : nat_of_ascii c < 128) by (apply Nat.ltb_lt; exact Hc).
    cbn [CanonicalV1.valid_utf8_aux].
    replace (Nat.ltb (nat_of_ascii c) 128) with true by (symmetry; apply Nat.ltb_lt; lia).
    apply IHf; [ exact Hs | cbn in Hlen; lia ].
Qed.

Lemma all_ascii_valid_utf8 : forall s,
  all_ascii s = true -> CanonicalV1.valid_utf8 s = true.
Proof.
  intros s H. unfold CanonicalV1.valid_utf8.
  apply valid_utf8_aux_ascii; [ exact H | lia ].
Qed.

Lemma all_ascii_of_printable : forall s,
  printable_ascii_id s = true -> all_ascii s = true.
Proof.
  induction s as [| c s IH]; intros H; [ reflexivity |].
  cbn [printable_ascii_id] in H. apply Bool.andb_true_iff in H as [Hc Hs].
  destruct (printable_char_props c Hc) as (_ & U & _ & _).
  cbn [all_ascii]. rewrite (IH Hs), Bool.andb_true_r. apply Nat.ltb_lt; lia.
Qed.

Lemma all_ascii_of_hex : forall d,
  CanonicalV1.all_lower_hex d = true -> all_ascii d = true.
Proof.
  induction d as [| c d IH]; intros H; [ reflexivity |].
  cbn [CanonicalV1.all_lower_hex] in H. apply Bool.andb_true_iff in H as [Hc Hd].
  cbn [all_ascii]. rewrite (IH Hd), Bool.andb_true_r.
  destruct (is_lower_hex_props c Hc) as [[A B]|[A B]]; apply Nat.ltb_lt; lia.
Qed.

Lemma all_ascii_json_of_printable : forall s,
  printable_ascii_id s = true -> all_ascii (CanonicalV1.json_string s) = true.
Proof.
  intros s H. unfold CanonicalV1.json_string. rewrite (printable_esc_id s H).
  cbn [all_ascii]. change (nat_of_ascii CanonicalV1.a_dquote) with 34. cbn [Nat.ltb].
  rewrite all_ascii_app. cbn [all_ascii].
  change (nat_of_ascii CanonicalV1.a_dquote) with 34. cbn [Nat.ltb].
  rewrite Bool.andb_true_r, (all_ascii_of_printable s H). reflexivity.
Qed.

Lemma all_ascii_json_of_hex64 : forall d,
  CanonicalV1.is_hex64 d = true -> all_ascii (CanonicalV1.json_string d) = true.
Proof.
  intros d H. unfold CanonicalV1.is_hex64 in H.
  apply Bool.andb_true_iff in H as [_ Hhex].
  unfold CanonicalV1.json_string. rewrite (all_lower_hex_esc_id d Hhex).
  cbn [all_ascii]. change (nat_of_ascii CanonicalV1.a_dquote) with 34. cbn [Nat.ltb].
  rewrite all_ascii_app. cbn [all_ascii].
  change (nat_of_ascii CanonicalV1.a_dquote) with 34. cbn [Nat.ltb].
  rewrite Bool.andb_true_r, (all_ascii_of_hex d Hhex). reflexivity.
Qed.

Lemma render_dig_list_all_ascii : forall subs,
  forallb CanonicalV1.is_hex64 subs = true -> all_ascii (render_dig_list subs) = true.
Proof.
  induction subs as [| d subs IH]; intros H; [ reflexivity |].
  cbn [forallb] in H. apply Bool.andb_true_iff in H as [Hd Hs].
  destruct subs as [| d2 subs].
  - rewrite rdl_single. exact (all_ascii_json_of_hex64 d Hd).
  - rewrite rdl_cons2, all_ascii_app, (all_ascii_json_of_hex64 d Hd).
    cbn [all_ascii]. change (nat_of_ascii ","%char) with 44. cbn [Nat.ltb].
    rewrite (IH Hs). reflexivity.
Qed.

Lemma render_manifest_all_ascii : forall m,
  manifest_roundtrip_wf m -> all_ascii (CanonicalV1.render_manifest m) = true.
Proof.
  intros m (Hph & Hmm & Hpp & Hii & Hsub & Haid & Hcid).
  unfold CanonicalV1.render_manifest, CanonicalV1.render_context_descriptor,
         CanonicalV1.render_string_array, CanonicalV1.kv.
  rewrite concat_map_render.
  repeat rewrite all_ascii_app.
  repeat rewrite Bool.andb_true_iff. repeat split;
    try reflexivity;
    try (apply all_ascii_json_of_printable; assumption);
    try (apply all_ascii_json_of_hex64; assumption);
    try (apply render_dig_list_all_ascii; assumption).
Qed.

Lemma render_manifest_valid_utf8 : forall m,
  manifest_roundtrip_wf m -> CanonicalV1.valid_utf8 (CanonicalV1.render_manifest m) = true.
Proof.
  intros m H. apply all_ascii_valid_utf8, render_manifest_all_ascii, H.
Qed.

(* ----- the round-trip theorem ----- *)

(* render_manifest, with every concrete byte flattened and only the variable
   json_string / render_string_array parts left symbolic. *)
Lemma render_manifest_flat : forall aid cid mm pp ii ph subs,
  CanonicalV1.render_manifest
    (mkCampaignManifestView aid cid (mkContextDescriptor mm pp ii) ph subs)
  = ("{""audit_instance_id"":" ++ CanonicalV1.json_string aid ++
     ",""campaign_id"":" ++ CanonicalV1.json_string cid ++
     ",""context_digests"":{""inference_spec_digest"":" ++ CanonicalV1.json_string ii ++
     ",""model_artifact_digest"":" ++ CanonicalV1.json_string mm ++
     ",""preprocessing_digest"":" ++ CanonicalV1.json_string pp ++
     "},""policy_hash"":" ++ CanonicalV1.json_string ph ++
     ",""submission_digests"":" ++ CanonicalV1.render_string_array subs ++ "}")%string.
Proof.
  intros. unfold CanonicalV1.render_manifest, CanonicalV1.render_context_descriptor,
    CanonicalV1.kv. cbn [cm_audit_instance_id cm_campaign_id cm_context_digests
    cm_policy_hash cm_submission_digests cd_model_artifact_digest
    cd_preprocessing_digest cd_inference_spec_digest].
  rewrite !saa. reflexivity.
Qed.

Theorem parse_manifest_impl_roundtrip : forall m,
  manifest_roundtrip_wf m ->
  parse_manifest_impl (mkManifest (CanonicalV1.render_manifest m)) = Some m.
Proof.
  intros m Hwf.
  pose proof Hwf as (Hph & Hmm & Hpp & Hii & Hsub & Haid & Hcid).
  destruct m as [aid cid [mm pp ii] ph subs].
  unfold parse_manifest_impl. cbn [manifest_token].
  rewrite (render_manifest_valid_utf8 _ Hwf). cbn [negb].
  rewrite render_manifest_flat.
  rewrite starts_with_app; cbn match.
  rewrite (parse_json_string_printable aid _ Haid); cbn match.
  rewrite starts_with_app; cbn match.
  rewrite (parse_json_string_printable cid _ Hcid); cbn match.
  rewrite starts_with_app; cbn match.
  rewrite (parse_digest_field_hex64 ii _ Hii); cbn match.
  rewrite starts_with_app; cbn match.
  rewrite (parse_digest_field_hex64 mm _ Hmm); cbn match.
  rewrite starts_with_app; cbn match.
  rewrite (parse_digest_field_hex64 pp _ Hpp); cbn match.
  rewrite starts_with_app; cbn match.
  rewrite (parse_digest_field_hex64 ph _ Hph); cbn match.
  rewrite starts_with_app; cbn match.
  rewrite (parse_dig_array_hex subs "}" Hsub); cbn match.
  rewrite starts_with_1_match. reflexivity.
Qed.

(* ----- escape-decoder behaviour (vm_compute) ----- *)
Definition esc_body (b : string) : string := b ++ String dq "".
Definition bsl2 (x : ascii) : string := String bs (String x "").
Definition u_esc (h0 h1 : ascii) : string :=
  String bs (String "u"%char (String "0"%char (String "0"%char
    (String h0 (String h1 ""))))).

Lemma esc_decode_quote :
  parse_str_body (esc_body (bsl2 dq)) "" = Some (String dq "", "").
Proof. vm_compute. reflexivity. Qed.
Lemma esc_decode_backslash :
  parse_str_body (esc_body (bsl2 bs)) "" = Some (String bs "", "").
Proof. vm_compute. reflexivity. Qed.
Lemma esc_decode_u0000 :
  parse_str_body (esc_body (u_esc "0"%char "0"%char)) ""
  = Some (String (ascii_of_nat 0) "", "").
Proof. vm_compute. reflexivity. Qed.
Lemma esc_decode_u001f :
  parse_str_body (esc_body (u_esc "1"%char "f"%char)) ""
  = Some (String (ascii_of_nat 31) "", "").
Proof. vm_compute. reflexivity. Qed.

Lemma esc_reject_u0061 :
  parse_str_body (esc_body (u_esc "6"%char "1"%char)) "" = None.
Proof. vm_compute. reflexivity. Qed.
Lemma esc_reject_u0008 :
  parse_str_body (esc_body (u_esc "0"%char "8"%char)) "" = None.
Proof. vm_compute. reflexivity. Qed.
Lemma esc_reject_u00ff :
  parse_str_body (esc_body (u_esc "f"%char "f"%char)) "" = None.
Proof. vm_compute. reflexivity. Qed.
Lemma esc_reject_raw_ctrl :
  parse_str_body (esc_body (String (ascii_of_nat 1) "")) "" = None.
Proof. vm_compute. reflexivity. Qed.
Lemma esc_reject_raw_nonascii :
  parse_str_body (esc_body (String (ascii_of_nat 233) "")) "" = None.
Proof. vm_compute. reflexivity. Qed.

(* ----- parser output is always well-formed (CanonicalV1.manifest_wellformed) ----- *)

Lemma alh_app : forall a b,
  CanonicalV1.all_lower_hex (a ++ b)
  = CanonicalV1.all_lower_hex a && CanonicalV1.all_lower_hex b.
Proof.
  induction a as [| x a IH]; cbn [String.append CanonicalV1.all_lower_hex];
    intros b; [ reflexivity | rewrite IH; apply Bool.andb_assoc ].
Qed.

Lemma take_n_hex_wf : forall k s acc d r,
  take_n_hex k s acc = Some (d, r) ->
  CanonicalV1.all_lower_hex acc = true ->
  String.length d = (String.length acc + k)%nat
  /\ CanonicalV1.all_lower_hex d = true.
Proof.
  induction k as [| k IHk]; intros s acc d r H Hacc.
  - cbn in H. injection H as <- _. rewrite Nat.add_0_r.
    split; [ reflexivity | exact Hacc ].
  - cbn in H. destruct s as [| c s]; [ discriminate |].
    destruct (CanonicalV1.is_lower_hex_digit c) eqn:Ec; [| discriminate].
    assert (Hacc' : CanonicalV1.all_lower_hex (acc ++ String c "") = true).
    { rewrite alh_app, Hacc. cbn [CanonicalV1.all_lower_hex]. now rewrite Ec. }
    destruct (IHk s (acc ++ String c "") d r H Hacc') as [Hd1 Hd2].
    split; [| exact Hd2 ].
    rewrite Hd1, str_len_app. cbn [String.length]. lia.
Qed.

Lemma parse_digest_field_wf : forall s d r,
  parse_digest_field s = Some (d, r) -> CanonicalV1.is_hex64 d = true.
Proof.
  intros s d r H. unfold parse_digest_field in H.
  destruct s as [| c1 s1]; [ discriminate |].
  destruct (Nat.eqb (nat_of_ascii c1) 34); [| discriminate].
  destruct (take_n_hex 64 s1 "") as [[d0 r0] |] eqn:Etk; [| discriminate].
  destruct r0 as [| c2 r2]; [ discriminate |].
  destruct (Nat.eqb (nat_of_ascii c2) 34); [| discriminate].
  injection H as <- _.
  destruct (take_n_hex_wf 64 s1 "" d0 (String c2 r2) Etk eq_refl) as [Hl Hh].
  unfold CanonicalV1.is_hex64. cbn [String.length] in Hl.
  rewrite Hl, Hh. reflexivity.
Qed.

Lemma parse_str_body_all_ascii : forall f s acc v r,
  (String.length s <= f)%nat ->
  parse_str_body s acc = Some (v, r) ->
  all_ascii acc = true -> all_ascii v = true.
Proof.
  induction f as [| f IHf]; intros s acc v r Hlen H Hacc.
  - destruct s; [ discriminate | cbn [String.length] in Hlen; lia ].
  - destruct s as [| c s]; [ discriminate |].
    cbn [String.length] in Hlen.
    assert (Hasc : forall X, X < 128 ->
              all_ascii (acc ++ String (ascii_of_nat X) "") = true).
    { intros X HX. rewrite all_ascii_app, Hacc. cbn [all_ascii].
      rewrite Bool.andb_true_r, (Ascii.nat_ascii_embedding X ltac:(lia)).
      apply Nat.ltb_lt; lia. }
    cbn [parse_str_body] in H.
    destruct (Nat.eqb (nat_of_ascii c) 34) eqn:E34; cbn match in H.
    { injection H as <- _. exact Hacc. }
    destruct (Nat.eqb (nat_of_ascii c) 92) eqn:E92; cbn match in H.
    { destruct s as [| e s]; [ discriminate |]. cbn [String.length] in Hlen.
      destruct (Nat.eqb (nat_of_ascii e) 34) eqn:D1; cbn match in H;
        [ apply (IHf s _ v r ltac:(lia) H (Hasc 34 ltac:(lia))) |].
      destruct (Nat.eqb (nat_of_ascii e) 92) eqn:D2; cbn match in H;
        [ apply (IHf s _ v r ltac:(lia) H (Hasc 92 ltac:(lia))) |].
      destruct (Nat.eqb (nat_of_ascii e) 98) eqn:D3; cbn match in H;
        [ apply (IHf s _ v r ltac:(lia) H (Hasc 8 ltac:(lia))) |].
      destruct (Nat.eqb (nat_of_ascii e) 116) eqn:D4; cbn match in H;
        [ apply (IHf s _ v r ltac:(lia) H (Hasc 9 ltac:(lia))) |].
      destruct (Nat.eqb (nat_of_ascii e) 110) eqn:D5; cbn match in H;
        [ apply (IHf s _ v r ltac:(lia) H (Hasc 10 ltac:(lia))) |].
      destruct (Nat.eqb (nat_of_ascii e) 102) eqn:D6; cbn match in H;
        [ apply (IHf s _ v r ltac:(lia) H (Hasc 12 ltac:(lia))) |].
      destruct (Nat.eqb (nat_of_ascii e) 114) eqn:D7; cbn match in H;
        [ apply (IHf s _ v r ltac:(lia) H (Hasc 13 ltac:(lia))) |].
      destruct (Nat.eqb (nat_of_ascii e) 117) eqn:D8; cbn match in H;
        [| discriminate].
      destruct s as [| z0 s]; [ discriminate |].
      destruct s as [| z1 s]; [ discriminate |].
      destruct s as [| h0 s]; [ discriminate |].
      destruct s as [| h1 s]; [ discriminate |].
      cbn [String.length] in Hlen.
      destruct (andb (Nat.eqb (nat_of_ascii z0) 48) (Nat.eqb (nat_of_ascii z1) 48));
        cbn match in H; [| discriminate].
      destruct (hexval h0) as [hi|] eqn:Eh0; cbn match in H; [| discriminate].
      destruct (hexval h1) as [lo|] eqn:Eh1; cbn match in H; [| discriminate].
      destruct (andb (Nat.ltb (hi * 16 + lo) 32)
                 (andb (negb (Nat.eqb (hi * 16 + lo) 8))
                  (andb (negb (Nat.eqb (hi * 16 + lo) 9))
                   (andb (negb (Nat.eqb (hi * 16 + lo) 10))
                    (andb (negb (Nat.eqb (hi * 16 + lo) 12))
                     (negb (Nat.eqb (hi * 16 + lo) 13))))))) eqn:Eg;
        cbn match in H; [| discriminate].
      apply Bool.andb_true_iff in Eg as [Eg _]. apply Nat.ltb_lt in Eg.
      apply (IHf s _ v r ltac:(lia) H (Hasc (hi*16+lo) ltac:(lia))). }
    destruct (Nat.ltb (nat_of_ascii c) 32) eqn:Elt; cbn match in H;
      [ discriminate |].
    destruct (Nat.ltb 127 (nat_of_ascii c)) eqn:Egt; cbn match in H;
      [ discriminate |].
    apply Nat.ltb_ge in Elt, Egt.
    apply (IHf s _ v r ltac:(lia) H).
    rewrite all_ascii_app, Hacc. cbn [all_ascii]. rewrite Bool.andb_true_r.
    apply Nat.ltb_lt; lia.
Qed.

Lemma parse_json_string_wf : forall s v r,
  parse_json_string s = Some (v, r) -> all_ascii v = true.
Proof.
  intros s v r H. unfold parse_json_string in H.
  destruct s as [| c s]; [ discriminate |].
  destruct (Nat.eqb (nat_of_ascii c) 34); [| discriminate].
  eapply parse_str_body_all_ascii; [ reflexivity | exact H | reflexivity ].
Qed.

Lemma forallb_rev : forall (A : Type) (f : A -> bool) (l : list A),
  forallb f (List.rev l) = forallb f l.
Proof.
  induction l as [| x l IH]; [ reflexivity |].
  cbn [List.rev forallb]. rewrite forallb_app, IH. cbn [forallb].
  rewrite Bool.andb_true_r. apply Bool.andb_comm.
Qed.

Lemma parse_dig_array_elems_wf : forall f s acc l r,
  parse_dig_array_elems f s acc = Some (l, r) ->
  forallb CanonicalV1.is_hex64 acc = true ->
  forallb CanonicalV1.is_hex64 l = true.
Proof.
  induction f as [| f IHf]; intros s acc l r H Hacc; [ discriminate |].
  cbn [parse_dig_array_elems] in H.
  destruct (parse_digest_field s) as [[d s1] |] eqn:Ed; [| discriminate].
  destruct s1 as [| c rest]; [ discriminate |].
  pose proof (parse_digest_field_wf s d (String c rest) Ed) as Hd.
  destruct (Nat.eqb (nat_of_ascii c) 93) eqn:E93.
  { injection H as HL _. subst l.
    rewrite forallb_app, forallb_rev. cbn [forallb].
    rewrite Hacc, Hd. reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 44) eqn:E44; [| discriminate].
  eapply IHf; [ exact H |].
  cbn [forallb]. rewrite Hacc, Hd. reflexivity.
Qed.

Lemma parse_dig_array_wf : forall s l r,
  parse_dig_array s = Some (l, r) -> forallb CanonicalV1.is_hex64 l = true.
Proof.
  intros s l r H. unfold parse_dig_array in H.
  destruct s as [| c rest]; [ discriminate |].
  destruct (Nat.eqb (nat_of_ascii c) 91); [| discriminate].
  destruct (starts_with (String "]"%char "") rest) as [rest2 |] eqn:Es.
  { injection H as <- _. reflexivity. }
  eapply parse_dig_array_elems_wf; [ exact H | reflexivity ].
Qed.

Theorem parse_manifest_impl_wf : forall m v,
  parse_manifest_impl m = Some v -> CanonicalV1.manifest_wellformed v.
Proof.
  intros m v H. unfold parse_manifest_impl in H.
  destruct (negb (CanonicalV1.valid_utf8 (manifest_token m))); [ discriminate |].
  destruct (starts_with _ _) as [s1|] eqn:?; [| discriminate].
  destruct (parse_json_string s1) as [[aid s2]|] eqn:Eaid; [| discriminate].
  destruct (starts_with _ s2) as [s3|] eqn:?; [| discriminate].
  destruct (parse_json_string s3) as [[cid s4]|] eqn:Ecid; [| discriminate].
  destruct (starts_with _ s4) as [s5|] eqn:?; [| discriminate].
  destruct (parse_digest_field s5) as [[idig s6]|] eqn:Ei; [| discriminate].
  destruct (starts_with _ s6) as [s7|] eqn:?; [| discriminate].
  destruct (parse_digest_field s7) as [[mdig s8]|] eqn:Em; [| discriminate].
  destruct (starts_with _ s8) as [s9|] eqn:?; [| discriminate].
  destruct (parse_digest_field s9) as [[pdig s10]|] eqn:Ep; [| discriminate].
  destruct (starts_with _ s10) as [s11|] eqn:?; [| discriminate].
  destruct (parse_digest_field s11) as [[ph s12]|] eqn:Eph; [| discriminate].
  destruct (starts_with _ s12) as [s13|] eqn:?; [| discriminate].
  destruct (parse_dig_array s13) as [[subs s14]|] eqn:Esub; [| discriminate].
  destruct (starts_with "}" s14) as [rr|] eqn:?; [| discriminate].
  destruct rr; [| discriminate].
  injection H as <-. unfold CanonicalV1.manifest_wellformed. cbn.
  repeat split.
  - exact (parse_digest_field_wf _ _ _ Eph).
  - exact (parse_digest_field_wf _ _ _ Em).
  - exact (parse_digest_field_wf _ _ _ Ep).
  - exact (parse_digest_field_wf _ _ _ Ei).
  - exact (parse_dig_array_wf _ _ _ Esub).
  - apply all_ascii_valid_utf8. exact (parse_json_string_wf _ _ _ Eaid).
  - apply all_ascii_valid_utf8. exact (parse_json_string_wf _ _ _ Ecid).
Qed.

(* ================= 2.4.1 authenticate_manifest ================= *)

Section Auth.
Variable sha256_hex : bytes -> digest.
Variable ed25519_verify : bytes -> bytes -> bytes -> bool.
  (* pubkey (32B) -> signature (64B) -> message -> bool *)
Variable ed25519_pubkey_valid : bytes -> bool.
  (* F.3: a 32-byte string decodes to a CANONICAL, NON-small-order
     edwards25519 point (rejects the identity / cofactor-torsion keys the
     bare group equation would otherwise accept for S = 0). *)

Definition signer_authorised_impl (cfg : verifier_config) (mc : manifest_commitment)
  : bool :=
  signer_in (config_trust_anchor cfg) (commitment_signer mc).

Definition signature_valid_impl (cfg : verifier_config) (mc : manifest_commitment)
  (M : manifest) : bool :=
  match parse_manifest_impl M with
  | None => false
  | Some v =>
      String.eqb (commitment_digest mc)
                 (campaign_manifest_digest sha256_hex v) &&
      match ta_key_of (ta_keys (config_trust_anchor cfg)) (commitment_signer mc) with
      | None => false
      | Some k =>
          ed25519_pubkey_valid k &&
          ed25519_verify k (commitment_signature mc) (commitment_digest mc)
      end
  end.

(* the 2.4.1 predicate, concretely. *)
Definition manifest_authenticated_by_impl (cfg : verifier_config)
  (mc : manifest_commitment) (M : manifest) : Prop :=
  exists v k,
    parse_manifest_impl M = Some v /\
    commitment_digest mc = campaign_manifest_digest sha256_hex v /\
    signer_in (config_trust_anchor cfg) (commitment_signer mc) = true /\
    ta_key_of (ta_keys (config_trust_anchor cfg)) (commitment_signer mc) = Some k /\
    ed25519_pubkey_valid k = true /\
    ed25519_verify k (commitment_signature mc) (commitment_digest mc) = true.

Theorem signature_valid_impl_sound :
  forall cfg mc M,
    signature_valid_impl cfg mc M = true ->
    exists v k,
      parse_manifest_impl M = Some v /\
      commitment_digest mc = campaign_manifest_digest sha256_hex v /\
      ta_key_of (ta_keys (config_trust_anchor cfg)) (commitment_signer mc) = Some k /\
      ed25519_pubkey_valid k = true /\
      ed25519_verify k (commitment_signature mc) (commitment_digest mc) = true.
Proof.
  intros cfg mc M H. unfold signature_valid_impl in H.
  destruct (parse_manifest_impl M) as [v|] eqn:Ev; [| discriminate].
  apply andb_true_iff in H as [Hd Hk].
  apply String.eqb_eq in Hd.
  destruct (ta_key_of (ta_keys (config_trust_anchor cfg)) (commitment_signer mc))
    as [k|] eqn:Ek; [| discriminate].
  apply andb_true_iff in Hk as [Hkv Hver].
  exists v, k. repeat split; assumption.
Qed.

Theorem signer_authorised_impl_iff :
  forall cfg mc,
    signer_authorised_impl cfg mc = true <->
    signer_in (config_trust_anchor cfg) (commitment_signer mc) = true.
Proof. intros. unfold signer_authorised_impl. reflexivity. Qed.

(* signer authorisation AND signature validity give the composed predicate. *)
Theorem auth_from_ops :
  forall cfg mc M,
    signer_authorised_impl cfg mc = true ->
    signature_valid_impl cfg mc M = true ->
    manifest_authenticated_by_impl cfg mc M.
Proof.
  intros cfg mc M Hsa Hsv.
  destruct (signature_valid_impl_sound cfg mc M Hsv)
    as (v & k & Hpm & Hdig & Hkey & Hkv & Hver).
  unfold signer_authorised_impl in Hsa.
  exists v, k. repeat split; assumption.
Qed.

(* ================= wiring into validate_campaign ================= *)

Definition concrete_auth_ops (base : primitive_ops) : primitive_ops :=
  mkPrimitiveOps
    parse_commitment_impl
    signer_authorised_impl
    signature_valid_impl
    (op_manifest_policy_matches base)
    (op_manifest_audit_matches base)
    (op_manifest_context_matches base)
    (op_ledger_mismatch base)
    (op_record_identity_mismatch base)
    (op_completeness_wellformed base)
    (op_stage1_check base)
    (op_preflight base)
    (op_eval_o3 base)
    (op_stage2_check base)
    (op_record_crosscheck base)
    (op_transcript_digest base).

(* ----- capstone: validation success => the 2.4.1 authentication fact ----- *)

Theorem validate_campaign_authenticates :
  forall base ti ac l0,
    validate_campaign (concrete_auth_ops base) ti = ValidCampaign ac l0 ->
    manifest_authenticated_by_impl (ti_config ti)
      (authenticated_commitment ac) (authenticated_manifest ac).
Proof.
  intros base ti ac l0 H.
  destruct (validate_campaign_valid_guards (concrete_auth_ops base) ti H)
    as (mc & _ & Hsa & Hsv & _ & _ & Hac).
  subst ac.
  cbn [authenticated_of authenticated_commitment authenticated_manifest] in *.
  cbn [concrete_auth_ops op_signer_authorised op_signature_valid] in Hsa, Hsv.
  exact (auth_from_ops (ti_config ti) mc (ti_manifest ti) Hsa Hsv).
Qed.

(* the same, for any [ops] whose signer/signature fields are the impls -- used
   by the integrated pipeline where the manifest-matcher fields also change. *)
Theorem validate_campaign_authenticates_ops :
  forall ops ti ac l0,
    op_signer_authorised ops = signer_authorised_impl ->
    op_signature_valid ops = signature_valid_impl ->
    validate_campaign ops ti = ValidCampaign ac l0 ->
    manifest_authenticated_by_impl (ti_config ti)
      (authenticated_commitment ac) (authenticated_manifest ac).
Proof.
  intros ops ti ac l0 Hsa0 Hsv0 H.
  destruct (validate_campaign_valid_guards ops ti H)
    as (mc & _ & Hsa & Hsv & _ & _ & Hac).
  subst ac.
  cbn [authenticated_of authenticated_commitment authenticated_manifest] in *.
  rewrite Hsa0 in Hsa. rewrite Hsv0 in Hsv.
  exact (auth_from_ops (ti_config ti) mc (ti_manifest ti) Hsa Hsv).
Qed.

(* the retrieval-integrity residual stays explicit: authentication proves the
   commitment is validly signed by an authorised signer over the manifest
   digest, NOT that the retrieved object is the intended audit's object. *)

End Auth.
