(** A bounded fragment of the AUDIT_POLICY_AND_EVIDENCE.md 2.2 canonicalisation,
    covering exactly what authenticated-manifest validation needs:

    - esc_str / json_string : the 2.2.2 string escaping (only the seven named
      escapes plus U+0000..U+001F as backslash-u-00xx lowercase; every other byte
      raw).
    - render_manifest : canonicalise_v1(to_cv(campaign_manifest)) for the FIXED
      2.1 / 2.4-step-6 schema -- an object with the five keys in byte-ascending
      order, context_digests a nested three-key object.
    - digest_v1 : SHA256_hex( utf8(tag) ++ 0x1F ++ canonical bytes ).
      sha256_hex is an F.3 named component (SHA-256, lowercase hex); it is NOT
      implemented or proved here.  The OCaml harness links a real SHA-256 and
      checks the frozen pcfw.campaign_manifest.v1 vector.

    render_manifest_frozen_vector proves (by vm_compute) that render_manifest on
    the frozen inputs is byte-identical to the payload string in the AUDIT_POLICY
    2.2.5 vector table -- independent of sha256_hex.

    This is NOT a general JSON canonicaliser: only the campaign_manifest shape is
    rendered; arbitrary canonical_value trees are out of scope for this unit. *)

From Coq Require Import String Ascii List Bool.
Import ListNotations.
Open Scope string_scope.

Definition digest := string.
Definition bytes := string.

(* the campaign_manifest.context_digests object (2.2.5 context_descriptor). *)
Record context_descriptor := mkContextDescriptor {
  cd_model_artifact_digest : digest;
  cd_preprocessing_digest : digest;
  cd_inference_spec_digest : digest
}.

(* the campaign_manifest fields this system reads (2.1 / 2.4 step 6). *)
Record campaign_manifest_view := mkCampaignManifestView {
  cm_audit_instance_id : string;
  cm_campaign_id : string;
  cm_context_digests : context_descriptor;
  cm_policy_hash : digest;
  cm_submission_digests : list digest
}.

(* ----- 2.2.2 string escaping ----- *)

Definition hexdig (n : nat) : ascii :=
  match n with
  | 0 => "0"%char | 1 => "1"%char | 2 => "2"%char | 3 => "3"%char
  | 4 => "4"%char | 5 => "5"%char | 6 => "6"%char | 7 => "7"%char
  | 8 => "8"%char | 9 => "9"%char | 10 => "a"%char | 11 => "b"%char
  | 12 => "c"%char | 13 => "d"%char | 14 => "e"%char | _ => "f"%char
  end.

Definition a_bslash : ascii := ascii_of_nat 92.
Definition a_dquote : ascii := ascii_of_nat 34.

Definition esc_char (c : ascii) : string :=
  let n := nat_of_ascii c in
  if Nat.eqb n 34 then String a_bslash (String a_dquote EmptyString)
  else if Nat.eqb n 92 then String a_bslash (String a_bslash EmptyString)
  else if Nat.eqb n 8 then String a_bslash (String "b"%char EmptyString)
  else if Nat.eqb n 9 then String a_bslash (String "t"%char EmptyString)
  else if Nat.eqb n 10 then String a_bslash (String "n"%char EmptyString)
  else if Nat.eqb n 12 then String a_bslash (String "f"%char EmptyString)
  else if Nat.eqb n 13 then String a_bslash (String "r"%char EmptyString)
  else if Nat.ltb n 32 then
    String a_bslash (String "u"%char (String "0"%char (String "0"%char
      (String (hexdig (Nat.div n 16)) (String (hexdig (Nat.modulo n 16)) EmptyString)))))
  else String c EmptyString.

Fixpoint esc_str (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => esc_char c ++ esc_str rest
  end.

Definition json_string (s : string) : string :=
  String a_dquote (esc_str s ++ String a_dquote EmptyString).

(* ----- render campaign_manifest ----- *)

Definition kv (k : string) (v : string) : string := json_string k ++ ":" ++ v.

Definition render_context_descriptor (d : context_descriptor) : string :=
  "{" ++ kv "inference_spec_digest" (json_string (cd_inference_spec_digest d)) ++ ","
      ++ kv "model_artifact_digest" (json_string (cd_model_artifact_digest d)) ++ ","
      ++ kv "preprocessing_digest" (json_string (cd_preprocessing_digest d)) ++ "}".

Definition render_string_array (xs : list string) : string :=
  "[" ++ String.concat "," (List.map json_string xs) ++ "]".

Definition render_manifest (m : campaign_manifest_view) : string :=
  "{" ++ kv "audit_instance_id" (json_string (cm_audit_instance_id m)) ++ ","
      ++ kv "campaign_id" (json_string (cm_campaign_id m)) ++ ","
      ++ kv "context_digests" (render_context_descriptor (cm_context_digests m)) ++ ","
      ++ kv "policy_hash" (json_string (cm_policy_hash m)) ++ ","
      ++ kv "submission_digests" (render_string_array (cm_submission_digests m)) ++ "}".

(* ----- 2.2.4 digest_v1 ----- *)

Definition unit_separator : string := String (ascii_of_nat 31) EmptyString.

Section Digest.
Variable sha256_hex : bytes -> digest.   (* F.3 named component *)

Definition digest_v1 (tag : string) (canonical : bytes) : digest :=
  sha256_hex (tag ++ unit_separator ++ canonical).

Definition campaign_manifest_digest (m : campaign_manifest_view) : digest :=
  digest_v1 "pcfw.campaign_manifest.v1" (render_manifest m).

Lemma campaign_manifest_digest_unfold :
  forall m,
    campaign_manifest_digest m
    = sha256_hex ("pcfw.campaign_manifest.v1" ++ unit_separator ++ render_manifest m).
Proof. reflexivity. Qed.

End Digest.

(* ----- the frozen 2.2.5 vector: canonical bytes are exactly the payload ----- *)

Definition frozen_manifest_vector : campaign_manifest_view :=
  mkCampaignManifestView "ai-0001" "cmp-1"
    (mkContextDescriptor "mm" "pp" "ii") "fb0105" ["d1"; "d2"].

Lemma render_manifest_frozen_vector :
  render_manifest frozen_manifest_vector =
  "{""audit_instance_id"":""ai-0001"",""campaign_id"":""cmp-1"",""context_digests"":{""inference_spec_digest"":""ii"",""model_artifact_digest"":""mm"",""preprocessing_digest"":""pp""},""policy_hash"":""fb0105"",""submission_digests"":[""d1"",""d2""]}".
Proof. vm_compute. reflexivity. Qed.

(* ----- schema predicates ----- *)

Definition is_lower_hex_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (andb (Nat.leb 48 n) (Nat.leb n 57))     (* 0-9 *)
      (andb (Nat.leb 97 n) (Nat.leb n 102)).   (* a-f *)

Fixpoint all_lower_hex (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c r => is_lower_hex_digit c && all_lower_hex r
  end.

Definition is_hex64 (s : string) : bool :=
  andb (Nat.eqb (String.length s) 64) (all_lower_hex s).

(* structural UTF-8 well-formedness: byte-length prefixes + continuation bytes,
   with the RFC 3629 range guards (no overlong forms, no surrogates, <= U+10FFFF).
   Fuel = the byte length. *)
Definition is_cont (c : ascii) : bool :=
  let n := nat_of_ascii c in andb (Nat.leb 128 n) (Nat.leb n 191).

Fixpoint valid_utf8_aux (fuel : nat) (s : string) : bool :=
  match fuel with
  | 0 => match s with EmptyString => true | _ => false end
  | S f =>
    match s with
    | EmptyString => true
    | String c0 r0 =>
      let n0 := nat_of_ascii c0 in
      if Nat.ltb n0 128 then valid_utf8_aux f r0
      else if andb (Nat.leb 194 n0) (Nat.leb n0 223) then
        match r0 with
        | String c1 r1 => if is_cont c1 then valid_utf8_aux f r1 else false
        | _ => false end
      else if andb (Nat.leb 224 n0) (Nat.leb n0 239) then
        match r0 with
        | String c1 (String c2 r2) =>
          let n1 := nat_of_ascii c1 in
          let lo := if Nat.eqb n0 224 then 160 else 128 in
          let hi := if Nat.eqb n0 237 then 159 else 191 in
          if andb (andb (Nat.leb lo n1) (Nat.leb n1 hi)) (is_cont c2)
          then valid_utf8_aux f r2 else false
        | _ => false end
      else if andb (Nat.leb 240 n0) (Nat.leb n0 244) then
        match r0 with
        | String c1 (String c2 (String c3 r3)) =>
          let n1 := nat_of_ascii c1 in
          let lo := if Nat.eqb n0 240 then 144 else 128 in
          let hi := if Nat.eqb n0 244 then 143 else 191 in
          if andb (andb (andb (Nat.leb lo n1) (Nat.leb n1 hi)) (is_cont c2)) (is_cont c3)
          then valid_utf8_aux f r3 else false
        | _ => false end
      else false
    end
  end.

Definition valid_utf8 (s : string) : bool := valid_utf8_aux (String.length s) s.

Definition manifest_wellformed (m : campaign_manifest_view) : Prop :=
  is_hex64 (cm_policy_hash m) = true /\
  is_hex64 (cd_model_artifact_digest (cm_context_digests m)) = true /\
  is_hex64 (cd_preprocessing_digest (cm_context_digests m)) = true /\
  is_hex64 (cd_inference_spec_digest (cm_context_digests m)) = true /\
  forallb is_hex64 (cm_submission_digests m) = true /\
  valid_utf8 (cm_audit_instance_id m) = true /\
  valid_utf8 (cm_campaign_id m) = true.

(* a schema-valid manifest (full-length lowercase-hex digests) for the parser
   round-trip -- distinct from [frozen_manifest_vector], whose short placeholder
   digests are deliberately NOT schema-valid (AUDIT_POLICY 2.2.5 readability). *)
Definition d64_a : digest := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".
Definition d64_b : digest := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef".
Definition d64_c : digest := "fedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210".
Definition d64_d : digest := "00000000000000000000000000000000000000000000000000000000000000ff".

Definition schema_valid_manifest : campaign_manifest_view :=
  mkCampaignManifestView "ai-0001" "cmp-1"
    (mkContextDescriptor d64_a d64_b d64_c) d64_a [d64_b; d64_d].

Lemma schema_valid_manifest_wf : manifest_wellformed schema_valid_manifest.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* escaping sanity: raw  x " y \ z  becomes  x \" y \\ z  (2.2.2). *)
Definition esc_test_raw : string :=
  String "x"%char (String a_dquote (String "y"%char
    (String a_bslash (String "z"%char EmptyString)))).
Definition esc_test_expected : string :=
  String "x"%char (String a_bslash (String a_dquote (String "y"%char
    (String a_bslash (String a_bslash (String "z"%char EmptyString)))))).

Lemma esc_str_vector : esc_str esc_test_raw = esc_test_expected.
Proof. vm_compute. reflexivity. Qed.
