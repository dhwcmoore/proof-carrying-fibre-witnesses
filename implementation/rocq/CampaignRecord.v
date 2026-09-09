(** Structured campaign-record view + decoder, and concrete
    [op_record_identity_mismatch] (VERDICT_SEMANTICS.md 5 step 8).

    The wire-level [Orchestration.campaign_record] (`{ record_token : string }`)
    is UNCHANGED.  This module adds -- in the established
    [manifest] / [campaign_manifest_view] pattern -- a structured
    [campaign_record_view] and a strict canonical decoder [parse_record_impl].

    [campaign_record_view] is BOUNDED to the five step-8 identity fields:
      campaign_id, audit_instance_id, policy_hash, context_digests, manifest_digest

    [parse_record_impl] nonetheless decodes a FULL campaign record over the
    canonical ASCII-wire subset: the eight keys in byte-ascending order --
      audit_instance_id, campaign_id, completeness, context_digests,
      manifest_digest, policy_hash, recorded_results, resource_budget --
    with [completeness] / [recorded_results] / [resource_budget] syntactically
    CONSUMED by [skip_value], not interpreted.  Cross-checking [recorded_results]
    is a later [op_record_crosscheck] unit; that needs those fields represented,
    not just skipped.

    ASCII-WIRE RESTRICTION (explicit, as for the manifest decoder): the whole
    input is gated on [CanonicalV1.valid_utf8], and every string -- identifiers,
    digests, and every string inside a skipped value -- is read by
    [ManifestAuthentication.parse_json_string], which accepts raw bytes only in
    ASCII 0x20..0x7F (plus the escape-decodable controls via [\uXXXX]).  A
    canonical record carrying a raw non-ASCII (>= 0x80) UTF-8 string is REJECTED
    (a UTF-8-tolerant decoder is future work).  Within that subset [skip_value]
    enforces canonical form: integers exactly [0 | -?[1-9][0-9]*]; object keys
    strictly byte-ascending and duplicate-free.  Non-canonical bytes are
    rejected, not silently accepted.

    [record_identity_mismatch_impl] decodes the record and the manifest and, in
    the FROZEN order

      1. campaign_id       vs  cm.campaign_id
      2. audit_instance_id vs  cm.audit_instance_id
      3. policy_hash       vs  cm.policy_hash
      4. context_digests   vs  cm.context_digests
      5. manifest_digest   vs  commitment_digest mc

    returns [Some <field name>] at the first inequality, else [None].  A record
    decode failure is [Some sentinel_record_undecodable]; a manifest decode
    failure is [Some sentinel_manifest_undecodable].  Both sentinels begin with
    ASCII 0x21 ('!'), which no field name contains, so they can never be confused
    with an ordinary [Some field] (see [record_sentinels_distinct]). *)

From Coq Require Import String Ascii List Bool.
From PCFW Require Import Orchestration CanonicalV1 ManifestAuthentication.
Import ListNotations.
Open Scope string_scope.

(* ================= structured view ================= *)

Record campaign_record_view := mkCampaignRecordView {
  crv_campaign_id       : string;
  crv_audit_instance_id : string;
  crv_policy_hash       : digest;
  crv_context_digests   : context_descriptor;
  crv_manifest_digest   : digest
}.

(* ----- canonical-JSON value skipper (ASCII-wire subset) -----
   Consumes exactly ONE canonical JSON value (string, integer, boolean, null,
   array, object) and returns the suffix.  Used to syntactically consume the
   record's non-identity fields ([completeness], [recorded_results],
   [resource_budget]) without interpreting them.  It ENFORCES the canonical form:
     - integers exactly  [0 | -?[1-9][0-9]*]  (no leading zero, no [-0]);
     - object keys strictly byte-ascending and duplicate-free;
     - strings via [parse_json_string] -- the same canonical ASCII-wire subset
       the manifest decoder uses (raw non-ASCII UTF-8 rejected -- see the header).
   [fuel] bounds nesting/length; [String.length s] is a safe bound. *)

Fixpoint str_ltb (a b : string) : bool :=
  match a, b with
  | EmptyString, EmptyString => false
  | EmptyString, String _ _  => true
  | String _ _, EmptyString  => false
  | String ca ra, String cb rb =>
      let na := nat_of_ascii ca in let nb := nat_of_ascii cb in
      if Nat.ltb na nb then true
      else if Nat.ltb nb na then false
      else str_ltb ra rb
  end.

Fixpoint skip_digits (s : string) : string :=
  match s with
  | String c r =>
      if andb (Nat.leb 48 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 57)
      then skip_digits r else s
  | EmptyString => EmptyString
  end.

(* exactly  0 | -?[1-9][0-9]*  -- rejects 00, 01, -0, -01 *)
Definition skip_number (s : string) : option string :=
  let '(has_minus, s1) :=
    match s with
    | String c r => if Nat.eqb (nat_of_ascii c) 45 then (true, r) else (false, s)
    | EmptyString => (false, s)
    end in
  match s1 with
  | EmptyString => None
  | String c1 r1 =>
      let n1 := nat_of_ascii c1 in
      if Nat.eqb n1 48 then
        if has_minus then None
        else match r1 with
             | String c2 _ =>
                 if andb (Nat.leb 48 (nat_of_ascii c2)) (Nat.leb (nat_of_ascii c2) 57)
                 then None else Some r1
             | EmptyString => Some r1
             end
      else if andb (Nat.leb 49 n1) (Nat.leb n1 57) then Some (skip_digits r1)
      else None
  end.

Fixpoint skip_value (fuel : nat) (s : string) : option string :=
  match fuel with
  | 0 => None
  | S f =>
      match s with
      | EmptyString => None
      | String c rest =>
          let n := nat_of_ascii c in
          if Nat.eqb n 34 then
            match parse_json_string s with Some (_, r) => Some r | None => None end
          else if Nat.eqb n 123 then
            match rest with
            | String c2 r2 =>
                if Nat.eqb (nat_of_ascii c2) 125 then Some r2
                else skip_members f None rest
            | EmptyString => None
            end
          else if Nat.eqb n 91 then
            match rest with
            | String c2 r2 =>
                if Nat.eqb (nat_of_ascii c2) 93 then Some r2
                else skip_elems f rest
            | EmptyString => None
            end
          else if orb (Nat.eqb n 45) (andb (Nat.leb 48 n) (Nat.leb n 57)) then
            skip_number s
          else
            match starts_with "true" s with Some r => Some r | None =>
            match starts_with "false" s with Some r => Some r | None =>
            match starts_with "null" s with Some r => Some r | None => None
            end end end
      end
  end
with skip_members (fuel : nat) (prev : option string) (s : string) : option string :=
  match fuel with
  | 0 => None
  | S f =>
      match parse_json_string s with
      | None => None
      | Some (key, s1) =>
          if match prev with None => true | Some p => str_ltb p key end then
            match s1 with
            | String c s2 =>
                if Nat.eqb (nat_of_ascii c) 58 then
                  match skip_value f s2 with
                  | None => None
                  | Some s3 =>
                      match s3 with
                      | String c3 s4 =>
                          if Nat.eqb (nat_of_ascii c3) 44 then skip_members f (Some key) s4
                          else if Nat.eqb (nat_of_ascii c3) 125 then Some s4
                          else None
                      | EmptyString => None
                      end
                  end
                else None
            | EmptyString => None
            end
          else None
      end
  end
with skip_elems (fuel : nat) (s : string) : option string :=
  match fuel with
  | 0 => None
  | S f =>
      match skip_value f s with
      | None => None
      | Some s1 =>
          match s1 with
          | String c s2 =>
              if Nat.eqb (nat_of_ascii c) 44 then skip_elems f s2
              else if Nat.eqb (nat_of_ascii c) 93 then Some s2
              else None
          | EmptyString => None
          end
      end
  end.

(* render a canonical FULL campaign record (8 keys, byte-ascending): the five
   identity fields plus [completeness] (the no-payload [Unknown] form, i.e. the
   string "unknown"), an empty [recorded_results], an empty [resource_budget]. *)
Definition render_campaign_record (v : campaign_record_view) : string :=
  "{" ++ kv "audit_instance_id" (json_string (crv_audit_instance_id v)) ++ ","
      ++ kv "campaign_id" (json_string (crv_campaign_id v)) ++ ","
      ++ kv "completeness" (json_string "unknown") ++ ","
      ++ kv "context_digests" (render_context_descriptor (crv_context_digests v)) ++ ","
      ++ kv "manifest_digest" (json_string (crv_manifest_digest v)) ++ ","
      ++ kv "policy_hash" (json_string (crv_policy_hash v)) ++ ","
      ++ kv "recorded_results" "[]" ++ ","
      ++ kv "resource_budget" "{}" ++ "}".

(* strict canonical decoder for a FULL campaign record over the ASCII-wire
   subset: the eight keys byte-ascending, no whitespace; identifier/digest
   fields ASCII (raw non-ASCII UTF-8 rejected -- see header); the three
   non-identity fields are syntactically consumed with [skip_value] (which itself
   enforces canonical integer syntax and strictly-ascending, duplicate-free keys
   in every skipped object), not interpreted -- cross-checking [recorded_results]
   is a later [op_record_crosscheck] unit. *)
Definition parse_record_impl (r : campaign_record) : option campaign_record_view :=
  let s := record_token r in
  if negb (CanonicalV1.valid_utf8 s) then None else
  let fuel := String.length s in
  match starts_with "{""audit_instance_id"":" s with None => None | Some s1 =>
  match parse_json_string s1 with None => None | Some (aid, s2) =>
  match starts_with ",""campaign_id"":" s2 with None => None | Some s3 =>
  match parse_json_string s3 with None => None | Some (cid, s4) =>
  match starts_with ",""completeness"":" s4 with None => None | Some s5 =>
  match skip_value fuel s5 with None => None | Some s6 =>
  match starts_with ",""context_digests"":{""inference_spec_digest"":" s6
  with None => None | Some s7 =>
  match parse_digest_field s7 with None => None | Some (idig, s8) =>
  match starts_with ",""model_artifact_digest"":" s8 with None => None | Some s9 =>
  match parse_digest_field s9 with None => None | Some (mdig, s10) =>
  match starts_with ",""preprocessing_digest"":" s10 with None => None | Some s11 =>
  match parse_digest_field s11 with None => None | Some (pdig, s12) =>
  match starts_with "},""manifest_digest"":" s12 with None => None | Some s13 =>
  match parse_digest_field s13 with None => None | Some (mdg, s14) =>
  match starts_with ",""policy_hash"":" s14 with None => None | Some s15 =>
  match parse_digest_field s15 with None => None | Some (ph, s16) =>
  match starts_with ",""recorded_results"":" s16 with None => None | Some s17 =>
  match skip_value fuel s17 with None => None | Some s18 =>
  match starts_with ",""resource_budget"":" s18 with None => None | Some s19 =>
  match skip_value fuel s19 with None => None | Some s20 =>
  match starts_with "}" s20 with
  | Some EmptyString =>
      Some (mkCampaignRecordView cid aid ph
              (CanonicalV1.mkContextDescriptor mdig pdig idig) mdg)
  | _ => None
  end end end end end end end end end end end end end end end end end end end end end.

(* ----- a schema-valid vector, matching CanonicalV1.schema_valid_manifest's
   identity fields ----- *)
Definition schema_valid_record : campaign_record_view :=
  mkCampaignRecordView "cmp-1" "ai-0001" CanonicalV1.d64_a
    (CanonicalV1.mkContextDescriptor CanonicalV1.d64_a CanonicalV1.d64_b CanonicalV1.d64_c)
    CanonicalV1.d64_d.

Lemma parse_record_impl_schema_valid_vector :
  parse_record_impl (mkCampaignRecord (render_campaign_record schema_valid_record))
  = Some schema_valid_record.
Proof. vm_compute. reflexivity. Qed.

(* a NORMATIVE full record (schema-valid, per AUDIT_POLICY 2.2.5): [completeness]
   is the payload-carrying {"k":"complete","v":{"body":...,"scheme":...}};
   [recorded_results] has one accepted-valid-witness entry
   ({"k":"accepted","v":"valid_witness"}) and one accepted-not-a-witness entry
   ({"k":"accepted","v":{"k":"not_a_witness","v":"inputs_equal"}}) whose finding
   is {"check_id":"C1","outcome":"fail","reason":"inputs_equal"} (a "fail"
   finding is consistent with not_a_witness); [resource_budget] is populated.
   Every nested object's keys are strictly byte-ascending. *)
Definition full_record_vector_wire : string :=
  "{""audit_instance_id"":""ai-0001"",""campaign_id"":""cmp-1"","
  ++ """completeness"":{""k"":""complete"",""v"":{""body"":""b"",""scheme"":""registry-v0""}},"
  ++ """context_digests"":{""inference_spec_digest"":""" ++ CanonicalV1.d64_c
  ++ """,""model_artifact_digest"":""" ++ CanonicalV1.d64_a
  ++ """,""preprocessing_digest"":""" ++ CanonicalV1.d64_b
  ++ """},""manifest_digest"":""" ++ CanonicalV1.d64_d
  ++ """,""policy_hash"":""" ++ CanonicalV1.d64_a
  ++ """,""recorded_results"":["
  ++    "{""findings"":[],""outcome"":{""k"":""accepted"",""v"":""valid_witness""},""submission_digest"":""" ++ CanonicalV1.d64_b ++ """,""submission_index"":0},"
  ++    "{""findings"":[{""check_id"":""C1"",""outcome"":""fail"",""reason"":""inputs_equal""}],""outcome"":{""k"":""accepted"",""v"":{""k"":""not_a_witness"",""v"":""inputs_equal""}},""submission_digest"":""" ++ CanonicalV1.d64_c ++ """,""submission_index"":1}"
  ++ "],""resource_budget"":{""max_candidates"":10,""max_memory_bytes"":1024}}".

Lemma parse_record_impl_full_record_vector :
  parse_record_impl (mkCampaignRecord full_record_vector_wire) = Some schema_valid_record.
Proof. vm_compute. reflexivity. Qed.

Lemma parse_record_impl_rejects_empty_object :
  parse_record_impl (mkCampaignRecord "{}") = None.
Proof. vm_compute. reflexivity. Qed.

(* ----- canonicality of [skip_value] over the [resource_budget] slot ----- *)
Definition rec_with_budget (budget : string) : string :=
  "{""audit_instance_id"":""ai-0001"",""campaign_id"":""cmp-1"",""completeness"":""unknown"","
  ++ """context_digests"":{""inference_spec_digest"":""" ++ CanonicalV1.d64_c
  ++ """,""model_artifact_digest"":""" ++ CanonicalV1.d64_a
  ++ """,""preprocessing_digest"":""" ++ CanonicalV1.d64_b
  ++ """},""manifest_digest"":""" ++ CanonicalV1.d64_d
  ++ """,""policy_hash"":""" ++ CanonicalV1.d64_a
  ++ """,""recorded_results"":[],""resource_budget"":" ++ budget ++ "}".

Lemma parse_record_impl_accepts_canonical_budget :
  parse_record_impl (mkCampaignRecord (rec_with_budget "{""max_candidates"":10}"))
  = Some schema_valid_record.
Proof. vm_compute. reflexivity. Qed.

Lemma parse_record_impl_rejects_leading_zero :
  parse_record_impl (mkCampaignRecord (rec_with_budget "{""max_candidates"":01}")) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma parse_record_impl_rejects_neg_zero :
  parse_record_impl (mkCampaignRecord (rec_with_budget "{""max_candidates"":-0}")) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma parse_record_impl_rejects_dup_key :
  parse_record_impl (mkCampaignRecord
    (rec_with_budget "{""max_candidates"":1,""max_candidates"":2}")) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma parse_record_impl_rejects_descending_keys :
  parse_record_impl (mkCampaignRecord
    (rec_with_budget "{""max_memory_bytes"":1,""max_candidates"":2}")) = None.
Proof. vm_compute. reflexivity. Qed.

(* the identity-only mini-form (no [completeness] / [recorded_results] /
   [resource_budget]) is REJECTED -- a full record is required. *)
Lemma parse_record_impl_rejects_identity_only :
  parse_record_impl (mkCampaignRecord
    ("{""audit_instance_id"":""ai-0001"",""campaign_id"":""cmp-1"",""context_digests"":{""inference_spec_digest"":"
     ++ CanonicalV1.d64_c ++ """,""model_artifact_digest"":""" ++ CanonicalV1.d64_a
     ++ """,""preprocessing_digest"":""" ++ CanonicalV1.d64_b ++ """},""manifest_digest"":"""
     ++ CanonicalV1.d64_d ++ """,""policy_hash"":""" ++ CanonicalV1.d64_a ++ """}"))
  = None.
Proof. vm_compute. reflexivity. Qed.

(* ================= context-descriptor equality ================= *)

Definition cd_eqb (a b : context_descriptor) : bool :=
  String.eqb (CanonicalV1.cd_model_artifact_digest a) (CanonicalV1.cd_model_artifact_digest b) &&
  String.eqb (CanonicalV1.cd_preprocessing_digest a) (CanonicalV1.cd_preprocessing_digest b) &&
  String.eqb (CanonicalV1.cd_inference_spec_digest a) (CanonicalV1.cd_inference_spec_digest b).

Lemma cd_eqb_true : forall a b, cd_eqb a b = true -> a = b.
Proof.
  intros [m1 p1 i1] [m2 p2 i2] H. unfold cd_eqb in H. cbn in H.
  apply andb_true_iff in H as [H12 H3]. apply andb_true_iff in H12 as [H1 H2].
  apply String.eqb_eq in H1, H2, H3. subst. reflexivity.
Qed.

Lemma cd_eqb_refl : forall a, cd_eqb a a = true.
Proof.
  intros [m p i]. unfold cd_eqb. cbn.
  rewrite !String.eqb_refl. reflexivity.
Qed.

Lemma cd_eqb_eq : forall a b, cd_eqb a b = true <-> a = b.
Proof.
  intros a b. split; [ apply cd_eqb_true |]. intro E; subst; apply cd_eqb_refl.
Qed.

(* ================= deterministic decoder-failure sentinels ================= *)

Definition sentinel_record_undecodable   : string := "!record_undecodable".
Definition sentinel_manifest_undecodable : string := "!manifest_undecodable".

Definition record_id_field_names : list string :=
  ["campaign_id"; "audit_instance_id"; "policy_hash"; "context_digests"; "manifest_digest"].

Lemma record_sentinels_distinct :
  sentinel_record_undecodable <> sentinel_manifest_undecodable /\
  (forall f, In f record_id_field_names ->
     f <> sentinel_record_undecodable /\ f <> sentinel_manifest_undecodable).
Proof.
  split; [ discriminate |].
  intros f Hin. cbn in Hin.
  repeat destruct Hin as [<- | Hin]; try (split; discriminate).
  destruct Hin.
Qed.

(* ================= the comparison ================= *)

Section Mismatch.

Variable parse_rec : campaign_record -> option campaign_record_view.
Variable parse_man : manifest -> option campaign_manifest_view.

Definition record_identity_mismatch_impl
  (r : campaign_record) (mc : manifest_commitment) (M : manifest) : option string :=
  match parse_rec r with
  | None => Some sentinel_record_undecodable
  | Some rv =>
      match parse_man M with
      | None => Some sentinel_manifest_undecodable
      | Some cm =>
          if String.eqb (crv_campaign_id rv) (cm_campaign_id cm) then
          if String.eqb (crv_audit_instance_id rv) (cm_audit_instance_id cm) then
          if String.eqb (crv_policy_hash rv) (cm_policy_hash cm) then
          if cd_eqb (crv_context_digests rv) (cm_context_digests cm) then
          if String.eqb (crv_manifest_digest rv) (commitment_digest mc) then None
          else Some "manifest_digest"
          else Some "context_digests"
          else Some "policy_hash"
          else Some "audit_instance_id"
          else Some "campaign_id"
      end
  end.

(* ----- None iff both decoders succeed and all five equalities hold ----- *)
Lemma record_identity_mismatch_impl_none_iff : forall r mc M,
  record_identity_mismatch_impl r mc M = None <->
  exists rv cm,
    parse_rec r = Some rv /\ parse_man M = Some cm /\
    crv_campaign_id rv       = cm_campaign_id cm /\
    crv_audit_instance_id rv = cm_audit_instance_id cm /\
    crv_policy_hash rv       = cm_policy_hash cm /\
    crv_context_digests rv   = cm_context_digests cm /\
    crv_manifest_digest rv   = commitment_digest mc.
Proof.
  intros r mc M. unfold record_identity_mismatch_impl. split.
  - destruct (parse_rec r) as [rv|] eqn:Er; [| discriminate].
    destruct (parse_man M) as [cm|] eqn:Em; [| discriminate].
    destruct (String.eqb (crv_campaign_id rv) (cm_campaign_id cm)) eqn:E1; [| discriminate].
    destruct (String.eqb (crv_audit_instance_id rv) (cm_audit_instance_id cm)) eqn:E2; [| discriminate].
    destruct (String.eqb (crv_policy_hash rv) (cm_policy_hash cm)) eqn:E3; [| discriminate].
    destruct (cd_eqb (crv_context_digests rv) (cm_context_digests cm)) eqn:E4; [| discriminate].
    destruct (String.eqb (crv_manifest_digest rv) (commitment_digest mc)) eqn:E5; [| discriminate].
    intros _. exists rv, cm.
    apply String.eqb_eq in E1, E2, E3, E5. apply cd_eqb_true in E4.
    repeat split; assumption.
  - intros (rv & cm & Hr & Hm & H1 & H2 & H3 & H4 & H5).
    rewrite Hr, Hm.
    rewrite (proj2 (String.eqb_eq _ _) H1), (proj2 (String.eqb_eq _ _) H2),
            (proj2 (String.eqb_eq _ _) H3), (proj2 (cd_eqb_eq _ _) H4),
            (proj2 (String.eqb_eq _ _) H5).
    reflexivity.
Qed.

(* ----- for every ordinary [Some field]: preceding fields agree, named differs ----- *)

Lemma record_identity_mismatch_impl_some_campaign_id : forall r mc M,
  record_identity_mismatch_impl r mc M = Some "campaign_id" ->
  exists rv cm,
    parse_rec r = Some rv /\ parse_man M = Some cm /\
    crv_campaign_id rv <> cm_campaign_id cm.
Proof.
  intros r mc M H. unfold record_identity_mismatch_impl in H.
  destruct (parse_rec r) as [rv|] eqn:Er; [| discriminate].
  destruct (parse_man M) as [cm|] eqn:Em; [| discriminate].
  destruct (String.eqb (crv_campaign_id rv) (cm_campaign_id cm)) eqn:E1.
  - exfalso.
    destruct (String.eqb (crv_audit_instance_id rv) (cm_audit_instance_id cm)),
             (String.eqb (crv_policy_hash rv) (cm_policy_hash cm)),
             (cd_eqb (crv_context_digests rv) (cm_context_digests cm)),
             (String.eqb (crv_manifest_digest rv) (commitment_digest mc)); discriminate.
  - exists rv, cm. apply String.eqb_neq in E1. repeat split; assumption.
Qed.

Lemma record_identity_mismatch_impl_some_audit_instance_id : forall r mc M,
  record_identity_mismatch_impl r mc M = Some "audit_instance_id" ->
  exists rv cm,
    parse_rec r = Some rv /\ parse_man M = Some cm /\
    crv_campaign_id rv = cm_campaign_id cm /\
    crv_audit_instance_id rv <> cm_audit_instance_id cm.
Proof.
  intros r mc M H. unfold record_identity_mismatch_impl in H.
  destruct (parse_rec r) as [rv|] eqn:Er; [| discriminate].
  destruct (parse_man M) as [cm|] eqn:Em; [| discriminate].
  destruct (String.eqb (crv_campaign_id rv) (cm_campaign_id cm)) eqn:E1; [| discriminate].
  destruct (String.eqb (crv_audit_instance_id rv) (cm_audit_instance_id cm)) eqn:E2.
  - exfalso.
    destruct (String.eqb (crv_policy_hash rv) (cm_policy_hash cm)),
             (cd_eqb (crv_context_digests rv) (cm_context_digests cm)),
             (String.eqb (crv_manifest_digest rv) (commitment_digest mc)); discriminate.
  - exists rv, cm. apply String.eqb_eq in E1. apply String.eqb_neq in E2.
    repeat split; assumption.
Qed.

Lemma record_identity_mismatch_impl_some_policy_hash : forall r mc M,
  record_identity_mismatch_impl r mc M = Some "policy_hash" ->
  exists rv cm,
    parse_rec r = Some rv /\ parse_man M = Some cm /\
    crv_campaign_id rv = cm_campaign_id cm /\
    crv_audit_instance_id rv = cm_audit_instance_id cm /\
    crv_policy_hash rv <> cm_policy_hash cm.
Proof.
  intros r mc M H. unfold record_identity_mismatch_impl in H.
  destruct (parse_rec r) as [rv|] eqn:Er; [| discriminate].
  destruct (parse_man M) as [cm|] eqn:Em; [| discriminate].
  destruct (String.eqb (crv_campaign_id rv) (cm_campaign_id cm)) eqn:E1; [| discriminate].
  destruct (String.eqb (crv_audit_instance_id rv) (cm_audit_instance_id cm)) eqn:E2; [| discriminate].
  destruct (String.eqb (crv_policy_hash rv) (cm_policy_hash cm)) eqn:E3.
  - exfalso.
    destruct (cd_eqb (crv_context_digests rv) (cm_context_digests cm)),
             (String.eqb (crv_manifest_digest rv) (commitment_digest mc)); discriminate.
  - exists rv, cm. apply String.eqb_eq in E1, E2. apply String.eqb_neq in E3.
    repeat split; assumption.
Qed.

Lemma record_identity_mismatch_impl_some_context_digests : forall r mc M,
  record_identity_mismatch_impl r mc M = Some "context_digests" ->
  exists rv cm,
    parse_rec r = Some rv /\ parse_man M = Some cm /\
    crv_campaign_id rv = cm_campaign_id cm /\
    crv_audit_instance_id rv = cm_audit_instance_id cm /\
    crv_policy_hash rv = cm_policy_hash cm /\
    crv_context_digests rv <> cm_context_digests cm.
Proof.
  intros r mc M H. unfold record_identity_mismatch_impl in H.
  destruct (parse_rec r) as [rv|] eqn:Er; [| discriminate].
  destruct (parse_man M) as [cm|] eqn:Em; [| discriminate].
  destruct (String.eqb (crv_campaign_id rv) (cm_campaign_id cm)) eqn:E1; [| discriminate].
  destruct (String.eqb (crv_audit_instance_id rv) (cm_audit_instance_id cm)) eqn:E2; [| discriminate].
  destruct (String.eqb (crv_policy_hash rv) (cm_policy_hash cm)) eqn:E3; [| discriminate].
  destruct (cd_eqb (crv_context_digests rv) (cm_context_digests cm)) eqn:E4.
  - exfalso.
    destruct (String.eqb (crv_manifest_digest rv) (commitment_digest mc)); discriminate.
  - exists rv, cm. apply String.eqb_eq in E1, E2, E3.
    assert (Hne : crv_context_digests rv <> cm_context_digests cm).
    { intro Hc. rewrite (proj2 (cd_eqb_eq _ _) Hc) in E4. discriminate. }
    repeat split; assumption.
Qed.

Lemma record_identity_mismatch_impl_some_manifest_digest : forall r mc M,
  record_identity_mismatch_impl r mc M = Some "manifest_digest" ->
  exists rv cm,
    parse_rec r = Some rv /\ parse_man M = Some cm /\
    crv_campaign_id rv = cm_campaign_id cm /\
    crv_audit_instance_id rv = cm_audit_instance_id cm /\
    crv_policy_hash rv = cm_policy_hash cm /\
    crv_context_digests rv = cm_context_digests cm /\
    crv_manifest_digest rv <> commitment_digest mc.
Proof.
  intros r mc M H. unfold record_identity_mismatch_impl in H.
  destruct (parse_rec r) as [rv|] eqn:Er; [| discriminate].
  destruct (parse_man M) as [cm|] eqn:Em; [| discriminate].
  destruct (String.eqb (crv_campaign_id rv) (cm_campaign_id cm)) eqn:E1; [| discriminate].
  destruct (String.eqb (crv_audit_instance_id rv) (cm_audit_instance_id cm)) eqn:E2; [| discriminate].
  destruct (String.eqb (crv_policy_hash rv) (cm_policy_hash cm)) eqn:E3; [| discriminate].
  destruct (cd_eqb (crv_context_digests rv) (cm_context_digests cm)) eqn:E4; [| discriminate].
  destruct (String.eqb (crv_manifest_digest rv) (commitment_digest mc)) eqn:E5.
  - discriminate.
  - exists rv, cm. apply String.eqb_eq in E1, E2, E3. apply cd_eqb_true in E4.
    apply String.eqb_neq in E5. repeat split; assumption.
Qed.

(* ----- decoder-failure sentinels ----- *)

Lemma record_identity_mismatch_impl_record_undecodable_iff : forall r mc M,
  record_identity_mismatch_impl r mc M = Some sentinel_record_undecodable <->
  parse_rec r = None.
Proof.
  intros r mc M. unfold record_identity_mismatch_impl. split.
  - destruct (parse_rec r) as [rv|] eqn:Er; [| reflexivity].
    destruct (parse_man M) as [cm|] eqn:Em; [| discriminate].
    destruct (String.eqb (crv_campaign_id rv) (cm_campaign_id cm)),
             (String.eqb (crv_audit_instance_id rv) (cm_audit_instance_id cm)),
             (String.eqb (crv_policy_hash rv) (cm_policy_hash cm)),
             (cd_eqb (crv_context_digests rv) (cm_context_digests cm)),
             (String.eqb (crv_manifest_digest rv) (commitment_digest mc)); discriminate.
  - intro Hn. rewrite Hn. reflexivity.
Qed.

Lemma record_identity_mismatch_impl_manifest_undecodable_iff : forall r mc M,
  record_identity_mismatch_impl r mc M = Some sentinel_manifest_undecodable <->
  (exists rv, parse_rec r = Some rv) /\ parse_man M = None.
Proof.
  intros r mc M. unfold record_identity_mismatch_impl. split.
  - destruct (parse_rec r) as [rv|] eqn:Er; [| discriminate].
    destruct (parse_man M) as [cm|] eqn:Em.
    + destruct (String.eqb (crv_campaign_id rv) (cm_campaign_id cm)),
               (String.eqb (crv_audit_instance_id rv) (cm_audit_instance_id cm)),
               (String.eqb (crv_policy_hash rv) (cm_policy_hash cm)),
               (cd_eqb (crv_context_digests rv) (cm_context_digests cm)),
               (String.eqb (crv_manifest_digest rv) (commitment_digest mc)); discriminate.
    + intros _. split; [ exists rv; reflexivity | reflexivity ].
  - intros ((rv & Hr) & Hm). rewrite Hr, Hm. reflexivity.
Qed.

End Mismatch.
