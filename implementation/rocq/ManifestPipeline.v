(** Integrated concrete validation operations: the AUDIT_POLICY 2.4.1
    authentication ops AND the manifest matchers, over ONE shared manifest type
    ([CanonicalV1.campaign_manifest_view]) and ONE shared concrete decoder
    ([ManifestAuthentication.parse_manifest_impl]).

    [validate_campaign_pipeline] : one [validate_campaign] success yields THREE
    facts --

      - [manifest_authenticated_by_impl … (ti_config ti) …]   (2.4.1), and
      - [ti_policy ti = p_committed]                          (policy binding), and
      - [pipeline_commits (ti_config ti) (authenticated_commitment ac)
           committed_descriptor]                              (manifest -> descriptor,
                                                               in the shared
                                                               context_descriptor
                                                               type O1/O2/O3 use)

    with no opaque [parse_manifest] and no opaque manifest-match contract.
    The remaining premises are the explicitly-named F.3 residuals
    ([sha256_hex], [ed25519_verify], [ed25519_pubkey_valid], retrieval
    integrity).

    [op_ledger_mismatch] is now concrete too
    ([ManifestLedger.ledger_mismatch_impl digest_eqb parse_manifest_impl]).
    [validate_campaign_ledger_agrees] is a SEPARATE theorem (not folded into
    [validate_campaign_pipeline]): one [validate_campaign] success over
    [pipeline_ops] gives [parse_manifest_impl (ti_manifest ti) = Some v] with
    [cm_submission_digests v = map submission_digest (ti_submissions ti)]
    (VERDICT_SEMANTICS.md 5 step 7 -- element-wise, ordered, multiplicity kept).

    [op_manifest_audit_matches] is likewise concrete
    ([ManifestAudit.manifest_audit_matches_impl parse_manifest_impl
      policy_audit_instance_id_of]) with a SEPARATE theorem
    [validate_campaign_audit_agrees]: success gives
    [parse_manifest_impl (ti_manifest ti) = Some v] with
    [cm_audit_instance_id v = committed_audit_instance_id]
    (VERDICT_SEMANTICS.md 5 step 5).  Residual: [policy_audit_instance_id_of]
    returning the load-validated policy's true audit id (F.3 until the policy
    parser is concrete).

    [op_record_identity_mismatch] is concrete
    ([CampaignRecord.record_identity_mismatch_impl parse_record_impl
      parse_manifest_impl], step 8) with a SEPARATE theorem
    [validate_campaign_record_agrees]: success gives the record and manifest
    decoding and their five step-8 identity fields agreeing, the last against
    [commitment_digest (authenticated_commitment ac)].

    [op_record_crosscheck] is concrete
    ([RecordCrosscheck.record_crosscheck_impl parse_record_full_impl]).  Its
    output is advisory only: [pipeline_verdict_indep_of_crosscheck] shows the
    campaign verdict is unchanged if [op_record_crosscheck] is replaced by any
    other function (VERDICT_SEMANTICS.md 6.5 -- [record_findings] is not read by
    [decide]).

    [op_completeness_wellformed] is concrete
    ([CompletenessWellformed.op_completeness_wellformed_impl], step 9 -- the
    LAST validate_campaign guard) with a SEPARATE theorem
    [validate_campaign_completeness_agrees]: success gives the trusted input's
    completeness status well-formed, per
    [CompletenessWellformed.op_completeness_wellformed_impl_true_iff] (now
    stated over the INDEPENDENT [CompletenessWellformed.completeness_status_wf]
    relation, reviewer revision 2).  This is a pure structural check on the
    already-typed [completeness_status] -- no wire decode, and no change to
    [validate_campaign]'s precedence; it is UNRELATED to
    [Orchestration.valid_completeness_certificate_v0] (the semantic
    EXACT-branch check, untouched, still dead code in v0).

    [validate_campaign_completeness_bound_to_record] additionally binds the
    checked value to `ti.rec.completeness` (VERDICT_SEMANTICS.md 5 step 9 reads
    the RECORD, not an independently-supplied field) via the explicit F.3
    premise [record_completeness_load_validated], exactly like
    [ManifestMatching.policy_digest_load_validated] -- reviewer revision 2,
    blocker 2. *)

From Coq Require Import Bool List String.
From PCFW Require Import Orchestration CanonicalV1 ValidationBinding
  ManifestMatching ManifestAuthentication ManifestLedger ManifestAudit
  CampaignRecord RecordCrosscheck CompletenessWellformed TranscriptDigest.
Import ListNotations.

Section Pipeline.

Variable sha256_hex : bytes -> digest.
Variable ed25519_verify : bytes -> bytes -> bytes -> bool.
Variable ed25519_pubkey_valid : bytes -> bool.
Variable digest_eqb : digest -> digest -> bool.
Hypothesis digest_eqb_true : forall a b, digest_eqb a b = true -> a = b.
Hypothesis digest_eqb_refl : forall a, digest_eqb a a = true.

Variable p_committed : policy.
Variable committed_descriptor : context_descriptor.
Variable policy_payload_digest_of : policy -> digest.
Hypothesis policy_payload_digest_injective :
  forall p q, policy_payload_digest_of p = policy_payload_digest_of q -> p = q.
Variable policy_context_of : policy -> context_descriptor.
Variable policy_audit_instance_id_of : policy -> string.
Variable committed_audit_instance_id : string.

(* ----- the integrated ops ----- *)

Definition pipeline_ops (base : primitive_ops) : primitive_ops :=
  let a := concrete_auth_ops sha256_hex ed25519_verify ed25519_pubkey_valid base in
  mkPrimitiveOps
    (op_parse_commitment a)
    (op_signer_authorised a)
    (op_signature_valid a)
    (ManifestMatching.manifest_policy_matches_impl digest_eqb parse_manifest_impl)
    (ManifestAudit.manifest_audit_matches_impl parse_manifest_impl
       policy_audit_instance_id_of)
    (ManifestMatching.manifest_context_matches_impl digest_eqb parse_manifest_impl
       policy_context_of)
    (ManifestLedger.ledger_mismatch_impl digest_eqb parse_manifest_impl)
    (fun r mc M (_ : trusted_inputs) =>
       CampaignRecord.record_identity_mismatch_impl
         parse_record_impl parse_manifest_impl r mc M)
    CompletenessWellformed.op_completeness_wellformed_impl
    (op_stage1_check a)
    (op_preflight a)
    (op_eval_o3 a)
    (op_stage2_check a)
    (RecordCrosscheck.record_crosscheck_impl parse_record_full_impl)
    (op_transcript_digest a).

Lemma pipeline_ops_signer : forall base,
  op_signer_authorised (pipeline_ops base) = signer_authorised_impl.
Proof. reflexivity. Qed.

Lemma pipeline_ops_signature : forall base,
  op_signature_valid (pipeline_ops base) = signature_valid_impl sha256_hex ed25519_verify ed25519_pubkey_valid.
Proof. reflexivity. Qed.

Lemma pipeline_ops_policy_match : forall base,
  op_manifest_policy_matches (pipeline_ops base)
  = ManifestMatching.manifest_policy_matches_impl digest_eqb parse_manifest_impl.
Proof. reflexivity. Qed.

Lemma pipeline_ops_context_match : forall base,
  op_manifest_context_matches (pipeline_ops base)
  = ManifestMatching.manifest_context_matches_impl digest_eqb parse_manifest_impl
      policy_context_of.
Proof. reflexivity. Qed.

Lemma pipeline_ops_ledger : forall base,
  op_ledger_mismatch (pipeline_ops base)
  = ManifestLedger.ledger_mismatch_impl digest_eqb parse_manifest_impl.
Proof. reflexivity. Qed.

Lemma pipeline_ops_audit_match : forall base,
  op_manifest_audit_matches (pipeline_ops base)
  = ManifestAudit.manifest_audit_matches_impl parse_manifest_impl
      policy_audit_instance_id_of.
Proof. reflexivity. Qed.

Lemma pipeline_ops_record : forall base r mc M ti,
  op_record_identity_mismatch (pipeline_ops base) r mc M ti
  = CampaignRecord.record_identity_mismatch_impl
      parse_record_impl parse_manifest_impl r mc M.
Proof. reflexivity. Qed.

(* the authenticated manifest commits to descriptor [d] -- in the SHARED
   [context_descriptor] type, i.e. exactly the type O1/O2/O3 consume. *)
Definition pipeline_commits (cfg : verifier_config) (mc : manifest_commitment)
  (d : context_descriptor) : Prop :=
  exists M cm,
    manifest_authenticated_by_impl sha256_hex ed25519_verify ed25519_pubkey_valid cfg mc M /\
    parse_manifest_impl M = Some cm /\
    cm_context_digests cm = d.

(* ----- F.3 residuals, about the fixed audit objects ----- *)

Variable audit_manifest : manifest.
Variable audit_view : campaign_manifest_view.
Hypothesis audit_manifest_parses :
  parse_manifest_impl audit_manifest = Some audit_view.
Hypothesis audit_policy_hash_committed :
  cm_policy_hash audit_view = policy_payload_digest_of p_committed.
(* AUDIT_POLICY 2.4 step 3: the committed policy payload embeds the committed
   context digests. *)
Hypothesis committed_policy_context :
  policy_context_of p_committed = committed_descriptor.
(* AUDIT_POLICY 2.4 step 3 / 2.5: the committed policy payload carries the
   committed audit_instance_id.  Residual: [policy_audit_instance_id_of] returns
   the load-validated policy's true audit_instance_id -- an F.3 fact until the
   policy representation / parser is concrete. *)
Hypothesis committed_policy_audit_id :
  policy_audit_instance_id_of p_committed = committed_audit_instance_id.

Variable base : primitive_ops.
Hypothesis validated_manifest_is_audit :
  forall ti ac l0,
    validate_campaign (pipeline_ops base) ti = ValidCampaign ac l0 ->
    ti_manifest ti = audit_manifest.

(* ----- capstone ----- *)

Theorem validate_campaign_pipeline :
  forall ti ac l0,
    ManifestMatching.policy_digest_load_validated policy_payload_digest_of ti ->
    validate_campaign (pipeline_ops base) ti = ValidCampaign ac l0 ->
    manifest_authenticated_by_impl sha256_hex ed25519_verify ed25519_pubkey_valid (ti_config ti)
      (authenticated_commitment ac) (authenticated_manifest ac)
    /\ ti_policy ti = p_committed
    /\ pipeline_commits (ti_config ti) (authenticated_commitment ac)
         committed_descriptor.
Proof.
  intros ti ac l0 Hload H.
  assert (Hauth :
    manifest_authenticated_by_impl sha256_hex ed25519_verify ed25519_pubkey_valid (ti_config ti)
      (authenticated_commitment ac) (authenticated_manifest ac))
    by exact (validate_campaign_authenticates_ops sha256_hex ed25519_verify ed25519_pubkey_valid
               (pipeline_ops base) ti ac l0
               (pipeline_ops_signer base) (pipeline_ops_signature base) H).
  assert (Hpolicy : ti_policy ti = p_committed)
    by exact (ManifestMatching.validate_campaign_concrete_binds_policy
               digest_eqb_true p_committed policy_payload_digest_injective
               audit_manifest_parses audit_policy_hash_committed
               (pipeline_ops base) (pipeline_ops_policy_match base)
               validated_manifest_is_audit Hload H).
  split; [ exact Hauth |]. split; [ exact Hpolicy |].
  (* the third conjunct: the context matcher fired => the manifest's context
     digests equal policy_context_of (ti_policy ti) = committed_descriptor *)
  destruct (validate_campaign_valid_guards (pipeline_ops base) ti H)
    as (mc & _ & _ & _ & _ & Hcm & Hac).
  rewrite (pipeline_ops_context_match base) in Hcm.
  pose proof (validated_manifest_is_audit ti ac l0 H) as Hman.
  unfold ManifestMatching.manifest_context_matches_impl in Hcm.
  rewrite Hman, audit_manifest_parses in Hcm.
  apply (ManifestMatching.descriptor_eqb_true digest_eqb digest_eqb_true) in Hcm.
  assert (Ham2 : authenticated_manifest ac = ti_manifest ti)
    by (rewrite Hac; reflexivity).
  exists (ti_manifest ti), audit_view.
  rewrite Ham2 in Hauth.
  split; [ exact Hauth |].
  split; [ rewrite Hman; exact audit_manifest_parses |].
  rewrite Hcm, Hpolicy. exact committed_policy_context.
Qed.

(* ----- ledger binding (VERDICT_SEMANTICS.md 5 step 7), a separate fact -----

   A successful validate_campaign over pipeline_ops means the concrete
   ledger_mismatch_impl returned None, i.e. the manifest decodes and its
   submission-digest list equals [map submission_digest (ti_submissions ti)]
   element-wise, ordered, multiplicity kept. *)
Theorem validate_campaign_ledger_agrees :
  forall ti ac l0,
    validate_campaign (pipeline_ops base) ti = ValidCampaign ac l0 ->
    exists v,
      parse_manifest_impl (ti_manifest ti) = Some v /\
      cm_submission_digests v = map submission_digest (ti_submissions ti).
Proof.
  intros ti ac l0 H.
  pose proof (validate_campaign_valid_ledger (pipeline_ops base) ti H) as Hlm.
  rewrite (pipeline_ops_ledger base) in Hlm.
  apply (ManifestLedger.ledger_mismatch_impl_none_iff
           digest_eqb digest_eqb_true digest_eqb_refl
           parse_manifest_impl (ti_manifest ti) (ti_submissions ti)) in Hlm.
  exact Hlm.
Qed.

(* ----- audit-instance binding (VERDICT_SEMANTICS.md 5 step 5), a separate fact -----

   A successful validate_campaign over pipeline_ops means the concrete
   manifest_audit_matches_impl returned true: the manifest decodes and its
   [cm_audit_instance_id] equals the committed policy's audit_instance_id,
   which -- via the policy binding and [committed_policy_audit_id] -- is the
   fixed [committed_audit_instance_id].  [validate_campaign_pipeline] keeps its
   three conclusions. *)
Theorem validate_campaign_audit_agrees :
  forall ti ac l0,
    ManifestMatching.policy_digest_load_validated policy_payload_digest_of ti ->
    validate_campaign (pipeline_ops base) ti = ValidCampaign ac l0 ->
    exists v,
      parse_manifest_impl (ti_manifest ti) = Some v /\
      cm_audit_instance_id v = committed_audit_instance_id.
Proof.
  intros ti ac l0 Hload H.
  pose proof (validate_campaign_valid_audit (pipeline_ops base) ti H) as Hau.
  rewrite (pipeline_ops_audit_match base) in Hau.
  apply (ManifestAudit.manifest_audit_matches_impl_true_iff
           parse_manifest_impl policy_audit_instance_id_of (ti_manifest ti) ti) in Hau.
  destruct Hau as (v & Hpar & Hid).
  assert (Hpolicy : ti_policy ti = p_committed)
    by exact (ManifestMatching.validate_campaign_concrete_binds_policy
               digest_eqb_true p_committed policy_payload_digest_injective
               audit_manifest_parses audit_policy_hash_committed
               (pipeline_ops base) (pipeline_ops_policy_match base)
               validated_manifest_is_audit Hload H).
  exists v. split; [ exact Hpar |].
  rewrite Hid, Hpolicy. exact committed_policy_audit_id.
Qed.

(* ----- record-identity binding (VERDICT_SEMANTICS.md 5 step 8), a separate fact -----

   A successful validate_campaign over pipeline_ops means the concrete
   record_identity_mismatch_impl returned None: the record and the manifest both
   decode, their campaign_id / audit_instance_id / policy_hash / context_digests
   agree, and the record's manifest_digest equals the parsed commitment digest.
   [validate_campaign_pipeline] keeps its three conclusions. *)
Theorem validate_campaign_record_agrees :
  forall ti ac l0,
    validate_campaign (pipeline_ops base) ti = ValidCampaign ac l0 ->
    exists rv cm,
      parse_record_impl (ti_record ti) = Some rv /\
      parse_manifest_impl (ti_manifest ti) = Some cm /\
      crv_campaign_id rv       = cm_campaign_id cm /\
      crv_audit_instance_id rv = cm_audit_instance_id cm /\
      crv_policy_hash rv       = cm_policy_hash cm /\
      crv_context_digests rv   = cm_context_digests cm /\
      crv_manifest_digest rv   = commitment_digest (authenticated_commitment ac).
Proof.
  intros ti ac l0 H.
  destruct (validate_campaign_valid_record (pipeline_ops base) ti H)
    as (mc & Hpc & Hrim).
  rewrite (pipeline_ops_record base (ti_record ti) mc (ti_manifest ti) ti) in Hrim.
  apply (CampaignRecord.record_identity_mismatch_impl_none_iff
           parse_record_impl parse_manifest_impl (ti_record ti) mc (ti_manifest ti))
    in Hrim.
  destruct Hrim as (rv & cm & Hr & Hm & H1 & H2 & H3 & H4 & H5).
  destruct (validate_campaign_valid_guards (pipeline_ops base) ti H)
    as (mc' & Hpc' & _ & _ & _ & _ & Hac).
  assert (Hcom : authenticated_commitment ac = mc).
  { rewrite Hac. unfold authenticated_of. cbn. congruence. }
  exists rv, cm. rewrite Hcom.
  repeat split; assumption.
Qed.

(* ----- completeness well-formedness (VERDICT_SEMANTICS.md 5 step 9), a separate
   fact -----

   A successful validate_campaign over pipeline_ops means the concrete
   op_completeness_wellformed_impl returned true on the trusted input's
   completeness status.  [validate_campaign_pipeline] keeps its three
   conclusions. *)
Lemma pipeline_ops_completeness : forall base,
  op_completeness_wellformed (pipeline_ops base)
  = CompletenessWellformed.op_completeness_wellformed_impl.
Proof. reflexivity. Qed.

Theorem validate_campaign_completeness_agrees :
  forall ti ac l0,
    validate_campaign (pipeline_ops base) ti = ValidCampaign ac l0 ->
    CompletenessWellformed.op_completeness_wellformed_impl (ti_completeness ti) = true.
Proof.
  intros ti ac l0 H.
  pose proof (validate_campaign_valid_completeness (pipeline_ops base) ti H) as Hcw.
  rewrite (pipeline_ops_completeness base) in Hcw. exact Hcw.
Qed.

(* Boolean-disjunction corollary (supporting): the trusted input's completeness
   status is Unknown, Incomplete, or a Complete certificate whose scheme and
   body Booleans both return true. *)
Theorem validate_campaign_completeness_agrees_bool :
  forall ti ac l0,
    validate_campaign (pipeline_ops base) ti = ValidCampaign ac l0 ->
    ti_completeness ti = CompletenessUnknown \/
    ti_completeness ti = CompletenessIncomplete \/
    exists c, ti_completeness ti = CompletenessComplete c /\
      CompletenessWellformed.wellformed_scheme (completeness_scheme c) = true /\
      CompletenessWellformed.wellformed_body (completeness_body c) = true.
Proof.
  intros ti ac l0 H.
  apply CompletenessWellformed.op_completeness_wellformed_impl_true_iff_bool.
  exact (validate_campaign_completeness_agrees ti ac l0 H).
Qed.

(* structured corollary, over the INDEPENDENT specification-level relation
   (CompletenessWellformed.completeness_status_wf): the trusted input's
   completeness status is Unknown, Incomplete, or a Complete certificate whose
   scheme is non-empty and whose body is exactly one ASCII-wire canonical
   value. *)
Theorem validate_campaign_completeness_agrees_structured :
  forall ti ac l0,
    validate_campaign (pipeline_ops base) ti = ValidCampaign ac l0 ->
    CompletenessWellformed.completeness_status_wf (ti_completeness ti).
Proof.
  intros ti ac l0 H.
  apply CompletenessWellformed.op_completeness_wellformed_impl_true_iff.
  exact (validate_campaign_completeness_agrees ti ac l0 H).
Qed.

(* ----- binding the checked value to `ti.rec.completeness` (reviewer HOLD,
   blocker 2) -----

   VERDICT_SEMANTICS.md 5 step 9 reads `ti.rec.completeness`, not an
   independently-supplied field.  No completeness-status wire decoder exists
   yet -- `CampaignRecord.skip_value` only SYNTACTICALLY consumes the record's
   `completeness` field (see its header), never interprets it.

   [record_completeness_of] stands for "the value a completeness decoder would
   recover from a campaign record" (an abstract denotation, like
   `ManifestMatching.policy_context_of`).  [record_completeness_load_validated]
   is a PREDICATE ON ONE INPUT -- exactly
   `ManifestMatching.policy_digest_load_validated ti`, a `Definition`, NOT a
   blanket Section `Hypothesis` -- because a `forall ti, record_completeness_of
   (ti_record ti) = ti_completeness ti` premise is UNSATISFIABLE: two
   `trusted_inputs` can share `ti_record` while differing in `ti_completeness`
   (e.g. `Unknown` vs `Incomplete`), forcing those to be equal (reviewer HOLD
   on r2, blocker 2).  Each theorem below therefore takes
   `record_completeness_load_validated ti` as an explicit premise, about the
   one `ti` in play, matching every other per-input F.3 premise in this file.
   A concrete decoder (PREFERRED, per the reviewer) is future work -- see
   `PHASE_1_COMPLETENESS_WELLFORMED.md` 5. *)
Variable record_completeness_of : campaign_record -> completeness_status.
Definition record_completeness_load_validated (ti : trusted_inputs) : Prop :=
  record_completeness_of (ti_record ti) = ti_completeness ti.

Theorem validate_campaign_completeness_bound_to_record :
  forall ti ac l0,
    record_completeness_load_validated ti ->
    validate_campaign (pipeline_ops base) ti = ValidCampaign ac l0 ->
    CompletenessWellformed.op_completeness_wellformed_impl
      (record_completeness_of (ti_record ti)) = true.
Proof.
  intros ti ac l0 Hload H.
  unfold record_completeness_load_validated in Hload.
  rewrite Hload.
  exact (validate_campaign_completeness_agrees ti ac l0 H).
Qed.

Theorem validate_campaign_completeness_bound_to_record_structured :
  forall ti ac l0,
    record_completeness_load_validated ti ->
    validate_campaign (pipeline_ops base) ti = ValidCampaign ac l0 ->
    CompletenessWellformed.completeness_status_wf (record_completeness_of (ti_record ti)).
Proof.
  intros ti ac l0 Hload H.
  apply CompletenessWellformed.op_completeness_wellformed_impl_true_iff.
  exact (validate_campaign_completeness_bound_to_record ti ac l0 Hload H).
Qed.

(* ----- op_record_crosscheck: concrete, and advisory-only ----- *)

Lemma pipeline_ops_crosscheck : forall base,
  op_record_crosscheck (pipeline_ops base)
  = RecordCrosscheck.record_crosscheck_impl parse_record_full_impl.
Proof. reflexivity. Qed.

(* the campaign verdict does not depend on op_record_crosscheck: replacing the
   pipeline's crosscheck by ANY function [g] leaves the verdict unchanged.
   (VERDICT_SEMANTICS.md 6.5 -- record_findings are advisory, never read by
   decide.) *)
Theorem pipeline_verdict_indep_of_crosscheck :
  forall base g ti vr src,
    verdict_of (assess_validated
      (RecordCrosscheck.set_crosscheck (pipeline_ops base) g) ti vr src)
    = verdict_of (assess_validated (pipeline_ops base) ti vr src).
Proof.
  intros. apply RecordCrosscheck.assess_validated_verdict_indep_crosscheck.
Qed.

(* ----- op_transcript_digest: a contract-bound primitive (the hook itself is
   passed through unchanged; it is not made concrete here), and the pipeline
   preserves any baseline agreement premise ----- *)

Lemma pipeline_ops_transcript_digest : forall base,
  op_transcript_digest (pipeline_ops base) = op_transcript_digest base.
Proof. reflexivity. Qed.

Theorem pipeline_transcript_digest_agrees :
  forall (transcript_digest_v1 : exec_transcript -> digest) tr,
    TranscriptDigest.transcript_digest_agrees transcript_digest_v1 base tr ->
    TranscriptDigest.transcript_digest_agrees transcript_digest_v1
      (pipeline_ops base) tr.
Proof.
  intros transcript_digest_v1 tr Hagree.
  unfold TranscriptDigest.transcript_digest_agrees in *.
  rewrite (pipeline_ops_transcript_digest base). exact Hagree.
Qed.

End Pipeline.
