(** Concrete [op_manifest_policy_matches] / [op_manifest_context_matches], and a
    concrete replacement for the two soundness contracts [ValidationBinding.v]
    assumed abstractly.

    Revision (2026-09-07), addressing three reviewer defects in the first cut:

    1. digest truthfulness was [forall ti, ti_policy_digest ti =
       policy_payload_digest_of (ti_policy ti)] -- inconsistent, since two
       records may share a policy but carry different digest strings.  It is now
       [policy_digest_load_validated ti], a predicate on ONE input, supplied as
       an explicit premise (the AUDIT_POLICY 2.3 load-validation postcondition
       for that input).

    2. authentication was [forall mc M cm, <auth> -> <parse> -> cm_policy_hash cm
       = committed_policy_digest] -- it forced EVERY authenticated manifest to
       carry this audit's policy.  The audit's authenticated commitment / manifest
       / decoded view are now FIXED section objects ([audit_commitment],
       [audit_manifest], [audit_view]); the hypotheses speak only about them; and
       [validated_commitment_is_audit] / [validated_manifest_is_audit] connect a
       *successful [validate_campaign]* to those fixed objects (the F.3
       retrieval-integrity + Ed25519-unforgeability residual, stated once).

    3. the [discharges_*] lemmas were "contract-shaped modulo extra premises" and
       did not instantiate [ValidationBinding]'s contracts, whose live/offline
       replay-policy consumers were unchanged.  They are replaced by
       [assess_validated_{live,offline}_concrete] -- the SAME statements as
       [ValidationBinding.assess_validated_*_uses_committed_policy], proved from
       the corrected capstone with no opaque contract (plus the per-input
       load-validation premise).

    [manifest_matching_core_hyps_consistent] exhibits concrete witnesses
    satisfying the SEVEN core non-[ops] facts simultaneously (digest_eqb_true,
    policy_payload_digest_injective, audit_authenticated, audit_manifest_parses,
    audit_policy_hash_committed, committed_policy_context, and
    policy_digest_load_validated for a concrete input) -- so those hypotheses are
    not mutually contradictory (defect 1: the old [forall ti] truthfulness is
    gone).  It does NOT exhibit an [ops], the four [ops]-hypotheses, or a
    successful [validate_campaign]; it is a consistency result, not full
    non-vacuous satisfiability of the capstone premises.

    Still F.3-external (each narrower than the contract it helps discharge):
    - [parse_manifest] : the campaign-manifest wire decoder;
    - [manifest_authenticated_by] : the AUDIT_POLICY 2.4.1 [authenticate_manifest]
      predicate (mc.digest = digest_v1(to_cv M) and Ed25519 verify) -- named, not
      implemented;
    - [audit_authenticated] / [audit_manifest_parses] / [audit_policy_hash_committed]
      / [committed_policy_context] : the audit's published commitment authenticates
      its manifest, which decodes to a view whose policy hash is the committed
      policy's digest and whose context digests the committed policy also embeds
      (AUDIT_POLICY 2.4 steps 3 and 6);
    - [validated_commitment_is_audit] / [validated_manifest_is_audit] : a
      successful validation is a validation OF THIS AUDIT (retrieval integrity +
      unforgeability);
    - [policy_payload_digest_injective] : digest_v1 collision-freedom on policy
      payloads;
    - [policy_digest_load_validated ti] : supplied per validated input. *)

From Coq Require Import Bool List String.
From PCFW Require Import Orchestration ContextResolution ValidationBinding CanonicalV1.
Import ListNotations.

Set Implicit Arguments.

(* the [campaign_manifest] fields (AUDIT_POLICY 2.1 / 2.4 step 6) this unit reads;
   [parse_manifest] is the F.3 decoder from the wire [manifest]. *)
(* THE shared validation type (also produced by ManifestAuthentication.parse_manifest_impl). *)
Notation campaign_manifest_view := CanonicalV1.campaign_manifest_view.
Notation cd := CanonicalV1.context_descriptor.

Section MM.

Variable digest_eqb : digest -> digest -> bool.
Hypothesis digest_eqb_true : forall a b, digest_eqb a b = true -> a = b.

Definition descriptor_eqb (d1 d2 : cd) : bool :=
  digest_eqb (CanonicalV1.cd_model_artifact_digest d1) (CanonicalV1.cd_model_artifact_digest d2) &&
  digest_eqb (CanonicalV1.cd_preprocessing_digest d1) (CanonicalV1.cd_preprocessing_digest d2) &&
  digest_eqb (CanonicalV1.cd_inference_spec_digest d1) (CanonicalV1.cd_inference_spec_digest d2).

Lemma descriptor_eqb_true : forall d1 d2, descriptor_eqb d1 d2 = true -> d1 = d2.
Proof.
  intros [m1 p1 i1] [m2 p2 i2] H. unfold descriptor_eqb in H. cbn in H.
  apply andb_true_iff in H as [H12 H3].
  apply andb_true_iff in H12 as [H1 H2].
  apply digest_eqb_true in H1, H2, H3. subst. reflexivity.
Qed.

(* ----- F.3 wire decoder + committed policy / descriptor ----- *)
Variable parse_manifest : manifest -> option campaign_manifest_view.

Variable p_committed : policy.
Variable committed_descriptor : cd.

Variable policy_payload_digest_of : policy -> digest.
Hypothesis policy_payload_digest_injective :
  forall p q, policy_payload_digest_of p = policy_payload_digest_of q -> p = q.

Variable policy_context_of : policy -> cd.

(* ----- the AUDIT_POLICY 2.4.1 authenticate_manifest predicate ----- *)
Variable manifest_authenticated_by : manifest_commitment -> manifest -> Prop.

(* ----- the fixed objects this audit published (2.4 steps 3, 6) ----- *)
Variable audit_commitment : manifest_commitment.
Variable audit_manifest : manifest.
Variable audit_view : campaign_manifest_view.

Hypothesis audit_authenticated :
  manifest_authenticated_by audit_commitment audit_manifest.
Hypothesis audit_manifest_parses :
  parse_manifest audit_manifest = Some audit_view.
Hypothesis audit_policy_hash_committed :
  cm_policy_hash audit_view = policy_payload_digest_of p_committed.
Hypothesis committed_policy_context :
  policy_context_of p_committed = committed_descriptor.

(* ----- concrete matchers ----- *)

Definition manifest_policy_matches_impl (M : manifest) (ti : trusted_inputs)
  : bool :=
  match parse_manifest M with
  | Some cm => digest_eqb (cm_policy_hash cm) (ti_policy_digest ti)
  | None => false
  end.

Definition manifest_context_matches_impl (M : manifest) (ti : trusted_inputs)
  : bool :=
  match parse_manifest M with
  | Some cm => descriptor_eqb (cm_context_digests cm)
                              (policy_context_of (ti_policy ti))
  | None => false
  end.

(* concrete [commits] for [ValidationBinding]. *)
Definition commits_impl (mc : manifest_commitment) (d : cd) : Prop :=
  exists M cm,
    manifest_authenticated_by mc M /\
    parse_manifest M = Some cm /\
    cm_context_digests cm = d.

(* the AUDIT_POLICY 2.3 load-validation postcondition, for ONE input. *)
Definition policy_digest_load_validated (ti : trusted_inputs) : Prop :=
  ti_policy_digest ti = policy_payload_digest_of (ti_policy ti).

(* ----- the ops under verification ----- *)

Variable ops : primitive_ops.
Hypothesis ops_policy_match :
  op_manifest_policy_matches ops = manifest_policy_matches_impl.
Hypothesis ops_context_match :
  op_manifest_context_matches ops = manifest_context_matches_impl.

(* a successful validation is a validation OF THIS AUDIT. *)
Hypothesis validated_commitment_is_audit :
  forall ti ac l0,
    validate_campaign ops ti = ValidCampaign ac l0 ->
    authenticated_commitment ac = audit_commitment.
Hypothesis validated_manifest_is_audit :
  forall ti ac l0,
    validate_campaign ops ti = ValidCampaign ac l0 ->
    ti_manifest ti = audit_manifest.

(* ----- contract 1: policy match soundness ----- *)

Lemma manifest_policy_matches_impl_sound :
  forall ti,
    policy_digest_load_validated ti ->
    parse_manifest (ti_manifest ti) = Some audit_view ->
    manifest_policy_matches_impl (ti_manifest ti) ti = true ->
    ti_policy ti = p_committed.
Proof.
  intros ti Hload Hpar Hpm.
  unfold manifest_policy_matches_impl in Hpm. rewrite Hpar in Hpm.
  apply digest_eqb_true in Hpm.               (* cm_policy_hash audit_view = ti_policy_digest ti *)
  unfold policy_digest_load_validated in Hload.
  apply policy_payload_digest_injective.
  rewrite <- audit_policy_hash_committed.     (* goal: ppd (ti_policy ti) = cm_policy_hash audit_view *)
  rewrite Hpm. symmetry. exact Hload.
Qed.

(* ----- contract 2: context match soundness ----- *)

Lemma manifest_context_matches_impl_sound :
  forall ti,
    ti_policy ti = p_committed ->
    parse_manifest (ti_manifest ti) = Some audit_view ->
    manifest_context_matches_impl (ti_manifest ti) ti = true ->
    commits_impl audit_commitment committed_descriptor.
Proof.
  intros ti Hpolicy Hpar Hcm.
  unfold manifest_context_matches_impl in Hcm. rewrite Hpar in Hcm.
  apply descriptor_eqb_true in Hcm.           (* cm_context_digests audit_view = policy_context_of (ti_policy ti) *)
  exists audit_manifest, audit_view.
  split; [ exact audit_authenticated |].
  split; [ exact audit_manifest_parses |].
  rewrite Hcm, Hpolicy. exact committed_policy_context.
Qed.

(* ----- policy-only capstone: no context-side dependency ----- *)
(* proved from the policy matcher alone -- after section discharge this does NOT
   inherit ops_context_match / validated_commitment_is_audit / audit_authenticated
   / committed_policy_context / policy_context_of / committed_descriptor. *)

Theorem validate_campaign_concrete_binds_policy :
  forall ti ac l0,
    policy_digest_load_validated ti ->
    validate_campaign ops ti = ValidCampaign ac l0 ->
    ti_policy ti = p_committed.
Proof.
  intros ti ac l0 Hload H.
  destruct (validate_campaign_valid_guards ops ti H)
    as (mc & _ & _ & _ & Hpm0 & _ & _).
  rewrite ops_policy_match in Hpm0.
  pose proof (validated_manifest_is_audit ti H) as Hman.
  assert (parse_manifest (ti_manifest ti) = Some audit_view) as Hpar
    by (rewrite Hman; exact audit_manifest_parses).
  eapply manifest_policy_matches_impl_sound; eauto.
Qed.

(* ----- full capstone: policy AND context ----- *)

Theorem validate_campaign_concrete_binds :
  forall ti ac l0,
    policy_digest_load_validated ti ->
    validate_campaign ops ti = ValidCampaign ac l0 ->
    ti_policy ti = p_committed /\
    commits_impl (authenticated_commitment ac) committed_descriptor.
Proof.
  intros ti ac l0 Hload H.
  pose proof (validate_campaign_concrete_binds_policy Hload H) as Hpolicy.
  split; [ exact Hpolicy |].
  destruct (validate_campaign_valid_guards ops ti H)
    as (mc & _ & _ & _ & _ & Hcm0 & _).
  rewrite ops_context_match in Hcm0.
  pose proof (validated_manifest_is_audit ti H) as Hman.
  assert (parse_manifest (ti_manifest ti) = Some audit_view) as Hpar
    by (rewrite Hman; exact audit_manifest_parses).
  rewrite (validated_commitment_is_audit ti H).
  eapply manifest_context_matches_impl_sound; eauto.
Qed.

(* ----- concrete live/offline replay-policy corollaries ----- *)
(* SAME statements as ValidationBinding.assess_validated_*_uses_committed_policy,
   proved here from the policy-only capstone -- no opaque contract, and no
   context-side dependency beyond policy_digest_load_validated. *)

Theorem assess_validated_live_concrete :
  forall ti ac l0 tr cb,
    policy_digest_load_validated ti ->
    validate_campaign ops ti = ValidCampaign ac l0 ->
    assess_validated ops ti (ValidCampaign ac l0) (LiveTranscript tr cb)
    = decide ops
        (replay ops ac cb (ti_config ti) (ti_policy_document ti)
           p_committed l0 tr)
        ac ti tr (LiveCapture (op_transcript_digest ops tr))
        (AuthenticatedCommitment
           (commitment_digest (authenticated_commitment ac))).
Proof.
  intros ti ac l0 tr cb Hload H.
  pose proof (validate_campaign_concrete_binds_policy Hload H) as Hp.
  cbn [assess_validated]. rewrite Hp. reflexivity.
Qed.

Theorem assess_validated_offline_concrete :
  forall ti ac l0 tr wd cb,
    policy_digest_load_validated ti ->
    validate_campaign ops ti = ValidCampaign ac l0 ->
    assess_validated ops ti (ValidCampaign ac l0)
      (OfflineParse (WellformedParse tr wd) cb)
    = decide ops
        (replay ops ac cb (ti_config ti) (ti_policy_document ti)
           p_committed l0 tr)
        ac ti tr (OfflineTranscript (op_transcript_digest ops tr) wd)
        (AuthenticatedCommitment
           (commitment_digest (authenticated_commitment ac))).
Proof.
  intros ti ac l0 tr wd cb Hload H.
  pose proof (validate_campaign_concrete_binds_policy Hload H) as Hp.
  cbn [assess_validated]. rewrite Hp. reflexivity.
Qed.

End MM.

(* =====================================================================
   Consistency witness: concrete instances satisfying every non-[ops]
   hypothesis of Section MM at once.  (The two [ops] hypotheses hold by
   construction for the wired ops; the two [validated_*_is_audit] are
   vacuously satisfiable by any [ops] whose validation never succeeds --
   see the note in the header.)
   ===================================================================== *)

Definition mm_D0 : cd := CanonicalV1.mkContextDescriptor "m" "p" "i".
Definition mm_view : campaign_manifest_view :=
  CanonicalV1.mkCampaignManifestView "ai-0001" "cmp" mm_D0 "PH" [].

(* concrete witnesses *)
Definition mm_ppd : policy -> digest := fun p => p.
Definition mm_pco : policy -> cd := fun _ => mm_D0.
Definition mm_pm  : manifest -> option campaign_manifest_view := fun _ => Some mm_view.
Definition mm_mab : manifest_commitment -> manifest -> Prop := fun _ _ => True.
Definition mm_p_committed : policy := "PH".
Definition mm_manifest : manifest := mkManifest "M".
Definition mm_commitment : manifest_commitment := mkManifestCommitment "dg" "signer" "".
Definition mm_ti : trusted_inputs :=
  mkTrustedInputs (mkManifestCommitmentWire "" "" "") mm_manifest []
    (mkCampaignRecord "") CompletenessUnknown
    (mkVerifierConfig 0 0 0 0 0 0 (mkFuelSchedule 0 0 0 0 0 0 0)
       (mkTrustAnchor [] []))
    "" "PH" "PH".

Lemma mm_ppd_injective : forall p q, mm_ppd p = mm_ppd q -> p = q.
Proof. unfold mm_ppd. intros p q H. exact H. Qed.

(* every non-[ops] hypothesis of Section MM holds simultaneously for these
   witnesses -- so the hypothesis set is consistent (defect 1 addressed: the
   old [forall ti, ...] digest-truthfulness is replaced by
   [policy_digest_load_validated ti] on ONE input, satisfiable here). *)
Lemma manifest_matching_core_hyps_consistent :
  (forall a b, String.eqb a b = true -> a = b) /\
  (forall p q, mm_ppd p = mm_ppd q -> p = q) /\
  mm_mab mm_commitment mm_manifest /\
  mm_pm mm_manifest = Some mm_view /\
  cm_policy_hash mm_view = mm_ppd mm_p_committed /\
  mm_pco mm_p_committed = mm_D0 /\
  policy_digest_load_validated mm_ppd mm_ti.
Proof.
  split; [ intros a b Hab; now apply String.eqb_eq |].
  split; [ exact mm_ppd_injective |].
  split; [ exact I |].
  split; [ reflexivity |].
  split; [ reflexivity |].
  split; [ reflexivity |].
  reflexivity.
Qed.
