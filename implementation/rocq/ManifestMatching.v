(** Parametric policy binding and separate concrete manifest checks.
    [policy_binding p_committed ti] is supplied local orchestration-token
    equality, not inferred from a digest. Kernel.Policy / AuditContext semantic
    realisation is a separate external contract. The two digest-agreement
    results expose integrity evidence independently. No matcher, authentication,
    context or validation algorithm changes. The examples use opaque strings,
    not a concrete semantic Policy or loader. *)

From Coq Require Import Bool List String.
From PCFW Require Import Orchestration ContextResolution ValidationBinding CanonicalV1.
Import ListNotations.

Set Implicit Arguments.

(* the [campaign_manifest] fields (AUDIT_POLICY 2.1 / 2.4 step 6) this unit reads;
   [parse_manifest] is the F.3 decoder from the wire [manifest]. *)
(* THE shared validation type (also produced by ManifestAuthentication.parse_manifest_impl). *)
Notation campaign_manifest_view := CanonicalV1.campaign_manifest_view.
Notation cd := CanonicalV1.context_descriptor.

(* Transparent local contract on ONE input. *)
Definition policy_binding (p_committed : policy) (ti : trusted_inputs) : Prop :=
  ti_policy ti = p_committed.

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

(* Digest evidence does not establish policy identity. *)
Lemma manifest_policy_matches_impl_digest_agrees :
  forall ti cm,
    parse_manifest (ti_manifest ti) = Some cm ->
    manifest_policy_matches_impl (ti_manifest ti) ti = true ->
    cm_policy_hash cm = ti_policy_digest ti.
Proof.
  intros ti cm Hpar Hmatch.
  unfold manifest_policy_matches_impl in Hmatch. rewrite Hpar in Hmatch.
  now apply digest_eqb_true in Hmatch.
Qed.

Lemma manifest_policy_matches_impl_sound :
  forall ti,
    policy_binding p_committed ti ->
    parse_manifest (ti_manifest ti) = Some audit_view ->
    manifest_policy_matches_impl (ti_manifest ti) ti = true ->
    ti_policy ti = p_committed.
Proof. intros ti Hbinding _ _. exact Hbinding. Qed.

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

(* Policy identity is an explicit local premise. *)
Theorem validate_campaign_concrete_binds_policy :
  forall ti ac l0,
    policy_binding p_committed ti ->
    validate_campaign ops ti = ValidCampaign ac l0 ->
    ti_policy ti = p_committed.
Proof. intros ti ac l0 Hbinding _. exact Hbinding. Qed.

Theorem validate_campaign_concrete_digest_agrees :
  forall ti ac l0,
    validate_campaign ops ti = ValidCampaign ac l0 ->
    exists cm,
      parse_manifest (ti_manifest ti) = Some cm /\
      cm_policy_hash cm = ti_policy_digest ti.
Proof.
  intros ti ac l0 H.
  destruct (validate_campaign_valid_guards ops ti H)
    as (mc & _ & _ & _ & Hmatch & _ & _).
  rewrite ops_policy_match in Hmatch.
  destruct (parse_manifest (ti_manifest ti)) as [cm|] eqn:Hpar.
  - exists cm. split; [ reflexivity |].
    eapply manifest_policy_matches_impl_digest_agrees; eauto.
  - unfold manifest_policy_matches_impl in Hmatch. rewrite Hpar in Hmatch.
    discriminate.
Qed.

(* ----- full capstone: policy AND context ----- *)

Theorem validate_campaign_concrete_binds :
  forall ti ac l0,
    policy_binding p_committed ti ->
    validate_campaign ops ti = ValidCampaign ac l0 ->
    ti_policy ti = p_committed /\
    commits_impl (authenticated_commitment ac) committed_descriptor.
Proof.
  intros ti ac l0 Hbinding H.
  pose proof (validate_campaign_concrete_binds_policy Hbinding H) as Hpolicy.
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
   proved here from an explicit local equality contract, with no
   digest-to-policy identity inference or context-side dependency. *)

Theorem assess_validated_live_concrete :
  forall ti ac l0 tr cb,
    policy_binding p_committed ti ->
    validate_campaign ops ti = ValidCampaign ac l0 ->
    assess_validated ops ti (ValidCampaign ac l0) (LiveTranscript tr cb)
    = decide ops
        (replay ops ac cb (ti_config ti) (ti_policy_document ti)
           p_committed l0 tr)
        ac ti tr (LiveCapture (op_transcript_digest ops tr))
        (AuthenticatedCommitment
           (commitment_digest (authenticated_commitment ac))).
Proof.
  intros ti ac l0 tr cb Hbinding H.
  pose proof (validate_campaign_concrete_binds_policy Hbinding H) as Hp.
  cbn [assess_validated]. rewrite Hp. reflexivity.
Qed.

Theorem assess_validated_offline_concrete :
  forall ti ac l0 tr wd cb,
    policy_binding p_committed ti ->
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
  intros ti ac l0 tr wd cb Hbinding H.
  pose proof (validate_campaign_concrete_binds_policy Hbinding H) as Hp.
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

(* Fixed-object and per-input contracts are jointly satisfiable; this is not
   a successful validation or a semantic Policy loader. *)
Lemma manifest_matching_core_hyps_consistent :
  (forall a b, String.eqb a b = true -> a = b) /\
  mm_mab mm_commitment mm_manifest /\
  mm_pm mm_manifest = Some mm_view /\
  cm_policy_hash mm_view = mm_ppd mm_p_committed /\
  mm_pco mm_p_committed = mm_D0 /\
  policy_digest_load_validated mm_ppd mm_ti /\
  policy_binding mm_p_committed mm_ti.
Proof.
  split; [ intros a b Hab; now apply String.eqb_eq |].
  split; [ exact I |]. repeat split; reflexivity.
Qed.

(* An abstract constant digest demonstrates independence, not a SHA collision.
   Truthful digest fields and matching hashes do not imply policy binding. *)
Example digest_agreement_does_not_bind_policy :
  let h : policy -> digest := fun _ => "PH" in
  policy_digest_load_validated h mm_ti /\
  cm_policy_hash mm_view = h "different" /\
  manifest_policy_matches_impl String.eqb mm_pm mm_manifest mm_ti = true /\
  ~ policy_binding "different" mm_ti.
Proof. cbn. repeat split; try reflexivity. discriminate. Qed.
