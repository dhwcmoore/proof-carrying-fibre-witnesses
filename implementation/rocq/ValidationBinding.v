(** Connect a successful [validate_campaign] to the committed policy and the
    committed descriptor, and thread the committed policy through
    [assess_validated] / [replay].

    [validate_campaign_valid_guards] is a general fact (any [ops]).  The
    soundness contracts are then scoped to ONE [ops]:

      Variable ops : primitive_ops.
      Hypothesis policy_match_sound :
        forall ti, op_manifest_policy_matches ops (ti_manifest ti) ti = true ->
          ti_policy ti = p_committed.
      Hypothesis context_match_sound : ... (for that same [ops]).

    So the hypotheses constrain the [ops] under verification -- not every
    conceivable implementation.  After section discharge they are ordinary
    premises about a given [ops], satisfiable when its manifest-matching
    primitives are implemented against the frozen manifest schema
    (AUDIT_POLICY_AND_EVIDENCE.md 2.4).

    Dependency split:
    - [validate_campaign_binds_policy] : [ti_policy ti = p_committed] -- uses
      [policy_match_sound] ONLY.
    - [validate_campaign_binds_descriptor] :
      [commits (authenticated_commitment ac) committed_descriptor] -- uses
      [context_match_sound].
    - the two [assess_validated_*_uses_committed_policy] proofs use
      [validate_campaign_binds_policy], hence [policy_match_sound] only. *)

From Coq Require Import Bool List ZArith.
From PCFW Require Import Orchestration ContextResolution.
Import ListNotations.

Set Implicit Arguments.

Section VB.
Variable p_committed : policy.
Variable committed_descriptor : descriptor.
Variable commits : manifest_commitment -> descriptor -> Prop.

(* ----- general: a successful validate_campaign passed every guard ----- *)

Lemma validate_campaign_valid_guards :
  forall ops ti ac l0,
    validate_campaign ops ti = ValidCampaign ac l0 ->
    exists mc,
      op_parse_commitment ops (ti_commitment_wire ti) = CommitmentParsed mc /\
      op_signer_authorised ops (ti_config ti) mc = true /\
      op_signature_valid ops (ti_config ti) mc (ti_manifest ti) = true /\
      op_manifest_policy_matches ops (ti_manifest ti) ti = true /\
      op_manifest_context_matches ops (ti_manifest ti) ti = true /\
      ac = authenticated_of ti mc.
Proof.
  intros ops ti ac l0 H. unfold validate_campaign in H.
  destruct (charge (validation_seed ti)
              (commitment_parse_fuel (schedule (ti_config ti)))) as [l1|];
    [| discriminate].
  destruct (op_parse_commitment ops (ti_commitment_wire ti)) as [msg | mc];
    [ discriminate |].
  destruct (op_signer_authorised ops (ti_config ti) mc) eqn:Hsa; cbn [negb] in H; [| discriminate].
  destruct (charge l1 (signature_verify_fuel (schedule (ti_config ti)))) as [l2|];
    [| discriminate].
  destruct (op_signature_valid ops (ti_config ti) mc (ti_manifest ti)) eqn:Hsv;
    cbn [negb] in H; [| discriminate].
  destruct (charge l2 (manifest_bind_fuel (schedule (ti_config ti)))) as [l3|];
    [| discriminate].
  destruct (op_manifest_policy_matches ops (ti_manifest ti) ti) eqn:Hpm;
    cbn [negb] in H; [| discriminate].
  destruct (op_manifest_audit_matches ops (ti_manifest ti) ti) eqn:Ham;
    cbn [negb] in H; [| discriminate].
  destruct (op_manifest_context_matches ops (ti_manifest ti) ti) eqn:Hcm;
    cbn [negb] in H; [| discriminate].
  destruct (charge l3 (record_bind_fuel (schedule (ti_config ti)))) as [l4|];
    [| discriminate].
  destruct (op_ledger_mismatch ops (ti_manifest ti) (ti_submissions ti)) as [i|];
    [ discriminate |].
  destruct (op_record_identity_mismatch ops (ti_record ti) mc (ti_manifest ti) ti)
    as [field|]; [ discriminate |].
  destruct (op_completeness_wellformed ops (ti_completeness ti)) eqn:Hcw;
    cbn [negb] in H; [| discriminate].
  injection H as <- _.
  exists mc. repeat split; try assumption; reflexivity.
Qed.

(* the ledger step (step 7) also passed: op_ledger_mismatch returned None.
   Kept as a standalone fact so the existing valid_guards destructures are
   undisturbed. *)
Lemma validate_campaign_valid_ledger :
  forall ops ti ac l0,
    validate_campaign ops ti = ValidCampaign ac l0 ->
    op_ledger_mismatch ops (ti_manifest ti) (ti_submissions ti) = None.
Proof.
  intros ops ti ac l0 H. unfold validate_campaign in H.
  destruct (charge (validation_seed ti)
              (commitment_parse_fuel (schedule (ti_config ti)))) as [l1|];
    [| discriminate].
  destruct (op_parse_commitment ops (ti_commitment_wire ti)) as [msg | mc];
    [ discriminate |].
  destruct (op_signer_authorised ops (ti_config ti) mc) eqn:Hsa;
    cbn [negb] in H; [| discriminate].
  destruct (charge l1 (signature_verify_fuel (schedule (ti_config ti)))) as [l2|];
    [| discriminate].
  destruct (op_signature_valid ops (ti_config ti) mc (ti_manifest ti)) eqn:Hsv;
    cbn [negb] in H; [| discriminate].
  destruct (charge l2 (manifest_bind_fuel (schedule (ti_config ti)))) as [l3|];
    [| discriminate].
  destruct (op_manifest_policy_matches ops (ti_manifest ti) ti) eqn:Hpm;
    cbn [negb] in H; [| discriminate].
  destruct (op_manifest_audit_matches ops (ti_manifest ti) ti) eqn:Ham;
    cbn [negb] in H; [| discriminate].
  destruct (op_manifest_context_matches ops (ti_manifest ti) ti) eqn:Hcm;
    cbn [negb] in H; [| discriminate].
  destruct (charge l3 (record_bind_fuel (schedule (ti_config ti)))) as [l4|];
    [| discriminate].
  destruct (op_ledger_mismatch ops (ti_manifest ti) (ti_submissions ti))
    as [i|] eqn:Hlm; [ discriminate | reflexivity ].
Qed.

(* the audit-instance step (step 5) also passed.  Standalone, so the existing
   valid_guards destructures stay as they are. *)
Lemma validate_campaign_valid_audit :
  forall ops ti ac l0,
    validate_campaign ops ti = ValidCampaign ac l0 ->
    op_manifest_audit_matches ops (ti_manifest ti) ti = true.
Proof.
  intros ops ti ac l0 H. unfold validate_campaign in H.
  destruct (charge (validation_seed ti)
              (commitment_parse_fuel (schedule (ti_config ti)))) as [l1|];
    [| discriminate].
  destruct (op_parse_commitment ops (ti_commitment_wire ti)) as [msg | mc];
    [ discriminate |].
  destruct (op_signer_authorised ops (ti_config ti) mc) eqn:Hsa;
    cbn [negb] in H; [| discriminate].
  destruct (charge l1 (signature_verify_fuel (schedule (ti_config ti)))) as [l2|];
    [| discriminate].
  destruct (op_signature_valid ops (ti_config ti) mc (ti_manifest ti)) eqn:Hsv;
    cbn [negb] in H; [| discriminate].
  destruct (charge l2 (manifest_bind_fuel (schedule (ti_config ti)))) as [l3|];
    [| discriminate].
  destruct (op_manifest_policy_matches ops (ti_manifest ti) ti) eqn:Hpm;
    cbn [negb] in H; [| discriminate].
  destruct (op_manifest_audit_matches ops (ti_manifest ti) ti) eqn:Ham;
    cbn [negb] in H; [| discriminate].
  reflexivity.
Qed.

(* the record-identity step (step 8) also passed: op_record_identity_mismatch
   returned None on the parsed commitment.  Standalone. *)
Lemma validate_campaign_valid_record :
  forall ops ti ac l0,
    validate_campaign ops ti = ValidCampaign ac l0 ->
    exists mc,
      op_parse_commitment ops (ti_commitment_wire ti) = CommitmentParsed mc /\
      op_record_identity_mismatch ops (ti_record ti) mc (ti_manifest ti) ti = None.
Proof.
  intros ops ti ac l0 H. unfold validate_campaign in H.
  destruct (charge (validation_seed ti)
              (commitment_parse_fuel (schedule (ti_config ti)))) as [l1|];
    [| discriminate].
  destruct (op_parse_commitment ops (ti_commitment_wire ti)) as [msg | mc] eqn:Hpc;
    [ discriminate |].
  destruct (op_signer_authorised ops (ti_config ti) mc) eqn:Hsa;
    cbn [negb] in H; [| discriminate].
  destruct (charge l1 (signature_verify_fuel (schedule (ti_config ti)))) as [l2|];
    [| discriminate].
  destruct (op_signature_valid ops (ti_config ti) mc (ti_manifest ti)) eqn:Hsv;
    cbn [negb] in H; [| discriminate].
  destruct (charge l2 (manifest_bind_fuel (schedule (ti_config ti)))) as [l3|];
    [| discriminate].
  destruct (op_manifest_policy_matches ops (ti_manifest ti) ti) eqn:Hpm;
    cbn [negb] in H; [| discriminate].
  destruct (op_manifest_audit_matches ops (ti_manifest ti) ti) eqn:Ham;
    cbn [negb] in H; [| discriminate].
  destruct (op_manifest_context_matches ops (ti_manifest ti) ti) eqn:Hcm;
    cbn [negb] in H; [| discriminate].
  destruct (charge l3 (record_bind_fuel (schedule (ti_config ti)))) as [l4|];
    [| discriminate].
  destruct (op_ledger_mismatch ops (ti_manifest ti) (ti_submissions ti))
    as [i|]; [ discriminate |].
  destruct (op_record_identity_mismatch ops (ti_record ti) mc (ti_manifest ti) ti)
    as [field|] eqn:Hrim; [ discriminate |].
  exists mc. split; [ reflexivity | exact Hrim ].
Qed.

(* the completeness step (step 9) also passed: op_completeness_wellformed
   returned true on the trusted-input's completeness status.  Standalone, so
   the existing valid_guards destructures stay as they are. *)
Lemma validate_campaign_valid_completeness :
  forall ops ti ac l0,
    validate_campaign ops ti = ValidCampaign ac l0 ->
    op_completeness_wellformed ops (ti_completeness ti) = true.
Proof.
  intros ops ti ac l0 H. unfold validate_campaign in H.
  destruct (charge (validation_seed ti)
              (commitment_parse_fuel (schedule (ti_config ti)))) as [l1|];
    [| discriminate].
  destruct (op_parse_commitment ops (ti_commitment_wire ti)) as [msg | mc];
    [ discriminate |].
  destruct (op_signer_authorised ops (ti_config ti) mc) eqn:Hsa;
    cbn [negb] in H; [| discriminate].
  destruct (charge l1 (signature_verify_fuel (schedule (ti_config ti)))) as [l2|];
    [| discriminate].
  destruct (op_signature_valid ops (ti_config ti) mc (ti_manifest ti)) eqn:Hsv;
    cbn [negb] in H; [| discriminate].
  destruct (charge l2 (manifest_bind_fuel (schedule (ti_config ti)))) as [l3|];
    [| discriminate].
  destruct (op_manifest_policy_matches ops (ti_manifest ti) ti) eqn:Hpm;
    cbn [negb] in H; [| discriminate].
  destruct (op_manifest_audit_matches ops (ti_manifest ti) ti) eqn:Ham;
    cbn [negb] in H; [| discriminate].
  destruct (op_manifest_context_matches ops (ti_manifest ti) ti) eqn:Hcm;
    cbn [negb] in H; [| discriminate].
  destruct (charge l3 (record_bind_fuel (schedule (ti_config ti)))) as [l4|];
    [| discriminate].
  destruct (op_ledger_mismatch ops (ti_manifest ti) (ti_submissions ti))
    as [i|]; [ discriminate |].
  destruct (op_record_identity_mismatch ops (ti_record ti) mc (ti_manifest ti) ti)
    as [field|]; [ discriminate |].
  destruct (op_completeness_wellformed ops (ti_completeness ti));
    cbn [negb] in H; [reflexivity | discriminate].
Qed.

(* ----- contracts scoped to ONE ops ----- *)

Variable ops : primitive_ops.

Hypothesis policy_match_sound :
  forall ti,
    op_manifest_policy_matches ops (ti_manifest ti) ti = true ->
    ti_policy ti = p_committed.

Hypothesis context_match_sound :
  forall ti mc,
    op_parse_commitment ops (ti_commitment_wire ti) = CommitmentParsed mc ->
    op_signature_valid ops (ti_config ti) mc (ti_manifest ti) = true ->
    op_manifest_context_matches ops (ti_manifest ti) ti = true ->
    commits mc committed_descriptor.

Lemma validate_campaign_binds_policy :
  forall ti ac l0,
    validate_campaign ops ti = ValidCampaign ac l0 ->
    ti_policy ti = p_committed.
Proof.
  intros ti ac l0 H.
  destruct (validate_campaign_valid_guards ops ti H)
    as (mc & _ & _ & _ & Hpm & _ & _).
  exact (policy_match_sound ti Hpm).
Qed.

Lemma validate_campaign_binds_descriptor :
  forall ti ac l0,
    validate_campaign ops ti = ValidCampaign ac l0 ->
    commits (authenticated_commitment ac) committed_descriptor.
Proof.
  intros ti ac l0 H.
  destruct (validate_campaign_valid_guards ops ti H)
    as (mc & Hpc & _ & Hsv & _ & Hcm & ->).
  cbn [authenticated_of authenticated_commitment].
  exact (context_match_sound ti Hpc Hsv Hcm).
Qed.

Theorem validate_campaign_binds :
  forall ti ac l0,
    validate_campaign ops ti = ValidCampaign ac l0 ->
    ti_policy ti = p_committed /\
    commits (authenticated_commitment ac) committed_descriptor.
Proof.
  intros ti ac l0 H.
  split; [ exact (validate_campaign_binds_policy ti H)
         | exact (validate_campaign_binds_descriptor ti H) ].
Qed.

(* ----- committed policy flows into replay (policy contract only) ----- *)

Theorem assess_validated_live_uses_committed_policy :
  forall ti ac l0 tr cb,
    validate_campaign ops ti = ValidCampaign ac l0 ->
    assess_validated ops ti (ValidCampaign ac l0) (LiveTranscript tr cb)
    = decide ops
        (replay ops ac cb (ti_config ti) (ti_policy_document ti)
           p_committed l0 tr)
        ac ti tr (LiveCapture (op_transcript_digest ops tr))
        (AuthenticatedCommitment
           (commitment_digest (authenticated_commitment ac))).
Proof.
  intros ti ac l0 tr cb H.
  pose proof (validate_campaign_binds_policy ti H) as Hp.
  cbn [assess_validated]. rewrite Hp. reflexivity.
Qed.

Theorem assess_validated_offline_uses_committed_policy :
  forall ti ac l0 tr wd cb,
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
  intros ti ac l0 tr wd cb H.
  pose proof (validate_campaign_binds_policy ti H) as Hp.
  cbn [assess_validated]. rewrite Hp. reflexivity.
Qed.

End VB.
