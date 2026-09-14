(** Contract-bound primitive `op_transcript_digest` (VERDICT_SEMANTICS.md 6.7,
    9): the final open `primitive_ops` member.

    SCOPE.  This is an interface-and-evidence-binding unit, NOT a
    cryptographic implementation unit:

    - `op_transcript_digest : exec_transcript -> digest` REMAINS a primitive
      hook -- this module does not implement it.
    - The normative target is `digest_v1("pcfw.exec_transcript.v1",
      to_cv(tr))`; its concrete canonicaliser and SHA-256 realisation stay F.3
      (an abstract `transcript_digest_v1` Section `Variable` stands for it).
    - The required formal guarantee is DETERMINISTIC EQUALITY on identical
      typed canonical inputs -- ordinary Gallina functional congruence, proved
      below and documented as exactly that, no more.  NO injectivity or
      collision-resistance claim is made or needed: different transcripts are
      NOT required to produce provably different digests.
    - This unit does NOT implement or prove `parse_transcript`, does NOT
      discharge `transcript_stage2_wf`, and does NOT establish transcript
      faithfulness -- all three stay open, separate obligations.
    - The offline RAW-WIRE digest `digest_bytes_v1("pcfw.exec_transcript_wire.v1",
      wire_bytes)` is a SEPARATE quantity (computed upstream, over the parsed
      transcript's `wire_digest`, never over a typed `exec_transcript`) and is
      never conflated with the typed-transcript digest anywhere below.

    The substantive work here is: (1) that replacing `op_transcript_digest`
    cannot affect `validate_campaign`, `replay`, or the campaign verdict --
    only `transcript_evidence` can carry the replacement digest; (2) that live
    and (well-formed) offline evidence bind the SAME typed-transcript digest,
    with the offline branch ALSO carrying its own, separate raw-wire digest;
    (3) that a malformed offline transcript carries ONLY its raw-wire digest,
    with no typed-transcript digest and no dependence on `op_transcript_digest`
    at all. *)

From Coq Require Import String List Arith.
From PCFW Require Import Orchestration.
Import ListNotations.

(* ================= 1. the operation itself: replace, and preserve everything else ================= *)

(* `op_transcript_digest` is the LAST `primitive_ops` field; every other field
   is a straight pass-through of `ops`'s own. *)
Definition set_transcript_digest (ops : primitive_ops)
  (g : exec_transcript -> digest) : primitive_ops :=
  mkPrimitiveOps
    (op_parse_commitment ops) (op_signer_authorised ops) (op_signature_valid ops)
    (op_manifest_policy_matches ops) (op_manifest_audit_matches ops)
    (op_manifest_context_matches ops) (op_ledger_mismatch ops)
    (op_record_identity_mismatch ops) (op_completeness_wellformed ops)
    (op_stage1_check ops) (op_preflight ops) (op_eval_o3 ops)
    (op_stage2_check ops) (op_record_crosscheck ops) g.

Lemma set_transcript_digest_field : forall ops g,
  op_transcript_digest (set_transcript_digest ops g) = g.
Proof. reflexivity. Qed.

(* every OTHER field is preserved -- a single compact conjunction covering all
   fourteen of them. *)
Lemma set_transcript_digest_preserves_others : forall ops g,
  op_parse_commitment (set_transcript_digest ops g) = op_parse_commitment ops /\
  op_signer_authorised (set_transcript_digest ops g) = op_signer_authorised ops /\
  op_signature_valid (set_transcript_digest ops g) = op_signature_valid ops /\
  op_manifest_policy_matches (set_transcript_digest ops g) = op_manifest_policy_matches ops /\
  op_manifest_audit_matches (set_transcript_digest ops g) = op_manifest_audit_matches ops /\
  op_manifest_context_matches (set_transcript_digest ops g) = op_manifest_context_matches ops /\
  op_ledger_mismatch (set_transcript_digest ops g) = op_ledger_mismatch ops /\
  op_record_identity_mismatch (set_transcript_digest ops g) = op_record_identity_mismatch ops /\
  op_completeness_wellformed (set_transcript_digest ops g) = op_completeness_wellformed ops /\
  op_stage1_check (set_transcript_digest ops g) = op_stage1_check ops /\
  op_preflight (set_transcript_digest ops g) = op_preflight ops /\
  op_eval_o3 (set_transcript_digest ops g) = op_eval_o3 ops /\
  op_stage2_check (set_transcript_digest ops g) = op_stage2_check ops /\
  op_record_crosscheck (set_transcript_digest ops g) = op_record_crosscheck ops.
Proof. intros. repeat split; reflexivity. Qed.

(* ================= 2. determinism -- ordinary functional congruence ================= *)

(* NOT a cryptographic claim: this is Gallina congruence (any function maps
   equal inputs to equal outputs).  It says nothing about different
   transcripts, and nothing about collision resistance. *)
Theorem op_transcript_digest_deterministic : forall ops tr1 tr2,
  tr1 = tr2 -> op_transcript_digest ops tr1 = op_transcript_digest ops tr2.
Proof. intros ops tr1 tr2 ->. reflexivity. Qed.

(* ================= 3. non-interference: validate_campaign / replay / verdict ================= *)

(* validate_campaign never reads op_transcript_digest at all (it runs entirely
   before any transcript is consulted) -- a direct consequence of every
   op-projection it uses reducing through set_transcript_digest unchanged, no
   induction needed (validate_campaign has no unbounded recursion). *)
Theorem validate_campaign_indep_of_transcript_digest : forall ops g ti,
  validate_campaign (set_transcript_digest ops g) ti = validate_campaign ops ti.
Proof. reflexivity. Qed.

(* run_stage1 / run_stage2 recurse over an abstract list, so (as with
   RecordCrosscheck.set_crosscheck) proving them unchanged needs induction:
   the OTHER fourteen fields are unaffected at every step, but the recursive
   application itself is only convertible once fuel/subs/pending are
   generalised through the induction. *)
Lemma run_stage1_set_transcript_digest : forall ops g cfg pd p subs i fuel sr pr,
  run_stage1 (set_transcript_digest ops g) cfg pd p subs i fuel sr pr
  = run_stage1 ops cfg pd p subs i fuel sr pr.
Proof.
  intros ops g cfg pd p subs.
  induction subs as [| sub rest IH]; intros i fuel sr pr;
    cbn [run_stage1]; [ reflexivity |].
  replace (op_stage1_check (set_transcript_digest ops g)) with (op_stage1_check ops)
    by reflexivity.
  destruct (charge fuel (stage1_cost cfg sub)) as [fuel'|]; [| reflexivity].
  rewrite IH. reflexivity.
Qed.

Lemma run_stage2_set_transcript_digest : forall ops g rc cfg tr pending fuel sr,
  run_stage2 (set_transcript_digest ops g) rc cfg tr pending fuel sr
  = run_stage2 ops rc cfg tr pending fuel sr.
Proof.
  intros ops g rc cfg tr pending.
  induction pending as [| ps rest IH]; intros fuel sr;
    cbn [run_stage2]; [ reflexivity |].
  replace (op_stage2_check (set_transcript_digest ops g)) with (op_stage2_check ops)
    by reflexivity.
  destruct (charge fuel (4 * model_call_fuel cfg)) as [fuel'|]; [| reflexivity].
  rewrite IH. reflexivity.
Qed.

(* finish_replay's only ops-dependency is op_record_crosscheck, unaffected. *)
Lemma finish_replay_set_transcript_digest : forall ops g ac cfg s1 ctx s2 fuel clo,
  finish_replay (set_transcript_digest ops g) ac cfg s1 ctx s2 fuel clo
  = finish_replay ops ac cfg s1 ctx s2 fuel clo.
Proof.
  intros. unfold finish_replay.
  replace (op_record_crosscheck (set_transcript_digest ops g))
    with (op_record_crosscheck ops) by reflexivity.
  reflexivity.
Qed.

(* the FULL replay_result is unchanged -- strictly stronger than
   RecordCrosscheck's field-wise independence, because unlike
   op_record_crosscheck, op_transcript_digest affects NOTHING inside replay,
   not even record_findings. *)
Theorem replay_indep_of_transcript_digest :
  forall ops g ac cb cfg pd p l0 tr,
    replay (set_transcript_digest ops g) ac cb cfg pd p l0 tr
    = replay ops ac cb cfg pd p l0 tr.
Proof.
  intros ops g ac cb cfg pd p l0 tr.
  unfold replay.
  rewrite run_stage1_set_transcript_digest.
  replace (op_preflight (set_transcript_digest ops g)) with (op_preflight ops)
    by reflexivity.
  replace (op_eval_o3 (set_transcript_digest ops g)) with (op_eval_o3 ops)
    by reflexivity.
  destruct (Nat.ltb (max_candidates cfg)
              (Datatypes.length (authenticated_submissions ac)));
    [ apply finish_replay_set_transcript_digest |].
  destruct (run_stage1 ops cfg pd p (authenticated_submissions ac) 0 l0 [] [])
    as [fuel s1 pending | fuel s1 pending];
    [| apply finish_replay_set_transcript_digest ].
  destruct pending as [| ps0 pr]; [ apply finish_replay_set_transcript_digest |].
  destruct cb as [| reason | lc];
    [ apply finish_replay_set_transcript_digest
    | apply finish_replay_set_transcript_digest |].
  destruct (charge fuel (preflight_fuel (schedule cfg))) as [fuel1|];
    [| apply finish_replay_set_transcript_digest ].
  destruct (op_preflight ops lc) as [reason findings | preflight_findings];
    [ apply finish_replay_set_transcript_digest |].
  destruct (charge fuel1 (model_call_fuel cfg)) as [fuel2|];
    [| apply finish_replay_set_transcript_digest ].
  destruct (lookup_unique tr (mkCallKey ContextProbe Probe 0)) as [event|];
    [| apply finish_replay_set_transcript_digest ].
  destruct (op_eval_o3 ops lc event p) as [findings | rc o3_findings];
    [ apply finish_replay_set_transcript_digest |].
  rewrite run_stage2_set_transcript_digest.
  destruct (run_stage2 ops rc cfg tr (ps0 :: pr) fuel2 []) as [[s2 fuel3] clo].
  apply finish_replay_set_transcript_digest.
Qed.

(* decide never inspects `_ops`, `_tr`, `tev`, or `cev` -- only `rr` and
   `authenticated_completeness ac` -- so verdict_of . decide is indifferent to
   ALL of them, in particular to the transcript_evidence value threaded in. *)
Lemma decide_verdict_indep_of_tev : forall ops ops' rr ac ti tr tev1 tev2 cev,
  verdict_of (decide ops rr ac ti tr tev1 cev)
  = verdict_of (decide ops' rr ac ti tr tev2 cev).
Proof.
  intros. unfold decide, verdict_of.
  destruct (valid_witnesses (replay_stage2 rr)); try reflexivity.
  destruct (replay_clo rr); try reflexivity.
  destruct (all_checked_obstructions (replay_stage2 rr)) as [ [[? ?] ?] |];
    try reflexivity.
  destruct (replay_context rr); try reflexivity.
  destruct (authenticated_completeness ac); try reflexivity.
Qed.

(* the headline result: the digest hook RECORDS which transcript was assessed
   (in transcript_evidence, §5 below) but cannot manufacture or suppress a
   witness -- replacing it by ANY function leaves the campaign verdict
   unchanged. *)
Theorem verdict_indep_of_transcript_digest :
  forall ops g ti vr src,
    verdict_of (assess_validated (set_transcript_digest ops g) ti vr src)
    = verdict_of (assess_validated ops ti vr src).
Proof.
  intros ops g ti vr src.
  destruct vr as [reason fuel ev | fuel ev | ac l0]; [ reflexivity | reflexivity |].
  unfold assess_validated.
  destruct src as [ tr cb | [ reason wd | tr wd ] cb ].
  - rewrite (replay_indep_of_transcript_digest ops g ac cb (ti_config ti)
               (ti_policy_document ti) (ti_policy ti) l0 tr).
    apply decide_verdict_indep_of_tev.
  - reflexivity.
  - rewrite (replay_indep_of_transcript_digest ops g ac cb (ti_config ti)
               (ti_policy_document ti) (ti_policy ti) l0 tr).
    apply decide_verdict_indep_of_tev.
Qed.

(* ================= 4. evidence projections ================= *)

Definition outcome_transcript_evidence (out : assessment_outcome) : transcript_evidence :=
  match out with
  | Inadmissible c | Exact c | Obstructed c => certificate_transcript c
  | Underdetermined r => report_transcript r
  end.

(* decide always stores its `tev` argument verbatim, in every branch. *)
Lemma decide_transcript_evidence : forall ops rr ac ti tr tev cev,
  outcome_transcript_evidence (decide ops rr ac ti tr tev cev) = tev.
Proof.
  intros. unfold decide, outcome_transcript_evidence.
  destruct (valid_witnesses (replay_stage2 rr)); try reflexivity.
  destruct (replay_clo rr); try reflexivity.
  destruct (all_checked_obstructions (replay_stage2 rr)) as [ [[? ?] ?] |];
    try reflexivity.
  destruct (replay_context rr); try reflexivity.
  destruct (authenticated_completeness ac); try reflexivity.
Qed.

Theorem live_evidence_uses_typed_transcript_digest :
  forall ops ti ac fuel tr cb,
    outcome_transcript_evidence
      (assess_validated ops ti (ValidCampaign ac fuel) (LiveTranscript tr cb))
    = LiveCapture (op_transcript_digest ops tr).
Proof. intros. unfold assess_validated. apply decide_transcript_evidence. Qed.

Theorem offline_evidence_uses_both_digests :
  forall ops ti ac fuel tr wire_digest cb,
    outcome_transcript_evidence
      (assess_validated ops ti (ValidCampaign ac fuel)
        (OfflineParse (WellformedParse tr wire_digest) cb))
    = OfflineTranscript (op_transcript_digest ops tr) wire_digest.
Proof. intros. unfold assess_validated. apply decide_transcript_evidence. Qed.

(* ================= 5. malformed-transcript separation ================= *)

(* the malformed branch never calls replay / decide / op_transcript_digest at
   all -- it is fully determined before `match src` inspects the wire's own
   parse result, so it does not depend on `ops` (or ANY of its fields) at
   all. *)
Theorem malformed_evidence_uses_only_wire_digest :
  forall ops ti ac fuel reason wire_digest cb,
    outcome_transcript_evidence
      (assess_validated ops ti (ValidCampaign ac fuel)
        (OfflineParse (MalformedParse reason wire_digest) cb))
    = MalformedTranscript reason wire_digest.
Proof. reflexivity. Qed.

Theorem malformed_assess_indep_of_transcript_digest :
  forall ops g ti ac fuel reason wire_digest cb,
    assess_validated (set_transcript_digest ops g) ti (ValidCampaign ac fuel)
      (OfflineParse (MalformedParse reason wire_digest) cb)
    = assess_validated ops ti (ValidCampaign ac fuel)
      (OfflineParse (MalformedParse reason wire_digest) cb).
Proof. reflexivity. Qed.

(* the typed-transcript digest, where present -- None for the two evidence
   shapes that carry no typed digest at all. *)
Definition typed_digest_of (tev : transcript_evidence) : option digest :=
  match tev with
  | LiveCapture d => Some d
  | OfflineTranscript d _ => Some d
  | MalformedTranscript _ _ => None
  | NoTranscript => None
  end.

Lemma malformed_no_typed_digest : forall reason wire_digest,
  typed_digest_of (MalformedTranscript reason wire_digest) = None.
Proof. reflexivity. Qed.

(* ================= 6. live/offline agreement on the typed digest ================= *)

(* for the SAME typed transcript, live and well-formed-offline evidence carry
   the SAME typed digest, regardless of the offline wire digest -- NOT a claim
   that the two evidence VALUES are identical (offline properly carries the
   extra raw-wire digest too). *)
Theorem live_offline_typed_digest_agree : forall ops tr wire_digest,
  typed_digest_of (LiveCapture (op_transcript_digest ops tr))
  = typed_digest_of (OfflineTranscript (op_transcript_digest ops tr) wire_digest).
Proof. reflexivity. Qed.

(* ================= 7. agreement with the normative denotation ================= *)

Section Normative.

(* stands for digest_v1("pcfw.exec_transcript.v1", to_cv(tr)) -- its concrete
   canonicaliser and SHA-256 realisation are F.3, exactly as for every other
   digest_v1 use in this codebase. *)
Variable transcript_digest_v1 : exec_transcript -> digest.

Theorem transcript_digest_v1_deterministic : forall tr1 tr2,
  tr1 = tr2 -> transcript_digest_v1 tr1 = transcript_digest_v1 tr2.
Proof. intros tr1 tr2 ->. reflexivity. Qed.

(* a PER-TRANSCRIPT agreement predicate -- deliberately NOT a blanket
   "forall tr" Section Hypothesis (that shape was the exact defect HELD twice
   this project: ManifestMatching.ti_policy_digest_truthful and
   CompletenessWellformed's revision-2 record_completeness_load_validated).
   Theorems needing correctness take `transcript_digest_agrees ops tr` as an
   explicit premise about the one transcript being assessed. *)
Definition transcript_digest_agrees (ops : primitive_ops) (tr : exec_transcript)
  : Prop :=
  op_transcript_digest ops tr = transcript_digest_v1 tr.

(* a NAMED universal contract for a host implementation to aim for -- NOT
   installed as an ambient hypothesis anywhere in this file. *)
Definition transcript_digest_implementation_valid (ops : primitive_ops) : Prop :=
  forall tr, transcript_digest_agrees ops tr.

Theorem live_evidence_digest_agrees :
  forall ops ti ac fuel tr cb,
    transcript_digest_agrees ops tr ->
    outcome_transcript_evidence
      (assess_validated ops ti (ValidCampaign ac fuel) (LiveTranscript tr cb))
    = LiveCapture (transcript_digest_v1 tr).
Proof.
  intros ops ti ac fuel tr cb Hagree.
  rewrite (live_evidence_uses_typed_transcript_digest ops ti ac fuel tr cb).
  unfold transcript_digest_agrees in Hagree. rewrite Hagree. reflexivity.
Qed.

Theorem offline_evidence_digest_agrees :
  forall ops ti ac fuel tr wire_digest cb,
    transcript_digest_agrees ops tr ->
    outcome_transcript_evidence
      (assess_validated ops ti (ValidCampaign ac fuel)
        (OfflineParse (WellformedParse tr wire_digest) cb))
    = OfflineTranscript (transcript_digest_v1 tr) wire_digest.
Proof.
  intros ops ti ac fuel tr wire_digest cb Hagree.
  rewrite (offline_evidence_uses_both_digests ops ti ac fuel tr wire_digest cb).
  unfold transcript_digest_agrees in Hagree. rewrite Hagree. reflexivity.
Qed.

End Normative.
