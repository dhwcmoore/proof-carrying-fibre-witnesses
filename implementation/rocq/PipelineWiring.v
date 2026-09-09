(** Pipeline wiring: a concrete [primitive_ops] whose stage-1, preflight, O3 and
    stage-2 members are all closed over the SAME committed context [C], and the
    theorems connecting O3 resolution to those actual operations.

    Reviewer decision (2026-09-06): keep the dimension-agnostic
    [Orchestration.resolved_context]; close both checkers over one [C] and prove
    a theorem linking O3 success to [C].

    - `wired_ops base` replaces exactly four members of `base` -- `op_stage1_check`
      (`Stage1Wrapper.op_stage1_wrapper C …`), `op_preflight`
      (`ContextResolution.preflight_check …`), `op_eval_o3`
      (`ContextResolution.eval_o3_check …`), `op_stage2_check`
      (`Stage2Adapter.adapter_stage2_check C rng`) -- with the other eleven
      carried from `base`.

    - `wired_ops_op_stage1_sound` / `wired_ops_stage2_index_contract`: the two
      `primitive_ops` obligations the orchestration proofs assume.

    - `wiring_resolution_consistent`: when the wired `op_preflight` and
      `op_eval_o3` succeed (with the committed policy), `ContextResolution.resolve`
      yields exactly `(C, rc)`, and both `op_stage1_check` and `op_stage2_check`
      of `wired_ops` are the `C`-closed checkers. Stage 1 (which `replay` runs
      before O3) uses `C` unconditionally; O3 success resolves to that same `C`.

    - `wired_run_stage1_pending_invariant`: every element of
      `stage1_run_pending (run_stage1 wired_ops … (authenticated_submissions ac)
      0 l0 [] [])` -- the pending list `replay` threads unchanged into its
      stage-2 phase (Orchestration.v 6.5) -- satisfies `pending_invariant C`.
    - `wired_c_recheck_redundant`: for such a candidate, `op_stage2_check
      wired_ops` equals the mapped `stage2_check C rng …` -- the adapter's
      C-recheck never fires.

    Explicit outstanding obligations (this unit does NOT establish them):
    - the policy `replay` supplies to `op_eval_o3` is `p_committed`
      (`wiring_resolution_consistent` is specialised to `p_committed`; the actual
      replay path must be shown to use the committed policy -- a `valid_campaign`
      / manifest-binding property);
    - `committed_context_wf` (loaded bytes realise `C`), digest truthfulness,
      `lower_parse` / `parse_literal` conformance;
    - the eleven inherited members of `base` -- `wired_ops` does not establish
      their correctness. *)

From Coq Require Import Bool List ZArith.
From Coq Require Vector.
From PCFW Require Import FibreWitnessKernel Orchestration Stage2 Stage2Adapter
  Stage1 Stage1Invariant Stage1Wrapper ContextResolution.
Import ListNotations.

Set Implicit Arguments.

Section Wiring.
Context {n_in n_pre n_obs : nat}.
Variable C : AuditContext n_in n_pre n_obs.
Variable rng : Vec Z n_obs -> bool.

(* stage-1 wrapper F.3 inputs *)
Variable token : Type.
Variable lower_parse :
  verifier_config -> policy_document -> candidate_submission ->
  (b_reason + (list token * list token)).
Variable parse_literal : token -> option Z.
Variable semantic_digest_of : parsed_candidate -> digest.

(* context-resolution F.3 inputs *)
Variable p_committed : policy.
Variable digest_eqb : digest -> digest -> bool.
Variable model_digest_of preproc_digest_of inference_digest_of : bytes -> digest.
Variable parse_descriptor : digest -> option descriptor.
Variable probe_of_spec : bytes -> option (Vec Z n_pre * Vec Z n_obs).

(* the eleven other primitive_ops members. *)
Variable base : primitive_ops.

Definition wired_stage1 :=
  op_stage1_wrapper C lower_parse parse_literal semantic_digest_of.
Definition wired_stage2 := adapter_stage2_check C rng.
Definition wired_preflight :=
  preflight_check digest_eqb model_digest_of preproc_digest_of inference_digest_of
    parse_descriptor.
Definition wired_eval_o3 :=
  @eval_o3_check n_pre n_obs probe_of_spec.
Definition wired_resolve :=
  @resolve n_in n_pre n_obs C p_committed digest_eqb
    model_digest_of preproc_digest_of inference_digest_of
    parse_descriptor probe_of_spec.

Definition wired_ops : primitive_ops :=
  mkPrimitiveOps
    (op_parse_commitment base) (op_signer_authorised base) (op_signature_valid base)
    (op_manifest_policy_matches base) (op_manifest_audit_matches base)
    (op_manifest_context_matches base) (op_ledger_mismatch base)
    (op_record_identity_mismatch base) (op_completeness_wellformed base)
    wired_stage1 wired_preflight wired_eval_o3 wired_stage2
    (op_record_crosscheck base) (op_transcript_digest base).

(* ----- field projections (all by construction) ----- *)

Lemma wired_op_stage1 : op_stage1_check wired_ops = wired_stage1.
Proof. reflexivity. Qed.
Lemma wired_op_stage2 : op_stage2_check wired_ops = wired_stage2.
Proof. reflexivity. Qed.
Lemma wired_op_preflight : op_preflight wired_ops = wired_preflight.
Proof. reflexivity. Qed.
Lemma wired_op_eval_o3 : op_eval_o3 wired_ops = wired_eval_o3.
Proof. reflexivity. Qed.

(* ----- the two primitive_ops obligations ----- *)

Theorem wired_ops_op_stage1_sound : op_stage1_sound C wired_ops.
Proof. eapply wrapper_op_stage1_sound. exact wired_op_stage1. Qed.

Theorem wired_ops_stage2_index_contract : stage2_witness_index_contract wired_ops.
Proof. eapply adapter_satisfies_index_contract. exact wired_op_stage2. Qed.

(* ----- O3 resolution is connected to the actual operations ----- *)

Theorem wiring_resolution_consistent :
  forall lc ev pf o3f rc,
    op_preflight wired_ops lc = PreflightOk pf ->
    op_eval_o3 wired_ops lc ev p_committed = O3Ok rc o3f ->
    wired_resolve lc ev = Some (C, rc) /\
    op_stage1_check wired_ops = wired_stage1 /\
    op_stage2_check wired_ops = wired_stage2.
Proof.
  intros lc ev pf o3f rc Hpf Ho3.
  rewrite wired_op_preflight in Hpf. unfold wired_preflight in Hpf.
  rewrite wired_op_eval_o3 in Ho3. unfold wired_eval_o3 in Ho3.
  split; [| split; reflexivity].
  unfold wired_resolve, resolve.
  rewrite Hpf, Ho3. reflexivity.
Qed.

(* execution-order note: `replay` runs `run_stage1` (which calls
   `op_stage1_check wired_ops = wired_stage1`, closed over C) BEFORE it calls
   `op_preflight` / `op_eval_o3`.  So stage 1's context is C unconditionally;
   `wiring_resolution_consistent` then shows a *successful* O3 resolves to that
   same C.  Stage 1 never consumes an O3 result. *)

(* ----- the pending list `run_stage1` produces (which `replay` threads
   unchanged into its stage-2 phase, Orchestration.v 6.5) all satisfies the
   invariant, so the stage-2 C-recheck is redundant on each ----- *)

Corollary wired_run_stage1_pending_invariant :
  forall ac cfg pd p l0 q,
    In q (stage1_run_pending
            (run_stage1 wired_ops cfg pd p (authenticated_submissions ac) 0 l0 [] [])) ->
    Stage1Invariant.pending_invariant C q.
Proof.
  intros ac cfg pd p l0 q Hq.
  eapply Stage1Invariant.run_stage1_all_pending_invariant;
    [ exact wired_ops_op_stage1_sound | exact Hq ].
Qed.

Corollary wired_c_recheck_redundant :
  forall q, Stage1Invariant.pending_invariant C q ->
  forall rc cfg tr,
    exists x y,
      parse_vec n_in (candidate_x (pending_candidate q)) = Some x /\
      parse_vec n_in (candidate_y (pending_candidate q)) = Some y /\
      op_stage2_check wired_ops rc cfg tr q =
        match stage2_check C rng (fuel_ok cfg) x y
                (slot_at tr (pending_index q) XRole 0)
                (slot_at tr (pending_index q) XRole 1)
                (slot_at tr (pending_index q) YRole 0)
                (slot_at tr (pending_index q) YRole 1) with
        | S2Obstructed f =>
            mk_result q (WitnessCheckObstructed (o_reason_of_fail f))
        | S2NotWitness => mk_result q (S2NotAWitness QuantisedObservationsDiffer)
        | S2Valid o_x o_y => mk_result q (ValidWitness (mk_witness q x y o_x o_y))
        end.
Proof.
  intros q Hq rc cfg tr. rewrite wired_op_stage2. unfold wired_stage2.
  apply Stage1Invariant.adapter_c_recheck_redundant. exact Hq.
Qed.

End Wiring.
