(** Evidence preservation through orchestration.

    A per-submission invariant [pending_invariant C ps] -- the candidate of [ps]
    parses to kernel vectors with [Stage2.Stage1Evidence C x y] (hence
    [Stage2Adapter.adapter_candidate_wf ps]) -- is:

    1. established by a successful semantic stage 1 ([stage1_pending_invariant]);
    2. preserved by [run_stage1] for every pending submission it produces
       ([run_stage1_all_pending_invariant]), given the pending-output soundness
       contract [op_stage1_sound];
    3. the only aspect of [op_stage2_check] that [replay]'s result depends on:
       swapping [op_stage2_check] for one that agrees on invariant-satisfying
       submissions leaves [replay] unchanged ([replay_op_stage2_local]);
    4. sufficient for the stage-2 adapter's C-recheck to fall through -- its
       output is then determined entirely by [Stage2.stage2_check]
       ([adapter_c_recheck_redundant]).

    [op_stage1_sound] is a *pending-output soundness contract*: it asserts that
    every [S1Pending] verdict of [op_stage1_check] satisfies [pending_invariant].
    It does NOT compare [op_stage1_check] with [stage1_semantic_check] or
    establish parser correspondence. Its discharge -- via a parser wrapper that
    accounts for parse failure and binds the successful parse to the supplied
    submission and digests -- is an F.3 obligation, still open. An arbitrary
    [op_stage1_check] satisfies nothing.

    This unit discharges only the candidate / evidence hypotheses. It does not
    touch [transcript_stage2_wf], does not imply any stage-2 check succeeds, and
    changes no executable behaviour. *)

From Coq Require Import Bool List ZArith.
From Coq Require Vector.
From PCFW Require Import FibreWitnessKernel Orchestration Stage2 Stage2Adapter Stage1.
Import ListNotations.

Set Implicit Arguments.

Section Invariant.
Context {n_in n_pre n_obs : nat}.
Variable C : AuditContext n_in n_pre n_obs.
Variable rng : Vec Z n_obs -> bool.

Notation P := (context_policy C).

Definition pending_invariant (ps : pending_submission) : Prop :=
  exists x y,
    parse_vec n_in (candidate_x (pending_candidate ps)) = Some x /\
    parse_vec n_in (candidate_y (pending_candidate ps)) = Some y /\
    Stage1Evidence C x y.

Lemma pending_invariant_candidate_wf :
  forall ps, pending_invariant ps -> @adapter_candidate_wf n_in ps.
Proof.
  intros ps (x & y & Ex & Ey & _). unfold adapter_candidate_wf.
  split; [ exact (parse_vec_some _ Ex) | exact (parse_vec_some _ Ey) ].
Qed.

Lemma with_pending_index_invariant :
  forall i ps, pending_invariant ps -> pending_invariant (with_pending_index i ps).
Proof.
  intros i ps (x & y & Ex & Ey & Hev). unfold pending_invariant, with_pending_index.
  cbn [pending_candidate]. exists x, y. split; [ exact Ex |].
  split; [ exact Ey | exact Hev ].
Qed.

(* ----- (1) semantic stage 1 establishes it ----- *)

Theorem stage1_pending_invariant :
  forall sd cd idx c ps,
    stage1_semantic_check C sd cd idx c = S1Pending ps ->
    pending_invariant ps.
Proof.
  intros sd cd idx c ps H.
  destruct (stage1_pending_evidence _ _ _ _ _ H) as (_ & x & y & Ex & Ey & Hev).
  exists x, y. split; [ exact Ex |]. split; [ exact Ey | exact Hev ].
Qed.

(* ----- (2) run_stage1 preserves it ----- *)

(* Pending-output soundness contract (F.3-pending): every S1Pending verdict of
   op_stage1_check satisfies pending_invariant.  Not a comparison with
   stage1_semantic_check; discharged by a parser wrapper (open). *)
Definition op_stage1_sound (ops : primitive_ops) : Prop :=
  forall cfg pd p i sub ps,
    s1_verdict (op_stage1_check ops cfg pd p i sub) = S1Pending ps ->
    pending_invariant ps.

Lemma run_stage1_preserves_invariant :
  forall ops, op_stage1_sound ops ->
  forall subs cfg pd p i fuel slots_rev pending_rev,
    (forall q, In q pending_rev -> pending_invariant q) ->
    forall q,
      In q (stage1_run_pending
              (run_stage1 ops cfg pd p subs i fuel slots_rev pending_rev)) ->
      pending_invariant q.
Proof.
  intros ops Hsound subs.
  induction subs as [| sub rest IH];
    intros cfg pd p i fuel slots_rev pending_rev Hpr q Hq.
  - cbn [run_stage1 stage1_run_pending] in Hq.
    apply Hpr. apply (proj2 (in_rev _ _)). exact Hq.
  - cbn [run_stage1] in Hq.
    destruct (charge fuel (stage1_cost cfg sub)) as [fuel' |] eqn:Hc.
    + destruct (pending_of_stage1 (op_stage1_check ops cfg pd p i sub))
        as [cand |] eqn:Hp.
      * assert (Hinv_cand : pending_invariant cand).
        { assert (Hv : s1_verdict (op_stage1_check ops cfg pd p i sub)
                       = S1Pending cand).
          { unfold pending_of_stage1 in Hp.
            destruct (s1_verdict (op_stage1_check ops cfg pd p i sub));
              try discriminate. injection Hp as <-. reflexivity. }
          exact (Hsound cfg pd p i sub cand Hv). }
        eapply IH; [| exact Hq ].
        intros q0 Hq0. cbn [In] in Hq0. destruct Hq0 as [Hq0 | Hq0].
        -- subst q0. apply with_pending_index_invariant. exact Hinv_cand.
        -- apply Hpr. exact Hq0.
      * eapply IH; [ exact Hpr | exact Hq ].
    + cbn [stage1_run_pending] in Hq.
      apply Hpr. apply (proj2 (in_rev _ _)). exact Hq.
Qed.

Theorem run_stage1_all_pending_invariant :
  forall ops, op_stage1_sound ops ->
  forall cfg pd p subs l0 q,
    In q (stage1_run_pending
            (run_stage1 ops cfg pd p subs 0 l0 [] [])) ->
    pending_invariant q.
Proof.
  intros ops Hsound cfg pd p subs l0 q Hq.
  eapply run_stage1_preserves_invariant; [ exact Hsound | | exact Hq ].
  intros q0 [].
Qed.

(* The stage-1 pending list `replay` computes (its `Stage1Complete` /
   `Stage1Stopped` `pending` field) -- every element satisfies the invariant.
   This is a list-level fact; `replay_op_stage2_local` below is the statement
   about `replay` itself. *)
Theorem run_stage1_stage2_list_invariant :
  forall ops, op_stage1_sound ops ->
  forall ac cfg pd p l0 q,
    In q (stage1_run_pending
            (run_stage1 ops cfg pd p (authenticated_submissions ac) 0 l0 [] [])) ->
    pending_invariant q.
Proof.
  intros ops Hsound ac cfg pd p l0 q Hq.
  eapply run_stage1_all_pending_invariant; [ exact Hsound | exact Hq ].
Qed.

(* ----- (3) replay reachability: `replay`'s result depends on op_stage2_check
   ONLY through its behaviour on invariant-satisfying pending submissions --
   proved as an equality of `replay` outputs when op_stage2_check is swapped
   for any operation that agrees on such submissions. ----- *)

Definition ops_eq_except_stage2 (ops ops' : primitive_ops) : Prop :=
  op_parse_commitment ops' = op_parse_commitment ops /\
  op_signer_authorised ops' = op_signer_authorised ops /\
  op_signature_valid ops' = op_signature_valid ops /\
  op_manifest_policy_matches ops' = op_manifest_policy_matches ops /\
  op_manifest_audit_matches ops' = op_manifest_audit_matches ops /\
  op_manifest_context_matches ops' = op_manifest_context_matches ops /\
  op_ledger_mismatch ops' = op_ledger_mismatch ops /\
  op_record_identity_mismatch ops' = op_record_identity_mismatch ops /\
  op_completeness_wellformed ops' = op_completeness_wellformed ops /\
  op_stage1_check ops' = op_stage1_check ops /\
  op_preflight ops' = op_preflight ops /\
  op_eval_o3 ops' = op_eval_o3 ops /\
  op_record_crosscheck ops' = op_record_crosscheck ops /\
  op_transcript_digest ops' = op_transcript_digest ops.

Lemma run_stage1_ops_eq :
  forall ops ops', ops_eq_except_stage2 ops ops' ->
  forall subs cfg pd p i fuel sr pr,
    run_stage1 ops cfg pd p subs i fuel sr pr
    = run_stage1 ops' cfg pd p subs i fuel sr pr.
Proof.
  intros ops ops' Hoe subs.
  induction subs as [| sub rest IH]; intros cfg pd p i fuel sr pr.
  - reflexivity.
  - cbn [run_stage1]. destruct (charge fuel (stage1_cost cfg sub)) as [fuel'|].
    + destruct Hoe as (_&_&_&_&_&_&_&_&_&Hs1&_).
      rewrite Hs1. rewrite IH. reflexivity.
    + reflexivity.
Qed.

Lemma run_stage2_ops_eq :
  forall ops ops',
    (forall rc' cfg' tr' ps, pending_invariant ps ->
       op_stage2_check ops rc' cfg' tr' ps = op_stage2_check ops' rc' cfg' tr' ps) ->
    forall pending rc cfg tr fuel sr,
      (forall ps, In ps pending -> pending_invariant ps) ->
      run_stage2 ops rc cfg tr pending fuel sr
      = run_stage2 ops' rc cfg tr pending fuel sr.
Proof.
  intros ops ops' Hagree pending.
  induction pending as [| ps rest IH]; intros rc cfg tr fuel sr Hinv.
  - reflexivity.
  - cbn [run_stage2]. destruct (charge fuel (4 * model_call_fuel cfg)) as [fuel'|].
    + rewrite (Hagree rc cfg tr ps (Hinv ps (or_introl eq_refl))).
      rewrite IH; [ reflexivity |].
      intros ps0 Hps0. apply Hinv. right. exact Hps0.
    + reflexivity.
Qed.

Theorem replay_op_stage2_local :
  forall ops ops',
    ops_eq_except_stage2 ops ops' ->
    op_stage1_sound ops ->
    (forall rc' cfg' tr' ps, pending_invariant ps ->
       op_stage2_check ops rc' cfg' tr' ps = op_stage2_check ops' rc' cfg' tr' ps) ->
    forall ac cb cfg pd p l0 tr,
      replay ops ac cb cfg pd p l0 tr = replay ops' ac cb cfg pd p l0 tr.
Proof.
  intros ops ops' Hoe Hsound Hagree ac cb cfg pd p l0 tr.
  assert (Hcc : op_record_crosscheck ops' = op_record_crosscheck ops)
    by (destruct Hoe as (_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
  assert (Hpf : op_preflight ops' = op_preflight ops)
    by (destruct Hoe as (_&_&_&_&_&_&_&_&_&_&H&_); exact H).
  assert (Ho3 : op_eval_o3 ops' = op_eval_o3 ops)
    by (destruct Hoe as (_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
  (* finish_replay agrees whenever s1/ctx/s2/fuel/clo agree *)
  assert (Hfin : forall s1 ctx s2 fuel clo,
    finish_replay ops ac cfg s1 ctx s2 fuel clo
    = finish_replay ops' ac cfg s1 ctx s2 fuel clo).
  { intros. unfold finish_replay. rewrite Hcc. reflexivity. }
  assert (Hr1 : run_stage1 ops cfg pd p (authenticated_submissions ac) 0 l0 [] []
              = run_stage1 ops' cfg pd p (authenticated_submissions ac) 0 l0 [] [])
    by (apply run_stage1_ops_eq; exact Hoe).
  unfold replay.
  rewrite Hr1.
  destruct (Nat.ltb (max_candidates cfg)
             (List.length (authenticated_submissions ac))).
  { apply Hfin. }
  destruct (run_stage1 ops' cfg pd p (authenticated_submissions ac) 0 l0 [] [])
    as [fuel s1 pending | fuel s1 pending] eqn:Hrun.
  2: { apply Hfin. }
  (* Stage1Complete: pending submissions satisfy the invariant *)
  assert (Hinv : forall ps, In ps pending -> pending_invariant ps).
  { intros ps Hps.
    assert (Hin : stage1_run_pending
      (run_stage1 ops cfg pd p (authenticated_submissions ac) 0 l0 [] []) = pending)
      by (rewrite Hr1; reflexivity).
    apply (run_stage1_all_pending_invariant Hsound cfg pd p
             (authenticated_submissions ac) l0 ps).
    rewrite Hin. exact Hps. }
  destruct pending as [| ps0 pend']; [ apply Hfin |].
  destruct cb as [| rn | lc]; [ apply Hfin | apply Hfin |].
  destruct (charge fuel (preflight_fuel (schedule cfg))) as [fuel1|];
    [| apply Hfin ].
  rewrite Hpf. destruct (op_preflight ops lc) as [rn fs | pf]; [ apply Hfin |].
  destruct (charge fuel1 (model_call_fuel cfg)) as [fuel2|]; [| apply Hfin ].
  destruct (lookup_unique tr (mkCallKey ContextProbe Probe 0)) as [ev|];
    [| apply Hfin ].
  rewrite Ho3. destruct (op_eval_o3 ops lc ev p) as [fs | rc o3f]; [ apply Hfin |].
  assert (Hr2 : run_stage2 ops rc cfg tr (ps0 :: pend') fuel2 []
              = run_stage2 ops' rc cfg tr (ps0 :: pend') fuel2 [])
    by (apply run_stage2_ops_eq; [ exact Hagree | exact Hinv ]).
  rewrite Hr2.
  destruct (run_stage2 ops' rc cfg tr (ps0 :: pend') fuel2 []) as [[s2 f3] clo].
  apply Hfin.
Qed.

(* ----- (4) under the invariant, the adapter's C-recheck is redundant:
   adapter_stage2_check's output is determined by stage2_check ----- *)

Theorem adapter_c_recheck_redundant :
  forall ps, pending_invariant ps ->
  forall rc cfg tr,
    exists x y,
      parse_vec n_in (candidate_x (pending_candidate ps)) = Some x /\
      parse_vec n_in (candidate_y (pending_candidate ps)) = Some y /\
      adapter_stage2_check C rng rc cfg tr ps =
        match stage2_check C rng (fuel_ok cfg) x y
                (slot_at tr (pending_index ps) XRole 0)
                (slot_at tr (pending_index ps) XRole 1)
                (slot_at tr (pending_index ps) YRole 0)
                (slot_at tr (pending_index ps) YRole 1) with
        | S2Obstructed f =>
            mk_result ps (WitnessCheckObstructed (o_reason_of_fail f))
        | S2NotWitness =>
            mk_result ps (S2NotAWitness QuantisedObservationsDiffer)
        | S2Valid o_x o_y =>
            mk_result ps (ValidWitness (mk_witness ps x y o_x o_y))
        end.
Proof.
  intros ps (x & y & Ex & Ey & [Hxd Hyd Hne Htg]) rc cfg tr.
  exists x, y. split; [ exact Ex |]. split; [ exact Ey |].
  unfold adapter_stage2_check. rewrite Ex, Ey.
  unfold InDomain in Hxd, Hyd.
  rewrite Hxd. cbn [negb].
  rewrite Hyd. cbn [negb].
  replace (veqb x y) with false
    by (symmetry; apply not_true_is_false; rewrite veqb_true_iff; exact Hne).
  replace (Bool.eqb (target P x) (target P y)) with false
    by (symmetry; apply not_true_is_false;
        intro Hb; apply Htg; apply Bool.eqb_prop; exact Hb).
  reflexivity.
Qed.

End Invariant.
