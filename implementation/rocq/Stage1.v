(** Concrete stage-1 semantic checker (the B4 dimension check and C1/C2/C3/C5),
    connecting its [S1Pending] result to the hypotheses the stage-2 adapter
    carries:

    - [stage1_pending_candidate_wf]: a [Pending] submission satisfies
      [Stage2Adapter.adapter_candidate_wf] (x and y each have length n_in).
    - [stage1_pending_evidence]: a [Pending] submission's candidate parses to
      kernel vectors x, y with [Stage2.Stage1Evidence C x y] -- the premise
      [Stage2.stage2_valid_checked_witness] and the adapter's C-rechecks need.

    Precedence (frozen order B4 -> C1 -> C2 -> C3 -> C5,
    VERDICT_SEMANTICS.md 4.1 / AUDIT_POLICY_AND_EVIDENCE.md 6):
    - [stage1_reject_char]: each rejection reason is returned only when every
      earlier check passed.

    Wire-level tier B (B1a/B6/B1b/B1c/B2/B3/B5) is the F.3 parser's job and is
    out of scope here: this checker takes an already-parsed [parsed_candidate]
    ([list Z] x [list Z]) plus the two digests the wire layer computed. *)

From Coq Require Import Bool List ZArith.
From Coq Require Vector.
From PCFW Require Import FibreWitnessKernel Orchestration Stage2 Stage2Adapter.
Import ListNotations.

Set Implicit Arguments.

Section Stage1.
Context {n_in n_pre n_obs : nat}.
Variable C : AuditContext n_in n_pre n_obs.

Notation P := (context_policy C).

Definition stage1_semantic_check
  (sub_digest sem_digest : digest) (idx : nat) (c : parsed_candidate)
  : stage1_verdict :=
  match parse_vec n_in (candidate_x c), parse_vec n_in (candidate_y c) with
  | Some x, Some y =>
      if veqb x y then S1NotAWitness InputsEqual                 (* C1 *)
      else if negb (domainb P x) then S1NotAWitness XNotInDomain (* C2 *)
      else if negb (domainb P y) then S1NotAWitness YNotInDomain (* C3 *)
      else if Bool.eqb (target P x) (target P y)
           then S1NotAWitness TargetsAgree                       (* C5 *)
      else S1Pending (mkPendingSubmission idx sub_digest sem_digest c [])
  | _, _ => S1Rejected InputStructureError                       (* B4 *)
  end.

(* ----- helpers ----- *)

Lemma veqb_false_neq : forall (x y : Vec Z n_in), veqb x y = false -> x <> y.
Proof.
  intros x y H He. subst y. rewrite veqb_refl in H. discriminate.
Qed.

Lemma stage1_pending_parses :
  forall sd cd idx c ps,
    stage1_semantic_check sd cd idx c = S1Pending ps ->
    ps = mkPendingSubmission idx sd cd c [] /\
    exists x y,
      parse_vec n_in (candidate_x c) = Some x /\
      parse_vec n_in (candidate_y c) = Some y /\
      Stage1Evidence C x y.
Proof.
  intros sd cd idx c ps H. unfold stage1_semantic_check in H.
  destruct (parse_vec n_in (candidate_x c)) as [x|] eqn:Ex; [| discriminate ].
  destruct (parse_vec n_in (candidate_y c)) as [y|] eqn:Ey; [| discriminate ].
  destruct (veqb x y) eqn:Vxy; [ discriminate |].
  destruct (negb (domainb P x)) eqn:Dx; [ discriminate |].
  destruct (negb (domainb P y)) eqn:Dy; [ discriminate |].
  destruct (Bool.eqb (target P x) (target P y)) eqn:Txy; [ discriminate |].
  injection H as <-.
  split; [ reflexivity |].
  exists x, y. split; [ reflexivity |]. split; [ reflexivity |].
  constructor.
  - unfold InDomain. apply negb_false_iff in Dx. exact Dx.
  - unfold InDomain. apply negb_false_iff in Dy. exact Dy.
  - apply veqb_false_neq. exact Vxy.
  - exact (bool_eqb_false_neq Txy).
Qed.

(* ----- (1) identity preservation: the returned ps keeps the candidate, index
   AND the supplied digests exactly ----- *)

Theorem stage1_pending_identity :
  forall sd cd idx c ps,
    stage1_semantic_check sd cd idx c = S1Pending ps ->
    pending_candidate ps = c /\
    pending_index ps = idx /\
    pending_submission_digest ps = sd /\
    pending_semantic_digest ps = cd /\
    pending_findings ps = [].
Proof.
  intros sd cd idx c ps H.
  destruct (stage1_pending_parses _ _ _ _ H) as (-> & _).
  repeat split; reflexivity.
Qed.

(* ----- (2) adapter_candidate_wf ----- *)

Theorem stage1_pending_candidate_wf :
  forall sd cd idx c ps,
    stage1_semantic_check sd cd idx c = S1Pending ps ->
    @adapter_candidate_wf n_in ps.
Proof.
  intros sd cd idx c ps H.
  destruct (stage1_pending_parses _ _ _ _ H)
    as (-> & x & y & Ex & Ey & _).
  unfold adapter_candidate_wf. cbn [pending_candidate].
  split; [ exact (parse_vec_some _ Ex) | exact (parse_vec_some _ Ey) ].
Qed.

(* ----- (3) Stage1Evidence: x and y are exactly the vectors of the returned
   ps's candidate, under the same context C ----- *)

Theorem stage1_pending_evidence :
  forall sd cd idx c ps,
    stage1_semantic_check sd cd idx c = S1Pending ps ->
    pending_candidate ps = c /\
    exists x y,
      parse_vec n_in (candidate_x (pending_candidate ps)) = Some x /\
      parse_vec n_in (candidate_y (pending_candidate ps)) = Some y /\
      Stage1Evidence C x y.
Proof.
  intros sd cd idx c ps H.
  destruct (stage1_pending_parses _ _ _ _ H)
    as (Hps & x & y & Ex & Ey & Hev).
  assert (Hc : pending_candidate ps = c) by (rewrite Hps; reflexivity).
  split; [ exact Hc |].
  exists x, y. rewrite Hc. split; [ exact Ex |]. split; [ exact Ey | exact Hev ].
Qed.

(* ----- (4) C1/C2/C3/C5 rejection: [r] determines the branch (a [match] on the
   returned reason, so no exclusive-disjunction question arises); the earlier
   checks appear as conjuncts, giving the precedence.
   QuantisedObservationsDiffer / TargetsAgree distinct constructors etc. are
   Coq-level facts about [c_reason]. ----- *)

Theorem stage1_reject_char :
  forall sd cd idx c r,
    stage1_semantic_check sd cd idx c = S1NotAWitness r ->
    exists x y,
      parse_vec n_in (candidate_x c) = Some x /\
      parse_vec n_in (candidate_y c) = Some y /\
      match r with
      | InputsEqual => x = y
      | XNotInDomain => x <> y /\ ~ InDomain P x
      | YNotInDomain => x <> y /\ InDomain P x /\ ~ InDomain P y
      | TargetsAgree => x <> y /\ InDomain P x /\ InDomain P y
                        /\ target P x = target P y
      | QuantisedObservationsDiffer => False   (* stage 1 never returns this *)
      end.
Proof.
  intros sd cd idx c r H. unfold stage1_semantic_check in H.
  destruct (parse_vec n_in (candidate_x c)) as [x|] eqn:Ex; [| discriminate ].
  destruct (parse_vec n_in (candidate_y c)) as [y|] eqn:Ey; [| discriminate ].
  exists x, y. split; [ reflexivity |]. split; [ reflexivity |].
  destruct (veqb x y) eqn:Vxy.
  { injection H as <-. cbn. apply veqb_true. exact Vxy. }
  assert (Hxy : x <> y) by (apply veqb_false_neq; exact Vxy).
  destruct (negb (domainb P x)) eqn:Dx.
  { injection H as <-. cbn. split; [ exact Hxy |].
    unfold InDomain. apply negb_true_iff in Dx. rewrite Dx. discriminate. }
  apply negb_false_iff in Dx.
  destruct (negb (domainb P y)) eqn:Dy.
  { injection H as <-. cbn. split; [ exact Hxy |].
    split; [ unfold InDomain; exact Dx |].
    unfold InDomain. apply negb_true_iff in Dy. rewrite Dy. discriminate. }
  apply negb_false_iff in Dy.
  destruct (Bool.eqb (target P x) (target P y)) eqn:Txy.
  { injection H as <-. cbn. split; [ exact Hxy |].
    split; [ unfold InDomain; exact Dx |]. split; [ unfold InDomain; exact Dy |].
    exact (Bool.eqb_prop _ _ Txy). }
  discriminate.
Qed.

(* ----- (4) B4: malformed dimension -> InputStructureError, before any C-check ----- *)

Theorem stage1_dim_reject :
  forall sd cd idx c,
    (length (candidate_x c) <> n_in \/ length (candidate_y c) <> n_in) ->
    stage1_semantic_check sd cd idx c = S1Rejected InputStructureError.
Proof.
  intros sd cd idx c Hbad. unfold stage1_semantic_check.
  destruct (parse_vec n_in (candidate_x c)) as [x|] eqn:Ex.
  - destruct (parse_vec n_in (candidate_y c)) as [y|] eqn:Ey.
    + exfalso. destruct Hbad as [Hb|Hb];
        [ apply Hb; exact (parse_vec_some _ Ex)
        | apply Hb; exact (parse_vec_some _ Ey) ].
    + reflexivity.
  - reflexivity.
Qed.

End Stage1.
