(** Concrete [op_ledger_mismatch]: AUDIT_POLICY_AND_EVIDENCE.md 2.4 step 6 /
    VERDICT_SEMANTICS.md 5 step 7 --

      ti.M.submission_digests = map submission_digest ti.subs
      (element-wise, ordered, multiplicity kept).

    [ld_mismatch] walks the two digest lists in parallel and returns the LEAST
    index at which they disagree: either the first position whose elements differ,
    or -- if one list is a strict prefix of the other -- the length of the shorter
    list (the first length-divergence index).  [None] iff the lists are equal.

    [ledger_mismatch_impl] is parametric in the manifest decoder (the pipeline
    supplies [ManifestAuthentication.parse_manifest_impl]); a decode failure is
    reported as a mismatch at index 0 (there is no ledger to compare against).

    This is pure list bookkeeping.  No F.3 component is used here; the residual is
    the decoder passed in and, downstream, retrieval integrity (that the manifest
    and the submission list are this audit's). *)

From Coq Require Import List Bool Arith PeanoNat.
From PCFW Require Import Orchestration CanonicalV1.
Import ListNotations.

Section Ledger.

Variable digest_eqb : digest -> digest -> bool.
Hypothesis digest_eqb_true : forall a b, digest_eqb a b = true -> a = b.
Hypothesis digest_eqb_refl : forall a, digest_eqb a a = true.

(* least mismatch index, relative to the head of the given lists *)
Fixpoint ld_mismatch (xs ys : list digest) : option nat :=
  match xs, ys with
  | [], [] => None
  | [], _ :: _ => Some 0
  | _ :: _, [] => Some 0
  | x :: xs', y :: ys' =>
      if digest_eqb x y then option_map S (ld_mismatch xs' ys')
      else Some 0
  end.

Lemma ld_mismatch_none_eq : forall xs ys,
  ld_mismatch xs ys = None -> xs = ys.
Proof.
  induction xs as [| x xs' IH]; intros [| y ys'] H; cbn in H;
    try reflexivity; try discriminate.
  destruct (digest_eqb x y) eqn:D; [| discriminate].
  apply digest_eqb_true in D. subst y.
  destruct (ld_mismatch xs' ys') eqn:E; cbn in H; [ discriminate |].
  f_equal. apply IH. exact E.
Qed.

Lemma ld_mismatch_eq_none : forall xs, ld_mismatch xs xs = None.
Proof.
  induction xs as [| x xs' IH]; cbn; [ reflexivity |].
  rewrite digest_eqb_refl. rewrite IH. reflexivity.
Qed.

Lemma ld_mismatch_none_iff : forall xs ys,
  ld_mismatch xs ys = None <-> xs = ys.
Proof.
  intros xs ys. split.
  - apply ld_mismatch_none_eq.
  - intro E. subst ys. apply ld_mismatch_eq_none.
Qed.

(* [Some i]: the two lists agree on their first [i] elements and genuinely
   diverge at position [i] (different element, or one list ends there). *)
Lemma ld_mismatch_some_spec : forall xs ys i,
  ld_mismatch xs ys = Some i ->
  firstn i xs = firstn i ys /\ nth_error xs i <> nth_error ys i.
Proof.
  induction xs as [| x xs' IH]; intros [| y ys'] i H; cbn in H.
  - discriminate.
  - injection H as <-. cbn. split; [ reflexivity | discriminate ].
  - injection H as <-. cbn. split; [ reflexivity | discriminate ].
  - destruct (digest_eqb x y) eqn:D.
    + apply digest_eqb_true in D. subst y.
      destruct (ld_mismatch xs' ys') as [i'|] eqn:E; cbn in H; [| discriminate].
      injection H as <-.
      destruct (IH ys' i' E) as [Hpre Hdiv].
      cbn. rewrite Hpre. split; [ reflexivity | exact Hdiv ].
    + injection H as <-. cbn. split; [ reflexivity |].
      intro Heq. injection Heq as Heq.
      assert (digest_eqb x y = true) by (subst y; apply digest_eqb_refl).
      congruence.
Qed.

Definition ledger_mismatch_impl
  (parse : manifest -> option campaign_manifest_view)
  (M : manifest) (subs : list candidate_submission) : option nat :=
  match parse M with
  | None => Some 0
  | Some v =>
      ld_mismatch (cm_submission_digests v) (map submission_digest subs)
  end.

Lemma ledger_mismatch_impl_none_iff : forall parse M subs,
  ledger_mismatch_impl parse M subs = None <->
  exists v,
    parse M = Some v /\
    cm_submission_digests v = map submission_digest subs.
Proof.
  intros parse M subs. unfold ledger_mismatch_impl. split.
  - destruct (parse M) as [v|] eqn:E; [| discriminate].
    intro H. exists v. split; [ reflexivity |].
    apply ld_mismatch_none_iff. exact H.
  - intros (v & Hp & Heq). rewrite Hp.
    apply ld_mismatch_none_iff. exact Heq.
Qed.

(* a positive result really is a divergence, at the least index *)
Lemma ledger_mismatch_impl_some_spec : forall parse M subs v i,
  parse M = Some v ->
  ledger_mismatch_impl parse M subs = Some i ->
  firstn i (cm_submission_digests v) = firstn i (map submission_digest subs) /\
  nth_error (cm_submission_digests v) i <> nth_error (map submission_digest subs) i.
Proof.
  intros parse M subs v i Hp H. unfold ledger_mismatch_impl in H.
  rewrite Hp in H. apply ld_mismatch_some_spec. exact H.
Qed.

End Ledger.
