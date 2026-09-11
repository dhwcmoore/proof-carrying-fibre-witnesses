(** F.3 stage-1 parser wrapper, and the discharge of [op_stage1_sound].

    [op_stage1_check] receives a raw [candidate_submission]; this wrapper wire-
    parses it (tiers B1a/B6/B1b/B1c/B2/B3 abstract, then B4 then B5 -- in that
    order) and, on success, runs [Stage1.stage1_semantic_check] under the
    committed context [C].

    Precedence: the semantic checker folds B4 with C1/C2/C3/C5; the full wire
    order is B4 -> B5 -> C1.  [wire_parse] checks the B4 dimension BEFORE the B5
    literal-representability check, so a candidate failing both is rejected with
    B4's [InputStructureError], not B5's [MalformedIntegerLiteral]
    ([wire_parse_B4_before_B5]).  Because [wire_parse] runs entirely before the
    semantic checker, B5 also precedes C1.

    Proved:
    - [wrapper_reject_not_pending]: a wire-parse rejection yields [S1Rejected],
      never [S1Pending].
    - [wrapper_pending_binds]: an [S1Pending] result records the wire-parsed
      candidate, the raw submission's [submission_digest], the semantic digest of
      that candidate, and the index -- exactly.
    - [wrapper_fields]: [s1_index] / [s1_submission_digest] / [s1_findings] are
      the index / raw digest / [[]]; on a successful parse [s1_verdict] is
      literally [stage1_semantic_check C ...].
    - [wrapper_op_stage1_sound]: any [primitive_ops] whose [op_stage1_check] is
      this wrapper satisfies [Stage1Invariant.op_stage1_sound].

    Still F.3-external (this unit does not close them): that
    [submission_digest sub] is the true [digest_bytes_v1] of the wire bytes and
    [semantic_digest_of] the true [digest_v1] of the parsed candidate;
    [lower_parse]'s correctness for B1a/B6/B1b/B1c/B2/B3. *)

From Coq Require Import Bool List ZArith Arith.
From Coq Require Vector.
From PCFW Require Import FibreWitnessKernel Orchestration Stage2 Stage2Adapter
  Stage1 Stage1Invariant.
Import ListNotations.

Set Implicit Arguments.

Fixpoint list_map_option {A B} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | a :: l' =>
      match f a, list_map_option f l' with
      | Some b, Some l'' => Some (b :: l'')
      | _, _ => None
      end
  end.

Lemma list_map_option_length :
  forall {A B} (f : A -> option B) l l', list_map_option f l = Some l' ->
    length l' = length l.
Proof.
  induction l as [| a l IH]; intros l' H; simpl in *.
  - injection H as <-. reflexivity.
  - destruct (f a); [| discriminate].
    destruct (list_map_option f l) eqn:E; [| discriminate].
    injection H as <-. simpl. f_equal. apply IH. reflexivity.
Qed.

Section Wrapper.
Context {n_in n_pre n_obs : nat}.
Variable C : AuditContext n_in n_pre n_obs.

(* the coordinate-token type produced by the structural parse (opaque). *)
Variable token : Type.

(* B1a/B6/B1b/B1c/B2/B3: structural wire parse to two coordinate token lists,
   or a b_reason.  Abstract -- the F.3 parser. *)
Variable lower_parse :
  verifier_config -> policy_document -> candidate_submission ->
  (b_reason + (list token * list token)).

(* B5: one integer literal -> Z within its declared integer_type, or None. *)
Variable parse_literal : token -> option Z.

(* the semantic candidate digest (digest_v1 "pcfw.candidate.v1" (to_cv c)). *)
Variable semantic_digest_of : parsed_candidate -> digest.

(* the parsed candidate_id wire field (VERDICT_SEMANTICS.md 4.1).  [digest] is a
   [Notation] for [string] (Orchestration); [String] is not imported here to
   avoid the [List]/[String] [length] collision. *)
Variable candidate_id_of : candidate_submission -> digest.

Inductive wire_result :=
| WireReject (r : b_reason)
| WireOk (c : parsed_candidate).

Definition wire_parse (cfg : verifier_config) (pd : policy_document)
  (sub : candidate_submission) : wire_result :=
  match lower_parse cfg pd sub with
  | inl r => WireReject r                                     (* B1a/B6/B1b/B1c/B2/B3 *)
  | inr (xs, ys) =>
      if andb (Nat.eqb (length xs) n_in) (Nat.eqb (length ys) n_in)
      then match list_map_option parse_literal xs,
                 list_map_option parse_literal ys with
           | Some xz, Some yz => WireOk (mkParsedCandidate (candidate_id_of sub) xz yz)
           | _, _ => WireReject MalformedIntegerLiteral       (* B5 *)
           end
      else WireReject InputStructureError                     (* B4 *)
  end.

Definition op_stage1_wrapper
  (cfg : verifier_config) (pd : policy_document) (p : policy)
  (i : nat) (sub : candidate_submission) : stage1_result :=
  let sd := submission_digest sub in
  match wire_parse cfg pd sub with
  | WireReject r => mkStage1Result i sd None None (S1Rejected r) []
  | WireOk c =>
      mkStage1Result i sd (Some (pc_candidate_id c)) (Some (semantic_digest_of c))
        (stage1_semantic_check C sd (semantic_digest_of c) i c) []
  end.

(* ----- ordering: B4 dimension check dominates B5 ----- *)

Theorem wire_parse_B4_before_B5 :
  forall cfg pd sub xs ys,
    lower_parse cfg pd sub = inr (xs, ys) ->
    (length xs <> n_in \/ length ys <> n_in) ->
    wire_parse cfg pd sub = WireReject InputStructureError.
Proof.
  intros cfg pd sub xs ys Hlp Hbad. unfold wire_parse. rewrite Hlp.
  destruct (Nat.eqb (length xs) n_in) eqn:Ex.
  - destruct (Nat.eqb (length ys) n_in) eqn:Ey.
    + apply Nat.eqb_eq in Ex, Ey.
      destruct Hbad as [H|H]; exfalso; [ apply H; exact Ex | apply H; exact Ey ].
    + reflexivity.
  - reflexivity.
Qed.

(* ----- (1) parse failure -> rejection, never pending ----- *)

Theorem wrapper_reject_not_pending :
  forall cfg pd p i sub r,
    wire_parse cfg pd sub = WireReject r ->
    op_stage1_wrapper cfg pd p i sub
      = mkStage1Result i (submission_digest sub) None None (S1Rejected r) [].
Proof.
  intros cfg pd p i sub r H. unfold op_stage1_wrapper. rewrite H. reflexivity.
Qed.

Corollary wrapper_reject_verdict :
  forall cfg pd p i sub r,
    wire_parse cfg pd sub = WireReject r ->
    s1_verdict (op_stage1_wrapper cfg pd p i sub) = S1Rejected r.
Proof.
  intros cfg pd p i sub r H. unfold op_stage1_wrapper. rewrite H. reflexivity.
Qed.

(* ----- (3) field preservation ----- *)

Theorem wrapper_fields :
  forall cfg pd p i sub,
    s1_index (op_stage1_wrapper cfg pd p i sub) = i /\
    s1_submission_digest (op_stage1_wrapper cfg pd p i sub) = submission_digest sub /\
    s1_findings (op_stage1_wrapper cfg pd p i sub) = [] /\
    (forall c, wire_parse cfg pd sub = WireOk c ->
       s1_verdict (op_stage1_wrapper cfg pd p i sub)
       = stage1_semantic_check C (submission_digest sub) (semantic_digest_of c) i c).
Proof.
  intros cfg pd p i sub. unfold op_stage1_wrapper.
  destruct (wire_parse cfg pd sub) as [r | c] eqn:Hw; cbn;
    repeat split; try reflexivity;
    intros c0 Hc0; try discriminate.
  injection Hc0 as <-. reflexivity.
Qed.

(* ----- (2) successful parse binds candidate + both digests to the raw sub ----- *)

Theorem wrapper_pending_binds :
  forall cfg pd p i sub ps,
    s1_verdict (op_stage1_wrapper cfg pd p i sub) = S1Pending ps ->
    exists c,
      wire_parse cfg pd sub = WireOk c /\
      pending_candidate ps = c /\
      pending_submission_digest ps = submission_digest sub /\
      pending_semantic_digest ps = semantic_digest_of c /\
      pending_index ps = i /\
      pending_findings ps = [].
Proof.
  intros cfg pd p i sub ps H. unfold op_stage1_wrapper in H.
  destruct (wire_parse cfg pd sub) as [r | c] eqn:Hw; cbn in H; [ discriminate |].
  exists c. split; [ reflexivity |].
  destruct (stage1_pending_identity _ _ _ _ _ H) as (Hc & Hi & Hsd & Hsemd & Hf).
  repeat split; assumption.
Qed.

(* a parsed candidate: [candidate_id] and [semantic_candidate_digest] are both
   [Some ...], bound to the raw sub (VERDICT_SEMANTICS.md 4.1). *)
Lemma wrapper_parsed_ids :
  forall cfg pd p i sub c,
    wire_parse cfg pd sub = WireOk c ->
    s1_candidate_id (op_stage1_wrapper cfg pd p i sub) = Some (pc_candidate_id c) /\
    s1_semantic_digest (op_stage1_wrapper cfg pd p i sub) = Some (semantic_digest_of c).
Proof.
  intros cfg pd p i sub c H. unfold op_stage1_wrapper. rewrite H.
  split; reflexivity.
Qed.

Lemma wrapper_reject_ids :
  forall cfg pd p i sub r,
    wire_parse cfg pd sub = WireReject r ->
    s1_candidate_id (op_stage1_wrapper cfg pd p i sub) = None /\
    s1_semantic_digest (op_stage1_wrapper cfg pd p i sub) = None.
Proof.
  intros cfg pd p i sub r H. unfold op_stage1_wrapper. rewrite H.
  split; reflexivity.
Qed.

(* ----- (4) discharge op_stage1_sound ----- *)

Theorem wrapper_op_stage1_sound :
  forall ops,
    op_stage1_check ops = op_stage1_wrapper ->
    op_stage1_sound C ops.
Proof.
  intros ops Hops. unfold op_stage1_sound.
  intros cfg pd p i sub ps H. rewrite Hops in H.
  unfold op_stage1_wrapper in H.
  destruct (wire_parse cfg pd sub) as [r | c] eqn:Hw; cbn in H; [ discriminate |].
  exact (stage1_pending_invariant C _ _ _ _ H).
Qed.

End Wrapper.
