(** Concrete stage-2 witness checker, kernel-facing.

    Implements the stage-2 semantic checks in the frozen order
    O6a -> O6b -> O6c -> O6d -> O4 -> O5 -> C4
    (VERDICT_SEMANTICS.md 6.5 / AUDIT_POLICY_AND_EVIDENCE.md 6), and connects a
    successful check to FibreWitnessKernel:

    - [stage2_valid_checked_witness]: a [S2Valid] result plus the stage-1 facts
      (C1/C2/C3/C5) supplies [CheckedWitness].
    - [stage2_valid_observation_binding]: [ObservationBinding] for the two
      witness inputs follows *conditionally* on transcript faithfulness for the
      two acquired "0"-repeat events -- the F.3 residual assumption
      (CLAIM_AND_DEFINITIONS.md 3.2.2 / 5.2); the checker never establishes it.

    Event inputs are carried on every outcome (Ok, Failed, Exhausted), so O6b
    (input correctness) is checked *before* O6c (outcome success): a wrong input
    on a failed event is reported as [S2ExecInputMismatch], not a failure.

    [stage2_check] is a pure, extraction-friendly function; its [fuel_ok]
    argument is the O6d predicate [4 * model_call_fuel <= max_fuel_per_candidate]
    computed by the caller. *)

From Coq Require Import Bool List ZArith.
From Coq Require Vector.
From PCFW Require Import FibreWitnessKernel.
Import ListNotations.

Set Implicit Arguments.

(* ----- decidable vector equality (via to_list; extracts as plain list
   recursion, avoiding the Vector.eqb 't/t0' extraction wart) ----- *)

Fixpoint list_zeqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | nil, nil => true
  | a :: l1', b :: l2' => Z.eqb a b && list_zeqb l1' l2'
  | _, _ => false
  end.

Lemma list_zeqb_true_iff : forall l1 l2, list_zeqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [| a l1 IH]; intros [| b l2]; simpl; split;
    try discriminate; try reflexivity; intro H.
  - apply andb_true_iff in H as [Ha Hl]. apply Z.eqb_eq in Ha.
    apply IH in Hl. subst. reflexivity.
  - injection H as -> ->. apply andb_true_iff. split.
    + apply Z.eqb_eq. reflexivity.
    + apply IH. reflexivity.
Qed.

Definition veqb {n} (u v : Vec Z n) : bool :=
  list_zeqb (Vector.to_list u) (Vector.to_list v).

Lemma veqb_true_iff : forall n (u v : Vec Z n), veqb u v = true <-> u = v.
Proof.
  intros n u v. unfold veqb. rewrite list_zeqb_true_iff. split.
  - apply Vector.to_list_inj.
  - intros ->. reflexivity.
Qed.

Lemma veqb_true : forall n (u v : Vec Z n), veqb u v = true -> u = v.
Proof. intros n u v H. apply veqb_true_iff. exact H. Qed.

Lemma veqb_refl : forall n (u : Vec Z n), veqb u u = true.
Proof. intros n u. apply veqb_true_iff. reflexivity. Qed.

(* ----- the four keyed stage-2 execution events for one candidate.
   Every outcome carries its input. ----- *)

Inductive obs_event (n_pre n_obs : nat) : Type :=
| OeOk (input : Vec Z n_pre) (value : Vec Z n_obs)
| OeFailed (input : Vec Z n_pre)
| OeExhausted (input : Vec Z n_pre).
Arguments OeOk {n_pre n_obs}.
Arguments OeFailed {n_pre n_obs}.
Arguments OeExhausted {n_pre n_obs}.

(* [None] models a missing or duplicated key (lookup_unique = None). *)
Definition obs_slot (n_pre n_obs : nat) := option (obs_event n_pre n_obs).

Definition ev_input {n_pre n_obs} (e : obs_event n_pre n_obs) : Vec Z n_pre :=
  match e with OeOk i _ => i | OeFailed i => i | OeExhausted i => i end.

Definition ev_value {n_pre n_obs} (e : obs_event n_pre n_obs)
  : option (Vec Z n_obs) :=
  match e with OeOk _ v => Some v | _ => None end.

Definition ev_exhausted {n_pre n_obs} (e : obs_event n_pre n_obs) : bool :=
  match e with OeExhausted _ => true | _ => false end.

(* ----- stage-2 failure reasons (mapped 1:1 to Orchestration.o_reason by the
   adapter) and the verdict ----- *)

Inductive stage2_fail : Type :=
| S2ExecMissing | S2ExecInputMismatch | S2ExecFailure | S2ExecFuelExhausted
| S2NonDeterministic | S2ObsOutOfRange.

Inductive Stage2Verdict (n_obs : nat) : Type :=
| S2Obstructed (r : stage2_fail)
| S2NotWitness                       (* C4 failed: quantised observations differ *)
| S2Valid (o_x o_y : Vec Z n_obs).
Arguments S2Obstructed {n_obs}.
Arguments S2NotWitness {n_obs}.
Arguments S2Valid {n_obs}.

(* ----- the checker ----- *)

Section Check.
Context {n_in n_pre n_obs : nat}.
Variable C : AuditContext n_in n_pre n_obs.
Variable rng : Vec Z n_obs -> bool.       (* O5, expected_observation_range; policy-bound *)

Notation P := (context_policy C).

Definition stage2_check (fuel_ok : bool) (x y : Vec Z n_in)
  (eX0 eX1 eY0 eY1 : obs_slot n_pre n_obs) : Stage2Verdict n_obs :=
  match eX0, eX1, eY0, eY1 with               (* O6a: keys present *)
  | Some vX0, Some vX1, Some vY0, Some vY1 =>
      let px := preproc C x in
      let py := preproc C y in
      if negb (veqb (ev_input vX0) px && veqb (ev_input vX1) px
               && veqb (ev_input vY0) py && veqb (ev_input vY1) py)
      then S2Obstructed S2ExecInputMismatch                       (* O6b *)
      else match ev_value vX0, ev_value vX1, ev_value vY0, ev_value vY1 with
           | Some oX0, Some oX1, Some oY0, Some oY1 =>             (* O6c ok *)
               if negb fuel_ok
               then S2Obstructed S2ExecFuelExhausted              (* O6d *)
               else if negb (veqb oX0 oX1 && veqb oY0 oY1)
               then S2Obstructed S2NonDeterministic               (* O4  *)
               else if negb (rng oX0 && rng oY0)
               then S2Obstructed S2ObsOutOfRange                  (* O5  *)
               else if negb (veqb (quantise P oX0) (quantise P oY0))
               then S2NotWitness                                  (* C4  *)
               else S2Valid oX0 oY0
           | _, _, _, _ =>                                        (* O6c fail *)
               if ev_exhausted vX0 || ev_exhausted vX1
                  || ev_exhausted vY0 || ev_exhausted vY1
               then S2Obstructed S2ExecFuelExhausted
               else S2Obstructed S2ExecFailure
           end
  | _, _, _, _ => S2Obstructed S2ExecMissing                      (* O6a fail *)
  end.

(* ----- (3) a valid check supplies CheckedWitness ----- *)

Record Stage1Evidence (x y : Vec Z n_in) : Prop := mkStage1Evidence {
  s1e_x_domain : InDomain P x;
  s1e_y_domain : InDomain P y;
  s1e_distinct : x <> y;
  s1e_targets  : target P x <> target P y
}.

Lemma stage2_valid_forces :
  forall fuel_ok x y eX0 eX1 eY0 eY1 o_x o_y,
    stage2_check fuel_ok x y eX0 eX1 eY0 eY1 = S2Valid o_x o_y ->
    eX0 = Some (OeOk (preproc C x) o_x) /\
    eY0 = Some (OeOk (preproc C y) o_y) /\
    quantise P o_x = quantise P o_y.
Proof.
  intros fuel_ok x y eX0 eX1 eY0 eY1 o_x o_y H. unfold stage2_check in H.
  destruct eX0 as [vX0|], eX1 as [vX1|], eY0 as [vY0|], eY1 as [vY1|];
    try (cbn in H; discriminate).
  destruct (negb (veqb (ev_input vX0) (preproc C x)
                  && veqb (ev_input vX1) (preproc C x)
                  && veqb (ev_input vY0) (preproc C y)
                  && veqb (ev_input vY1) (preproc C y))) eqn:HO6b;
    [ discriminate |].
  destruct (ev_value vX0) as [oX0|] eqn:VX0,
           (ev_value vX1) as [oX1|] eqn:VX1,
           (ev_value vY0) as [oY0|] eqn:VY0,
           (ev_value vY1) as [oY1|] eqn:VY1;
  try (destruct (ev_exhausted vX0 || ev_exhausted vX1
                 || ev_exhausted vY0 || ev_exhausted vY1); discriminate).
  destruct (negb fuel_ok); [ discriminate |].
  destruct (negb (veqb oX0 oX1 && veqb oY0 oY1)); [ discriminate |].
  destruct (negb (rng oX0 && rng oY0)); [ discriminate |].
  destruct (negb (veqb (quantise P oX0) (quantise P oY0))) eqn:HC4;
    [ discriminate |].
  injection H as HoX HoY. subst oX0 oY0.
  apply negb_false_iff in HO6b.
  apply andb_true_iff in HO6b as [HO6b Hy1].
  apply andb_true_iff in HO6b as [HO6b Hy0].
  apply andb_true_iff in HO6b as [Hx0 Hx1].
  apply veqb_true in Hx0. apply veqb_true in Hy0.
  apply negb_false_iff in HC4. apply veqb_true in HC4.
  destruct vX0 as [iX0 vX0v | iX0 | iX0]; cbn in VX0, Hx0; try discriminate.
  destruct vY0 as [iY0 vY0v | iY0 | iY0]; cbn in VY0, Hy0; try discriminate.
  injection VX0 as HvX0. injection VY0 as HvY0.
  subst iX0 iY0 vX0v vY0v.
  split; [ reflexivity | split; [ reflexivity | exact HC4 ] ].
Qed.

Lemma stage2_valid_checked_witness :
  forall fuel_ok x y eX0 eX1 eY0 eY1 o_x o_y,
    Stage1Evidence x y ->
    stage2_check fuel_ok x y eX0 eX1 eY0 eY1 = S2Valid o_x o_y ->
    CheckedWitness P x y o_x o_y.
Proof.
  intros fuel_ok x y eX0 eX1 eY0 eY1 o_x o_y [Hxd Hyd Hne Htg] Hchk.
  destruct (stage2_valid_forces _ _ _ _ _ _ _ Hchk) as (_ & _ & HC4).
  unfold CheckedWitness. repeat split; assumption.
Qed.

(* ----- (4) observation binding, conditional on transcript faithfulness ----- *)

Definition slot_faithful (s : obs_slot n_pre n_obs) : Prop :=
  match s with Some (OeOk i o) => o = model C i | _ => True end.

Lemma stage2_valid_observation_binding :
  forall fuel_ok x y eX0 eX1 eY0 eY1 o_x o_y,
    stage2_check fuel_ok x y eX0 eX1 eY0 eY1 = S2Valid o_x o_y ->
    slot_faithful eX0 ->
    slot_faithful eY0 ->
    ObservationBinding C x o_x /\ ObservationBinding C y o_y.
Proof.
  intros fuel_ok x y eX0 eX1 eY0 eY1 o_x o_y Hchk HfX HfY.
  destruct (stage2_valid_forces _ _ _ _ _ _ _ Hchk) as (HX0 & HY0 & _).
  rewrite HX0 in HfX. rewrite HY0 in HfY. cbn in HfX, HfY.
  unfold ObservationBinding, observation.
  split; symmetry; assumption.
Qed.

(* ----- reporting conformance: S2ExecMissing is produced only by O6a (a slot
   that is genuinely None), never from within the all-present branch ----- *)

Lemma stage2_check_missing_char :
  forall fuel_ok x y s0 s1 s2 s3,
    stage2_check fuel_ok x y s0 s1 s2 s3 = S2Obstructed S2ExecMissing ->
    s0 = None \/ s1 = None \/ s2 = None \/ s3 = None.
Proof.
  intros fuel_ok x y s0 s1 s2 s3 H.
  destruct s0 as [v0|]; [| left; reflexivity ].
  destruct s1 as [v1|]; [| right; left; reflexivity ].
  destruct s2 as [v2|]; [| right; right; left; reflexivity ].
  destruct s3 as [v3|]; [| right; right; right; reflexivity ].
  exfalso. unfold stage2_check in H.
  destruct (negb (veqb (ev_input v0) (preproc C x)
                  && veqb (ev_input v1) (preproc C x)
                  && veqb (ev_input v2) (preproc C y)
                  && veqb (ev_input v3) (preproc C y)));
    [ discriminate |].
  destruct (ev_value v0), (ev_value v1), (ev_value v2), (ev_value v3);
    try (destruct (ev_exhausted v0 || ev_exhausted v1
                   || ev_exhausted v2 || ev_exhausted v3); discriminate).
  destruct (negb fuel_ok); [ discriminate |].
  destruct (negb (veqb _ _ && veqb _ _)); [ discriminate |].
  destruct (negb (rng _ && rng _)); [ discriminate |].
  destruct (negb (veqb (quantise P _) (quantise P _))); discriminate.
Qed.

End Check.
