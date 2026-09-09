From Coq Require Import Bool Vector ZArith.

Set Implicit Arguments.

Definition Vec (A : Type) (n : nat) : Type := Vector.t A n.

(** A policy fixes every semantic choice needed by the kernel. The raw-input
    domain is Boolean so membership is decidable and extractable. Both the
    quantiser and target are total functions on dimension-indexed carriers. *)
Record Policy (n_in n_obs : nat) : Type := mkPolicy {
  domainb : Vec Z n_in -> bool;
  quantise : Vec Z n_obs -> Vec Z n_obs;
  target : Vec Z n_in -> bool
}.

Definition InDomain
  {n_in n_obs : nat} (P : Policy n_in n_obs) (x : Vec Z n_in) : Prop :=
  domainb P x = true.

(** Kernel witness over observations supplied to the kernel. There is no
    model, runner, transcript or execution-faithfulness premise here. *)
Definition CheckedWitness
  {n_in n_obs : nat} (P : Policy n_in n_obs)
  (x y : Vec Z n_in) (o_x o_y : Vec Z n_obs) : Prop :=
  InDomain P x /\
  InDomain P y /\
  x <> y /\
  quantise P o_x = quantise P o_y /\
  target P x <> target P y.

(** Fibre constancy is relative to an arbitrary observation function. *)
Definition FibreConstantObs
  {n_in n_obs : nat} (P : Policy n_in n_obs)
  (g : Vec Z n_in -> Vec Z n_obs) : Prop :=
  forall u v,
    InDomain P u ->
    InDomain P v ->
    quantise P (g u) = quantise P (g v) ->
    target P u = target P v.

(** (T1): a checked target-divergent quantised collision refutes fibre
    constancy for every observation function that realises the supplied
    observations at the two witness inputs. *)
Theorem T1_checked_witness_refutes_fibre_constancy :
  forall (n_in n_obs : nat) (P : Policy n_in n_obs)
         (x y : Vec Z n_in) (o_x o_y : Vec Z n_obs),
    CheckedWitness P x y o_x o_y ->
    forall g : Vec Z n_in -> Vec Z n_obs,
      g x = o_x ->
      g y = o_y ->
      ~ FibreConstantObs P g.
Proof.
  intros n_in n_obs P x y o_x o_y Hchecked g Hx Hy Hconstant.
  destruct Hchecked as [Hdomain_x [Hdomain_y [_ [Hquantised Htarget]]]].
  apply Htarget.
  apply (Hconstant x y Hdomain_x Hdomain_y).
  now rewrite Hx, Hy.
Qed.

(** A context adds the two functions that bind raw inputs to model
    observations. This is deliberately outside [Policy]. *)
Record AuditContext (n_in n_pre n_obs : nat) : Type := mkAuditContext {
  context_policy : Policy n_in n_obs;
  preproc : Vec Z n_in -> Vec Z n_pre;
  model : Vec Z n_pre -> Vec Z n_obs
}.

Definition observation
  {n_in n_pre n_obs : nat} (C : AuditContext n_in n_pre n_obs)
  (x : Vec Z n_in) : Vec Z n_obs :=
  model C (preproc C x).

Definition ObservationBinding
  {n_in n_pre n_obs : nat} (C : AuditContext n_in n_pre n_obs)
  (x : Vec Z n_in) (o : Vec Z n_obs) : Prop :=
  observation C x = o.

Definition FibreConstant
  {n_in n_pre n_obs : nat} (C : AuditContext n_in n_pre n_obs) : Prop :=
  FibreConstantObs (context_policy C) (observation C).

(** (A1): the system-level corollary. The two bindings are explicit premises;
    the kernel does not claim to establish them. *)
Corollary A1_bound_witness_refutes_context_fibre_constancy :
  forall (n_in n_pre n_obs : nat)
         (C : AuditContext n_in n_pre n_obs)
         (x y : Vec Z n_in) (o_x o_y : Vec Z n_obs),
    CheckedWitness (context_policy C) x y o_x o_y ->
    ObservationBinding C x o_x ->
    ObservationBinding C y o_y ->
    ~ FibreConstant C.
Proof.
  intros n_in n_pre n_obs C x y o_x o_y Hchecked Hx Hy.
  exact
    (@T1_checked_witness_refutes_fibre_constancy
       n_in n_obs (context_policy C) x y o_x o_y Hchecked
       (observation C) Hx Hy).
Qed.

