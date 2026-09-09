(** Adapter: the kernel-facing [Stage2.stage2_check] as an
    [Orchestration.op_stage2_check].

    It parses the orchestration's [list Z] carriers into the kernel's
    [Vec Z n], re-establishes the stage-1 facts C1/C2/C3/C5 locally (a
    Phase-1-complete [stage1_check] would carry these forward), computes the O6d
    per-candidate fuel predicate from [cfg], runs [Stage2.stage2_check], and maps
    the verdict back.

    Boundary conditions (Coq predicates that CONDITION the conformance theorem;
    the adapter does NOT enforce them at runtime -- connecting them to stage 1,
    the parser and capture is an outstanding integration obligation):
    - [adapter_candidate_wf ps]: the pending candidate's x and y each have
      length [n_in].  To be established by stage-1 tier B4 (a wrongly-sized
      candidate is [S1Rejected InputStructureError], never [Pending]).  The
      total function's fallback for a violation returns
      [WitnessCheckObstructed ExecFailure]; [adapter_reporting_conformance]
      proves it is not reached under [adapter_candidate_wf].
    - [transcript_stage2_wf]: a present stage-2 event has vectors at their
      declared lengths.  To be established by the atomic [parse_transcript]
      (offline) or by construction in [capture] (live).  [slot_of_event] maps a
      violation to [None]; [slot_at_wf_none_iff] shows that under the condition
      [slot_at = None] iff [lookup_unique = None] (no unique event: absent or
      duplicated).

    Proved here:
    - [adapter_satisfies_index_contract]: any [primitive_ops] whose
      [op_stage2_check] is this adapter satisfies
      [Orchestration.stage2_witness_index_contract] (the premise the repaired
      REP1 theorem carries).
    - [adapter_valid_supplies_checked_witness]: a [ValidWitness] result exposes
      kernel vectors x y o_x o_y with [CheckedWitness].
    - [adapter_valid_observation_binding]: [ObservationBinding] for x and y
      follows *conditionally* on transcript faithfulness for the two "0"-repeat
      events -- never established by the adapter. *)

From Coq Require Import Bool List Vector ZArith Arith.
From PCFW Require Import FibreWitnessKernel Orchestration Stage2.
Import ListNotations.

Set Implicit Arguments.

(* ----- list Z  <->  Vec Z n ----- *)

Definition parse_vec (n : nat) (l : list Z) : option (Vec Z n) :=
  match Nat.eq_dec (length l) n with
  | left H => Some (eq_rect (length l) (Vec Z) (Vector.of_list l) n H)
  | right _ => None
  end.

Lemma parse_vec_some : forall n l v, parse_vec n l = Some v -> length l = n.
Proof.
  intros n l v H. unfold parse_vec in H.
  destruct (Nat.eq_dec (length l) n) as [E|]; [ exact E | discriminate ].
Qed.

Lemma parse_vec_ok : forall n l, length l = n -> exists v, parse_vec n l = Some v.
Proof.
  intros n l H. unfold parse_vec.
  destruct (Nat.eq_dec (length l) n) as [E|NE]; [ eexists; reflexivity | contradiction ].
Qed.

(* ----- Stage2.stage2_fail  ->  Orchestration.o_reason ----- *)

Definition o_reason_of_fail (f : stage2_fail) : o_reason :=
  match f with
  | S2ExecMissing => ExecMissing
  | S2ExecInputMismatch => ExecInputMismatch
  | S2ExecFailure => ExecFailure
  | S2ExecFuelExhausted => ExecFuelExhausted
  | S2NonDeterministic => NonDeterministic
  | S2ObsOutOfRange => ObsOutOfRange
  end.

Section Adapter.
Context {n_in n_pre n_obs : nat}.
Variable C : AuditContext n_in n_pre n_obs.
Variable rng : Vec Z n_obs -> bool.

Notation P := (context_policy C).

(* one transcript event -> one kernel obs_slot; the input is kept on every
   outcome so O6b precedes O6c. *)
Definition slot_of_event (e : option exec_event) : obs_slot n_pre n_obs :=
  match e with
  | None => None                                   (* missing / duplicated key *)
  | Some ev =>
      match parse_vec n_pre (event_input ev) with
      | None => None                               (* transcript-wf violation *)
      | Some i =>
          match event_outcome ev with
          | ExecOk obs =>
              match parse_vec n_obs obs with
              | Some o => Some (OeOk i o)
              | None => None                       (* transcript-wf violation *)
              end
          | ExecFailed _ => Some (OeFailed i)
          | ExecExhausted => Some (OeExhausted i)
          end
      end
  end.

Definition s2_key (idx : nat) (r : call_role) (rep : nat) : call_key :=
  mkCallKey (Stage2Phase idx) r rep.

Definition slot_at (tr : exec_transcript) (idx : nat) (r : call_role) (rep : nat)
  : obs_slot n_pre n_obs :=
  slot_of_event (lookup_unique tr (s2_key idx r rep)).

(* O6d: 4 * model_call_fuel <= max_fuel_per_candidate *)
Definition fuel_ok (cfg : verifier_config) : bool :=
  Nat.leb (4 * model_call_fuel cfg) (max_fuel_per_candidate cfg).

Definition mk_witness (ps : pending_submission)
  (x y : Vec Z n_in) (o_x o_y : Vec Z n_obs) : witness_data :=
  mkWitnessData (pending_index ps)
    (pending_submission_digest ps) (pending_semantic_digest ps)
    (Vector.to_list x) (Vector.to_list y)
    (Vector.to_list o_x) (Vector.to_list o_y) [].

Definition mk_result (ps : pending_submission) (v : stage2_verdict) : stage2_result :=
  mkStage2Result (pending_index ps) v [].

Definition adapter_stage2_check
  (rc : resolved_context) (cfg : verifier_config)
  (tr : exec_transcript) (ps : pending_submission) : stage2_result :=
  match parse_vec n_in (candidate_x (pending_candidate ps)),
        parse_vec n_in (candidate_y (pending_candidate ps)) with
  | Some x, Some y =>
      if negb (domainb P x) then mk_result ps (S2NotAWitness XNotInDomain)
      else if negb (domainb P y) then mk_result ps (S2NotAWitness YNotInDomain)
      else if veqb x y then mk_result ps (S2NotAWitness InputsEqual)
      else if Bool.eqb (target P x) (target P y)
           then mk_result ps (S2NotAWitness TargetsAgree)
      else
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
        end
  | _, _ =>
      (* unreachable under adapter_candidate_wf (stage-1 tier B4) *)
      mk_result ps (WitnessCheckObstructed ExecFailure)
  end.

(* ============ boundary conditions (hypotheses, not runtime checks) ============ *)

(* Candidate dimensional well-formedness -- to be established by the concrete
   stage-1 checker (tier B4 parses x and y to exactly n_in Z values, else
   S1Rejected InputStructureError; a Pending submission satisfies this). *)
Definition adapter_candidate_wf (ps : pending_submission) : Prop :=
  length (candidate_x (pending_candidate ps)) = n_in /\
  length (candidate_y (pending_candidate ps)) = n_in.

(* Event dimensional well-formedness. *)
Definition event_dims_ok (ev : exec_event) : Prop :=
  length (event_input ev) = n_pre /\
  (forall obs, event_outcome ev = ExecOk obs -> length obs = n_obs).

(* A present stage-2 event at (idx, r, rep) has well-formed dimensions -- to be
   established by the offline parse_transcript (atomic: a Wellformed transcript
   rejects any wrong-length vector) or, for a live capture, by construction
   (capture emits typed Vec inputs, so wrong length is not representable). *)
Definition slot_present_wf (tr : exec_transcript) (idx : nat)
  (r : call_role) (rep : nat) : Prop :=
  forall ev, lookup_unique tr (s2_key idx r rep) = Some ev -> event_dims_ok ev.

Definition transcript_stage2_wf (tr : exec_transcript) (idx : nat) : Prop :=
  slot_present_wf tr idx XRole 0 /\ slot_present_wf tr idx XRole 1 /\
  slot_present_wf tr idx YRole 0 /\ slot_present_wf tr idx YRole 1.

Lemma slot_at_wf_none_iff :
  forall tr idx r rep,
    slot_present_wf tr idx r rep ->
    (slot_at tr idx r rep = None <->
     lookup_unique tr (s2_key idx r rep) = None).
Proof.
  intros tr idx r rep Hwf. unfold slot_at, slot_of_event.
  destruct (lookup_unique tr (s2_key idx r rep)) as [ev|] eqn:Hlu.
  - specialize (Hwf ev Hlu). destruct Hwf as [Hin Hobs].
    destruct (parse_vec_ok _ Hin) as [i Hi]. rewrite Hi.
    destruct (event_outcome ev) as [obs| |] eqn:Ho.
    + destruct (parse_vec_ok _ (Hobs obs eq_refl)) as [o Hoo]. rewrite Hoo.
      split; discriminate.
    + split; discriminate.
    + split; discriminate.
  - split; reflexivity.
Qed.

Lemma adapter_candidate_wf_parses :
  forall ps, adapter_candidate_wf ps ->
    exists x y,
      parse_vec n_in (candidate_x (pending_candidate ps)) = Some x /\
      parse_vec n_in (candidate_y (pending_candidate ps)) = Some y.
Proof.
  intros ps [Hx Hy].
  destruct (parse_vec_ok _ Hx) as [x Hxp].
  destruct (parse_vec_ok _ Hy) as [y Hyp].
  exists x, y. split; assumption.
Qed.

(* ---- the C-rechecks yield Stage1Evidence ---- *)

Lemma bool_eqb_false_neq : forall a b : bool, Bool.eqb a b = false -> a <> b.
Proof. intros [] [] H; simpl in H; try discriminate; congruence. Qed.

Lemma adapter_valid_shape :
  forall rc cfg tr ps w,
    s2_verdict (adapter_stage2_check rc cfg tr ps) = ValidWitness w ->
    exists x y o_x o_y,
      parse_vec n_in (candidate_x (pending_candidate ps)) = Some x /\
      parse_vec n_in (candidate_y (pending_candidate ps)) = Some y /\
      Stage1Evidence C x y /\
      stage2_check C rng (fuel_ok cfg) x y
        (slot_at tr (pending_index ps) XRole 0)
        (slot_at tr (pending_index ps) XRole 1)
        (slot_at tr (pending_index ps) YRole 0)
        (slot_at tr (pending_index ps) YRole 1) = S2Valid o_x o_y /\
      w = mk_witness ps x y o_x o_y.
Proof.
  intros rc cfg tr ps w H. unfold adapter_stage2_check in H.
  destruct (parse_vec n_in (candidate_x (pending_candidate ps))) as [x|] eqn:Ex;
    [| destruct (parse_vec n_in (candidate_y (pending_candidate ps)));
       cbn in H; discriminate ].
  destruct (parse_vec n_in (candidate_y (pending_candidate ps))) as [y|] eqn:Ey;
    [| cbn in H; discriminate ].
  destruct (negb (domainb P x)) eqn:Dx; [ cbn in H; discriminate |].
  destruct (negb (domainb P y)) eqn:Dy; [ cbn in H; discriminate |].
  destruct (veqb x y) eqn:Vxy; [ cbn in H; discriminate |].
  destruct (Bool.eqb (target P x) (target P y)) eqn:Txy;
    [ cbn in H; discriminate |].
  destruct (stage2_check C rng (fuel_ok cfg) x y
              (slot_at tr (pending_index ps) XRole 0)
              (slot_at tr (pending_index ps) XRole 1)
              (slot_at tr (pending_index ps) YRole 0)
              (slot_at tr (pending_index ps) YRole 1))
    as [f| |o_x o_y] eqn:Sc; cbn in H; try discriminate.
  injection H as Hw.
  exists x, y, o_x, o_y.
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { constructor.
    - apply negb_false_iff in Dx. exact Dx.
    - apply negb_false_iff in Dy. exact Dy.
    - intro He. subst y. rewrite veqb_refl in Vxy. discriminate.
    - apply bool_eqb_false_neq. exact Txy. }
  split; [ exact Sc |].
  symmetry. exact Hw.
Qed.

(* ----- (2) the index contract ----- *)

Lemma adapter_index_preserved :
  forall rc cfg tr ps w,
    s2_verdict (adapter_stage2_check rc cfg tr ps) = ValidWitness w ->
    witness_index w = pending_index ps.
Proof.
  intros rc cfg tr ps w H.
  destruct (adapter_valid_shape _ _ _ _ H)
    as (x & y & o_x & o_y & _ & _ & _ & _ & ->).
  reflexivity.
Qed.

Theorem adapter_satisfies_index_contract :
  forall ops,
    op_stage2_check ops = adapter_stage2_check ->
    stage2_witness_index_contract ops.
Proof.
  intros ops Hops. unfold stage2_witness_index_contract.
  intros rc cfg tr ps w H. rewrite Hops in H.
  exact (adapter_index_preserved _ _ _ _ H).
Qed.

(* ----- (3) a ValidWitness supplies CheckedWitness ----- *)

Theorem adapter_valid_supplies_checked_witness :
  forall rc cfg tr ps w,
    s2_verdict (adapter_stage2_check rc cfg tr ps) = ValidWitness w ->
    exists (x y : Vec Z n_in) (o_x o_y : Vec Z n_obs),
      parse_vec n_in (candidate_x (pending_candidate ps)) = Some x /\
      parse_vec n_in (candidate_y (pending_candidate ps)) = Some y /\
      witness_x w = Vector.to_list x /\
      witness_y w = Vector.to_list y /\
      witness_o_x w = Vector.to_list o_x /\
      witness_o_y w = Vector.to_list o_y /\
      CheckedWitness P x y o_x o_y.
Proof.
  intros rc cfg tr ps w H.
  destruct (adapter_valid_shape _ _ _ _ H)
    as (x & y & o_x & o_y & Ex & Ey & Hs1 & Hsc & Hw).
  exists x, y, o_x, o_y.
  subst w. cbn [mk_witness witness_x witness_y witness_o_x witness_o_y].
  split; [ exact Ex |]. split; [ exact Ey |].
  split; [ reflexivity |]. split; [ reflexivity |].
  split; [ reflexivity |]. split; [ reflexivity |].
  exact (stage2_valid_checked_witness (C:=C) rng (fuel_ok cfg)
           (slot_at tr (pending_index ps) XRole 0)
           (slot_at tr (pending_index ps) XRole 1)
           (slot_at tr (pending_index ps) YRole 0)
           (slot_at tr (pending_index ps) YRole 1)
           Hs1 Hsc).
Qed.

(* ----- (4) observation binding, conditional on transcript faithfulness ----- *)

Definition transcript_faithful_for (tr : exec_transcript) (idx : nat) : Prop :=
  slot_faithful C (slot_at tr idx XRole 0) /\
  slot_faithful C (slot_at tr idx YRole 0).

Theorem adapter_valid_observation_binding :
  forall rc cfg tr ps w x y o_x o_y,
    s2_verdict (adapter_stage2_check rc cfg tr ps) = ValidWitness w ->
    parse_vec n_in (candidate_x (pending_candidate ps)) = Some x ->
    parse_vec n_in (candidate_y (pending_candidate ps)) = Some y ->
    witness_o_x w = Vector.to_list o_x ->
    witness_o_y w = Vector.to_list o_y ->
    transcript_faithful_for tr (pending_index ps) ->
    ObservationBinding C x o_x /\ ObservationBinding C y o_y.
Proof.
  intros rc cfg tr ps w x y o_x o_y H Ex Ey Hox Hoy [HfX HfY].
  destruct (adapter_valid_shape _ _ _ _ H)
    as (x' & y' & o_x' & o_y' & Ex' & Ey' & _ & Hsc & Hw).
  rewrite Ex in Ex'; injection Ex' as <-.
  rewrite Ey in Ey'; injection Ey' as <-.
  subst w. cbn [mk_witness witness_o_x witness_o_y] in Hox, Hoy.
  apply Vector.to_list_inj in Hox. apply Vector.to_list_inj in Hoy.
  subst o_x' o_y'.
  exact (stage2_valid_observation_binding C rng (fuel_ok cfg) x y
           (slot_at tr (pending_index ps) XRole 0)
           (slot_at tr (pending_index ps) XRole 1)
           (slot_at tr (pending_index ps) YRole 0)
           (slot_at tr (pending_index ps) YRole 1)
           Hsc HfX HfY).
Qed.

(* ----- (5) reporting conformance, PROVED UNDER the boundary conditions ----- *)

Theorem adapter_reporting_conformance :
  forall rc cfg tr ps,
    adapter_candidate_wf ps ->
    transcript_stage2_wf tr (pending_index ps) ->
    (* (a) the candidate-parse fallback branch is not taken *)
    (exists x y,
       parse_vec n_in (candidate_x (pending_candidate ps)) = Some x /\
       parse_vec n_in (candidate_y (pending_candidate ps)) = Some y) /\
    (* (b) ExecMissing is reported only when a stage-2 key has no unique event
       (absent or duplicated) -- a present, uniquely-keyed but malformed event
       never yields ExecMissing here *)
    (s2_verdict (adapter_stage2_check rc cfg tr ps)
       = WitnessCheckObstructed ExecMissing ->
     lookup_unique tr (s2_key (pending_index ps) XRole 0) = None \/
     lookup_unique tr (s2_key (pending_index ps) XRole 1) = None \/
     lookup_unique tr (s2_key (pending_index ps) YRole 0) = None \/
     lookup_unique tr (s2_key (pending_index ps) YRole 1) = None).
Proof.
  intros rc cfg tr ps Hcwf Htwf.
  destruct (adapter_candidate_wf_parses Hcwf) as (x & y & Hx & Hy).
  split; [ exists x, y; split; assumption |].
  intro Hverd. unfold adapter_stage2_check in Hverd.
  rewrite Hx, Hy in Hverd.
  destruct (negb (domainb P x)); [ cbn in Hverd; discriminate |].
  destruct (negb (domainb P y)); [ cbn in Hverd; discriminate |].
  destruct (veqb x y); [ cbn in Hverd; discriminate |].
  destruct (Bool.eqb (target P x) (target P y)); [ cbn in Hverd; discriminate |].
  destruct (stage2_check C rng (fuel_ok cfg) x y
              (slot_at tr (pending_index ps) XRole 0)
              (slot_at tr (pending_index ps) XRole 1)
              (slot_at tr (pending_index ps) YRole 0)
              (slot_at tr (pending_index ps) YRole 1))
    as [f| |o_x o_y] eqn:Sc; cbn in Hverd; try discriminate.
  injection Hverd as Hf. destruct f; cbn in Hf; try discriminate.
  destruct Htwf as (W0 & W1 & W2 & W3).
  destruct (stage2_check_missing_char C rng (fuel_ok cfg) x y
              (slot_at tr (pending_index ps) XRole 0)
              (slot_at tr (pending_index ps) XRole 1)
              (slot_at tr (pending_index ps) YRole 0)
              (slot_at tr (pending_index ps) YRole 1) Sc)
    as [Hm|[Hm|[Hm|Hm]]].
  - left. apply (proj1 (slot_at_wf_none_iff W0)). exact Hm.
  - right; left. apply (proj1 (slot_at_wf_none_iff W1)). exact Hm.
  - right; right; left. apply (proj1 (slot_at_wf_none_iff W2)). exact Hm.
  - right; right; right. apply (proj1 (slot_at_wf_none_iff W3)). exact Hm.
Qed.

End Adapter.
