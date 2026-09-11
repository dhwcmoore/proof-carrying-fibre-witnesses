(** Concrete `op_record_crosscheck` (VERDICT_SEMANTICS.md 6.5):

      record_findings := crosscheck(ac.rec.recorded_results, stage1, stage2)
                      ++ crosscheck_budget(ac.rec.resource_budget, vcfg)

    The r13 identity representation is UNCHANGED: `CampaignRecord.campaign_record_view`,
    `parse_record_impl`, `record_identity_mismatch_impl` and
    `validate_campaign_record_agrees` are byte-identical.

    This module adds:
    - a FULLY TYPED `submission_check_result` view -- `scr_view` -- with the
      `outcome` decoded to a typed constructor (`scr_outcome_view`) carrying its
      `b_/c_/o_reason` payload, and `findings` decoded to `list finding`;
    - a typed `resource_budget_view`;
    - `parse_record_full_impl : campaign_record -> option campaign_record_full_view`.
      **The only proved decoder relation is the forward projection**
        parse_record_full_impl r = Some v  ->  parse_record_impl r = Some (rf_identity v)
      (`parse_record_full_impl_projects`).  The reverse does NOT hold -- r13's
      `skip_value` tolerates canonical bytes that the typed decoders reject (e.g.
      an unknown `resource_budget` key) -- so this is a one-way implication, not
      an equivalence.
    - `derive_expected` -- the per-submission results the replay actually
      produced.  A stage-1 `NotRun` slot, and a `S1Pending` submission whose
      stage-2 slot is `NotRun`, produce **no** `submission_check_result` (the
      schema, AUDIT_POLICY 2.2.5, has no `not_run` outcome and a mandatory
      `submission_digest`); those slots are FILTERED OUT.  `derive_expected` is
      therefore a filtered, order- and index-preserving projection of the
      stage-1 slot list (`derive_expected_indices`); a recorded result for a
      filtered slot is an extra entry and shows up as a length / index mismatch.
      Every derived result carries a mandatory `exp_digest : digest`.
    - `scr_agrees : scr_view -> expected_scr -> Prop` -- full field equality
      (index, digest, candidate_id, semantic digest, typed outcome, findings);
      `scr_matches_expected` is its Boolean decider, with the two-sided
      **`scr_matches_expected_true_iff`** : `scr_matches_expected r e = true`
      iff `scr_agrees r e`;
    - `crosscheck_impl` -- compares each recorded result against its
      replay-derived expectation, with the top-level
      **`crosscheck_impl_nil_iff`** :
        `crosscheck_impl rf s1 s2 = []  <->  Forall2 scr_agrees (rf_recorded rf) (derive_expected s1 s2)`
      -- it emits no `campaign_record_mismatch` finding iff every recorded
      result agrees, field for field, with its replay-derived expectation and
      the two lists have equal length and index order
      (T26: a recorded result inconsistent with the replay produces a finding);
    - `advisory_finding_ids` -- the closed 3-element identifier family
      (`budget_advisory`, `campaign_record_mismatch`, `campaign_record_undecodable`)
      that `record_crosscheck_impl` may emit into `replay_record_findings`,
      DISJOINT from the frozen stage `check_id` set; `record_crosscheck_impl_ids`
      proves every emitted finding's `check_id` is in it.  The governing-document
      erratum that authorises this family is
      `PHASE_1_ADVISORY_FINDING_IDS_ERRATUM.md` (pending reviewer concurrence);
    - `crosscheck_budget_impl` -- advisory (`rec.resource_budget` vs the
      effective `verifier_config`);
    - the **verdict-invariance** suite: `op_record_crosscheck`'s output lands only
      in `replay_record_findings`, which `decide` / `verdict_of` never read, so
      replacing `op_record_crosscheck` by ANY function leaves the campaign verdict
      unchanged (`assess_validated_verdict_indep_crosscheck`,
      `ManifestPipeline.pipeline_verdict_indep_of_crosscheck`).

    `op_completeness_wellformed` is out of scope here. *)

From Coq Require Import String Ascii List Bool Arith PeanoNat.
From PCFW Require Import Orchestration CanonicalV1 ManifestAuthentication
  CampaignRecord.
Import ListNotations.
Open Scope string_scope.

Notation SW := ManifestAuthentication.starts_with.
Notation PJS := ManifestAuthentication.parse_json_string.
Notation PDF := ManifestAuthentication.parse_digest_field.

(* ================= b_/c_/o_reason <-> lower_snake_case ================= *)

Fixpoint assoc_str {A} (l : list (string * A)) (k : string) : option A :=
  match l with
  | [] => None
  | (k', v) :: rest => if String.eqb k k' then Some v else assoc_str rest k
  end.

Definition b_reasons : list (string * b_reason) :=
  [("bundle_limit_exceeded", BundleLimitExceeded); ("invalid_utf8", InvalidUtf8);
   ("malformed_structure", MalformedStructure); ("duplicate_keys", DuplicateKeys);
   ("schema_unrecognised", SchemaUnrecognised);
   ("schema_version_mismatch", SchemaVersionMismatch);
   ("unknown_critical_field", UnknownCriticalField); ("override_field", OverrideField);
   ("policy_hash_mismatch", PolicyHashMismatch);
   ("input_structure_error", InputStructureError);
   ("malformed_integer_literal", MalformedIntegerLiteral)].
Definition c_reasons : list (string * c_reason) :=
  [("inputs_equal", InputsEqual); ("x_not_in_domain", XNotInDomain);
   ("y_not_in_domain", YNotInDomain);
   ("quantised_observations_differ", QuantisedObservationsDiffer);
   ("targets_agree", TargetsAgree)].
Definition o_reasons : list (string * o_reason) :=
  [("exec_missing", ExecMissing); ("exec_input_mismatch", ExecInputMismatch);
   ("exec_failure", ExecFailure); ("exec_fuel_exhausted", ExecFuelExhausted);
   ("non_deterministic", NonDeterministic); ("obs_out_of_range", ObsOutOfRange)].

Definition b_reason_eqb (a b : b_reason) : bool :=
  match a, b with
  | BundleLimitExceeded, BundleLimitExceeded | InvalidUtf8, InvalidUtf8
  | MalformedStructure, MalformedStructure | DuplicateKeys, DuplicateKeys
  | SchemaUnrecognised, SchemaUnrecognised
  | SchemaVersionMismatch, SchemaVersionMismatch
  | UnknownCriticalField, UnknownCriticalField | OverrideField, OverrideField
  | PolicyHashMismatch, PolicyHashMismatch
  | InputStructureError, InputStructureError
  | MalformedIntegerLiteral, MalformedIntegerLiteral => true
  | _, _ => false
  end.
Definition c_reason_eqb (a b : c_reason) : bool :=
  match a, b with
  | InputsEqual, InputsEqual | XNotInDomain, XNotInDomain
  | YNotInDomain, YNotInDomain
  | QuantisedObservationsDiffer, QuantisedObservationsDiffer
  | TargetsAgree, TargetsAgree => true
  | _, _ => false
  end.
Definition o_reason_eqb (a b : o_reason) : bool :=
  match a, b with
  | ExecMissing, ExecMissing | ExecInputMismatch, ExecInputMismatch
  | ExecFailure, ExecFailure | ExecFuelExhausted, ExecFuelExhausted
  | NonDeterministic, NonDeterministic | ObsOutOfRange, ObsOutOfRange => true
  | _, _ => false
  end.

Lemma b_reason_eqb_true : forall a b, b_reason_eqb a b = true -> a = b.
Proof. intros [] []; cbn; congruence. Qed.
Lemma c_reason_eqb_true : forall a b, c_reason_eqb a b = true -> a = b.
Proof. intros [] []; cbn; congruence. Qed.
Lemma o_reason_eqb_true : forall a b, o_reason_eqb a b = true -> a = b.
Proof. intros [] []; cbn; congruence. Qed.

Lemma b_reason_eqb_refl : forall a, b_reason_eqb a a = true.
Proof. intros []; reflexivity. Qed.
Lemma c_reason_eqb_refl : forall a, c_reason_eqb a a = true.
Proof. intros []; reflexivity. Qed.
Lemma o_reason_eqb_refl : forall a, o_reason_eqb a a = true.
Proof. intros []; reflexivity. Qed.

Definition check_outcome_eqb (a b : check_outcome) : bool :=
  match a, b with
  | Pass, Pass | Fail, Fail | NotEvaluated, NotEvaluated => true
  | _, _ => false
  end.
Lemma check_outcome_eqb_true : forall a b, check_outcome_eqb a b = true -> a = b.
Proof. intros [] []; cbn; congruence. Qed.
Lemma check_outcome_eqb_refl : forall a, check_outcome_eqb a a = true.
Proof. intros []; reflexivity. Qed.

Definition oeqb (a b : option string) : bool :=
  match a, b with
  | None, None => true
  | Some x, Some y => String.eqb x y
  | _, _ => false
  end.
Lemma oeqb_true : forall a b, oeqb a b = true -> a = b.
Proof.
  intros [x|] [y|] H; cbn in H; try discriminate; [| reflexivity].
  apply String.eqb_eq in H. now subst.
Qed.
Lemma oeqb_refl : forall a, oeqb a a = true.
Proof. intros [x|]; cbn; [ apply String.eqb_refl | reflexivity ]. Qed.

Definition finding_eqb (a b : finding) : bool :=
  String.eqb (finding_check_id a) (finding_check_id b)
  && check_outcome_eqb (finding_outcome a) (finding_outcome b)
  && oeqb (finding_reason a) (finding_reason b)
  && oeqb (finding_offending a) (finding_offending b).
Lemma finding_eqb_true : forall a b, finding_eqb a b = true -> a = b.
Proof.
  intros [i1 o1 r1 f1] [i2 o2 r2 f2] H. unfold finding_eqb in H. cbn in H.
  apply andb_true_iff in H as [H123 H4]. apply andb_true_iff in H123 as [H12 H3].
  apply andb_true_iff in H12 as [H1 H2].
  apply String.eqb_eq in H1. apply check_outcome_eqb_true in H2.
  apply oeqb_true in H3. apply oeqb_true in H4.
  now subst.
Qed.
Lemma finding_eqb_refl : forall a, finding_eqb a a = true.
Proof.
  intros [i o r f]. unfold finding_eqb; cbn.
  rewrite String.eqb_refl, check_outcome_eqb_refl, !oeqb_refl. reflexivity.
Qed.

Fixpoint findings_eqb (a b : list finding) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => finding_eqb x y && findings_eqb a' b'
  | _, _ => false
  end.
Lemma findings_eqb_true : forall a b, findings_eqb a b = true -> a = b.
Proof.
  induction a as [| x a' IH]; intros [| y b'] H; cbn in H;
    try discriminate; [ reflexivity |].
  apply andb_true_iff in H as [H1 H2]. apply finding_eqb_true in H1.
  apply IH in H2. now subst.
Qed.
Lemma findings_eqb_refl : forall a, findings_eqb a a = true.
Proof.
  induction a as [| x a' IH]; cbn; [ reflexivity |].
  rewrite finding_eqb_refl, IH. reflexivity.
Qed.

(* ================= typed views ================= *)

(* The four decodable `submission_check_result` outcomes.  There is deliberately
   NO `not_run` constructor: AUDIT_POLICY 2.2.5 gives no `not_run` outcome and a
   mandatory `submission_digest`, so a replay slot that did not produce a result
   is filtered out of `derive_expected`, not represented here. *)
Inductive scr_outcome_view :=
| ScrRejected (reason : b_reason)
| ScrValidWitness
| ScrNotAWitness (reason : c_reason)
| ScrObstructed (reason : o_reason).

Definition scr_outcome_view_eqb (a b : scr_outcome_view) : bool :=
  match a, b with
  | ScrRejected r1, ScrRejected r2 => b_reason_eqb r1 r2
  | ScrValidWitness, ScrValidWitness => true
  | ScrNotAWitness r1, ScrNotAWitness r2 => c_reason_eqb r1 r2
  | ScrObstructed r1, ScrObstructed r2 => o_reason_eqb r1 r2
  | _, _ => false
  end.
Lemma scr_outcome_view_eqb_true : forall a b,
  scr_outcome_view_eqb a b = true -> a = b.
Proof.
  intros [r1| |r1|r1] [r2| |r2|r2] H; cbn in H; try discriminate;
    try reflexivity.
  - apply b_reason_eqb_true in H; now subst.
  - apply c_reason_eqb_true in H; now subst.
  - apply o_reason_eqb_true in H; now subst.
Qed.
Lemma scr_outcome_view_eqb_refl : forall a, scr_outcome_view_eqb a a = true.
Proof.
  intros [r| |r|r]; cbn;
    [ apply b_reason_eqb_refl | reflexivity
    | apply c_reason_eqb_refl | apply o_reason_eqb_refl ].
Qed.

Record scr_view := mkScrView {
  scr_index        : nat;
  scr_digest       : digest;
  scr_candidate_id : option string;   (* replay-derived: the stage-1 result's s1_candidate_id *)
  scr_semantic     : option digest;
  scr_outcome      : scr_outcome_view;
  scr_findings     : list finding
}.

Record resource_budget_view := mkBudgetView {
  rb_max_candidates                       : option nat;
  rb_max_memory_bytes                     : option nat;
  rb_max_per_candidate_memory_bytes       : option nat;
  rb_max_per_candidate_wall_clock_seconds : option nat;
  rb_max_wall_clock_seconds               : option nat
}.
Definition empty_budget : resource_budget_view :=
  mkBudgetView None None None None None.

Record campaign_record_full_view := mkRecordFull {
  rf_identity : campaign_record_view;
  rf_recorded : list scr_view;
  rf_budget   : resource_budget_view
}.

(* ================= small canonical parsers ================= *)

Fixpoint nat_digits (s : string) (acc : nat) : nat * string :=
  match s with
  | String c r =>
      let n := nat_of_ascii c in
      if andb (Nat.leb 48 n) (Nat.leb n 57)
      then nat_digits r (acc * 10 + (n - 48))
      else (acc, s)
  | EmptyString => (acc, s)
  end.

Definition parse_nat (s : string) : option (nat * string) :=
  match s with
  | EmptyString => None
  | String c1 r1 =>
      let n1 := nat_of_ascii c1 in
      if Nat.eqb n1 48 then
        match r1 with
        | String c2 _ =>
            if andb (Nat.leb 48 (nat_of_ascii c2)) (Nat.leb (nat_of_ascii c2) 57)
            then None else Some (0, r1)
        | EmptyString => Some (0, r1)
        end
      else if andb (Nat.leb 49 n1) (Nat.leb n1 57) then
        Some (nat_digits r1 (n1 - 48))
      else None
  end.

(* the frozen closed check_id set (VERDICT_SEMANTICS.md 2). *)
Definition check_ids : list string :=
  ["B6";"B1a";"B1b";"B1c";"B2";"B3";"B4";"B5";
   "C1";"C2";"C3";"C5";"O1";"O2";"O3";"O6";"O4";"O5";"C4"].
Definition valid_check_id (s : string) : bool := existsb (String.eqb s) check_ids.

(* the raw canonical text a value occupies, plus the suffix *)
Definition capture_value (fuel : nat) (s : string) : option (string * string) :=
  match CampaignRecord.skip_value fuel s with
  | None => None
  | Some rest => Some (substring 0 (String.length s - String.length rest) s, rest)
  end.

(* ---- one `finding`: keys ascending  check_id, [offending], outcome, [reason].
   check_id must be in the frozen set; `offending`, if present, is captured as its
   raw canonical text and compared verbatim. ---- *)
Definition parse_finding (fuel : nat) (s : string) : option (finding * string) :=
  match SW "{""check_id"":" s with None => None | Some s1 =>
  match PJS s1 with None => None | Some (cid, s2) =>
  if negb (valid_check_id cid) then None else
  match (match SW ",""offending"":" s2 with
         | None => Some (None, s2)
         | Some sa =>
             match capture_value fuel sa with
             | Some (raw, sb) => Some (Some raw, sb)
             | None => None
             end
         end)
  with None => None | Some (off, s3) =>
  match SW ",""outcome"":" s3 with None => None | Some s4 =>
  match PJS s4 with None => None | Some (oc, s5) =>
  match (if String.eqb oc "pass" then Some Pass
         else if String.eqb oc "fail" then Some Fail
         else if String.eqb oc "not_evaluated" then Some NotEvaluated else None)
  with None => None | Some co =>
  let '(rsn, s6) :=
    match SW ",""reason"":" s5 with
    | Some sb => match PJS sb with Some (rv, sc) => (Some rv, sc) | None => (None, s5) end
    | None => (None, s5)
    end in
  match SW "}" s6 with
  | Some s7 => Some (mkFinding cid co rsn off, s7)
  | None => None
  end end end end end end end.

Fixpoint parse_finding_elems (fuel : nat) (s : string) (acc : list finding)
  : option (list finding * string) :=
  match fuel with
  | 0 => None
  | S f =>
      match parse_finding fuel s with
      | None => None
      | Some (e, s1) =>
          match s1 with
          | String c rest =>
              let n := nat_of_ascii c in
              if Nat.eqb n 93 then Some (List.rev (e :: acc), rest)
              else if Nat.eqb n 44 then parse_finding_elems f rest (e :: acc)
              else None
          | EmptyString => None
          end
      end
  end.

Definition parse_findings_array (fuel : nat) (s : string)
  : option (list finding * string) :=
  match s with
  | String c rest =>
      if Nat.eqb (nat_of_ascii c) 91 then
        match SW (String "]"%char "") rest with
        | Some rest2 => Some ([], rest2)
        | None => parse_finding_elems (S (String.length rest)) rest []
        end
      else None
  | EmptyString => None
  end.

(* ---- `outcome`:  {"k":"rejected","v":"<b_reason>"}
   or                {"k":"accepted","v":<witness_outcome>}
   where witness_outcome is  "valid_witness"
   or {"k":"not_a_witness","v":"<c_reason>"}
   or {"k":"witness_check_obstructed","v":"<o_reason>"} ---- *)
Definition parse_witness_outcome (s : string) : option (scr_outcome_view * string) :=
  match s with
  | EmptyString => None
  | String c _ =>
      if Nat.eqb (nat_of_ascii c) 34 then
        match PJS s with
        | Some (v, rest) =>
            if String.eqb v "valid_witness" then Some (ScrValidWitness, rest) else None
        | None => None
        end
      else if Nat.eqb (nat_of_ascii c) 123 then
        match SW "{""k"":" s with None => None | Some s1 =>
        match PJS s1 with None => None | Some (tag, s2) =>
        match SW ",""v"":" s2 with None => None | Some s3 =>
        match PJS s3 with None => None | Some (rn, s4) =>
        match SW "}" s4 with None => None | Some s5 =>
        if String.eqb tag "not_a_witness" then
          match assoc_str c_reasons rn with
          | Some cr => Some (ScrNotAWitness cr, s5) | None => None end
        else if String.eqb tag "witness_check_obstructed" then
          match assoc_str o_reasons rn with
          | Some orr => Some (ScrObstructed orr, s5) | None => None end
        else None
        end end end end end
      else None
  end.

Definition parse_scr_outcome (s : string) : option (scr_outcome_view * string) :=
  match SW "{""k"":" s with None => None | Some s1 =>
  match PJS s1 with None => None | Some (tag, s2) =>
  match SW ",""v"":" s2 with None => None | Some s3 =>
  if String.eqb tag "rejected" then
    match PJS s3 with None => None | Some (rn, s4) =>
    match assoc_str b_reasons rn with None => None | Some br =>
    match SW "}" s4 with Some s5 => Some (ScrRejected br, s5) | None => None
    end end end
  else if String.eqb tag "accepted" then
    match parse_witness_outcome s3 with None => None | Some (wo, s4) =>
    match SW "}" s4 with Some s5 => Some (wo, s5) | None => None
    end end
  else None
  end end end.

(* ---- one submission_check_result (canonical key order:
   candidate_id?, findings, outcome, semantic_candidate_digest?, submission_digest,
   submission_index) ---- *)
Definition parse_scr (fuel : nat) (s : string) : option (scr_view * string) :=
  match SW "{" s with None => None | Some s0 =>
  let '(cid, s1) :=
    match SW """candidate_id"":" s0 with
    | Some sa =>
        match PJS sa with
        | Some (v, sb) =>
            match SW "," sb with Some sc => (Some v, sc) | None => (None, s0) end
        | None => (None, s0)
        end
    | None => (None, s0)
    end in
  match SW """findings"":" s1 with None => None | Some sf =>
  match parse_findings_array fuel sf with None => None | Some (fds, sf2) =>
  match SW ",""outcome"":" sf2 with None => None | Some so =>
  match parse_scr_outcome so with None => None | Some (oc, so2) =>
  let '(semd, s2) :=
    match SW ",""semantic_candidate_digest"":" so2 with
    | Some sd0 => match PDF sd0 with Some (d, sd1) => (Some d, sd1) | None => (None, so2) end
    | None => (None, so2)
    end in
  match SW ",""submission_digest"":" s2 with None => None | Some sd2 =>
  match PDF sd2 with None => None | Some (subdig, sd3) =>
  match SW ",""submission_index"":" sd3 with None => None | Some si0 =>
  match parse_nat si0 with None => None | Some (idx, si1) =>
  match SW "}" si1 with
  | Some s3 => Some (mkScrView idx subdig cid semd oc fds, s3)
  | None => None
  end end end end end end end end end end.

Fixpoint parse_scr_elems (fuel : nat) (s : string) (acc : list scr_view)
  : option (list scr_view * string) :=
  match fuel with
  | 0 => None
  | S f =>
      match parse_scr fuel s with
      | None => None
      | Some (e, s1) =>
          match s1 with
          | String c rest =>
              let n := nat_of_ascii c in
              if Nat.eqb n 93 then Some (List.rev (e :: acc), rest)
              else if Nat.eqb n 44 then parse_scr_elems f rest (e :: acc)
              else None
          | EmptyString => None
          end
      end
  end.

Definition parse_recorded_array (fuel : nat) (s : string)
  : option (list scr_view * string) :=
  match s with
  | String c rest =>
      if Nat.eqb (nat_of_ascii c) 91 then
        match SW (String "]"%char "") rest with
        | Some rest2 => Some ([], rest2)
        | None => parse_scr_elems (S (String.length rest)) rest []
        end
      else None
  | EmptyString => None
  end.

(* ---- resource_budget: 0..5 known keys, strictly byte-ascending, dup-free ---- *)
Definition budget_key_rank (k : string) : option nat :=
  if String.eqb k "max_candidates" then Some 0
  else if String.eqb k "max_memory_bytes" then Some 1
  else if String.eqb k "max_per_candidate_memory_bytes" then Some 2
  else if String.eqb k "max_per_candidate_wall_clock_seconds" then Some 3
  else if String.eqb k "max_wall_clock_seconds" then Some 4
  else None.

Definition set_budget (k : string) (n : nat) (bv : resource_budget_view)
  : resource_budget_view :=
  if String.eqb k "max_candidates"
  then mkBudgetView (Some n) (rb_max_memory_bytes bv)
         (rb_max_per_candidate_memory_bytes bv)
         (rb_max_per_candidate_wall_clock_seconds bv) (rb_max_wall_clock_seconds bv)
  else if String.eqb k "max_memory_bytes"
  then mkBudgetView (rb_max_candidates bv) (Some n)
         (rb_max_per_candidate_memory_bytes bv)
         (rb_max_per_candidate_wall_clock_seconds bv) (rb_max_wall_clock_seconds bv)
  else if String.eqb k "max_per_candidate_memory_bytes"
  then mkBudgetView (rb_max_candidates bv) (rb_max_memory_bytes bv) (Some n)
         (rb_max_per_candidate_wall_clock_seconds bv) (rb_max_wall_clock_seconds bv)
  else if String.eqb k "max_per_candidate_wall_clock_seconds"
  then mkBudgetView (rb_max_candidates bv) (rb_max_memory_bytes bv)
         (rb_max_per_candidate_memory_bytes bv) (Some n) (rb_max_wall_clock_seconds bv)
  else mkBudgetView (rb_max_candidates bv) (rb_max_memory_bytes bv)
         (rb_max_per_candidate_memory_bytes bv)
         (rb_max_per_candidate_wall_clock_seconds bv) (Some n).

Fixpoint parse_budget_members (fuel : nat) (prev : option string)
  (bv : resource_budget_view) (s : string) : option (resource_budget_view * string) :=
  match fuel with
  | 0 => None
  | S f =>
      match PJS s with
      | None => None
      | Some (key, s1) =>
          match budget_key_rank key with
          | None => None
          | Some _ =>
            if match prev with
               | None => true
               | Some p => CampaignRecord.str_ltb p key
               end then
              match s1 with
              | String c s2 =>
                  if Nat.eqb (nat_of_ascii c) 58 then
                    match parse_nat s2 with
                    | None => None
                    | Some (n, s3) =>
                        let bv' := set_budget key n bv in
                        match s3 with
                        | String c3 s4 =>
                            if Nat.eqb (nat_of_ascii c3) 44
                            then parse_budget_members f (Some key) bv' s4
                            else if Nat.eqb (nat_of_ascii c3) 125
                            then Some (bv', s4)
                            else None
                        | EmptyString => None
                        end
                    end
                  else None
              | EmptyString => None
              end
            else None
          end
      end
  end.

Definition parse_budget_object (s : string)
  : option (resource_budget_view * string) :=
  match SW "{" s with
  | None => None
  | Some s0 =>
      match SW (String "}"%char "") s0 with
      | Some rest => Some (empty_budget, rest)
      | None => parse_budget_members (S (String.length s0)) None empty_budget s0
      end
  end.

(* ---- consume the identity prefix, exactly as [parse_record_impl] does, and
   return the suffix that begins at [,"recorded_results":] ---- *)
Definition skip_to_recorded (s : string) : option string :=
  let fuel := String.length s in
  match SW "{""audit_instance_id"":" s with None => None | Some s1 =>
  match PJS s1 with None => None | Some (_, s2) =>
  match SW ",""campaign_id"":" s2 with None => None | Some s3 =>
  match PJS s3 with None => None | Some (_, s4) =>
  match SW ",""completeness"":" s4 with None => None | Some s5 =>
  match CampaignRecord.skip_value fuel s5 with None => None | Some s6 =>
  match SW ",""context_digests"":{""inference_spec_digest"":" s6
  with None => None | Some s7 =>
  match PDF s7 with None => None | Some (_, s8) =>
  match SW ",""model_artifact_digest"":" s8 with None => None | Some s9 =>
  match PDF s9 with None => None | Some (_, s10) =>
  match SW ",""preprocessing_digest"":" s10 with None => None | Some s11 =>
  match PDF s11 with None => None | Some (_, s12) =>
  match SW "},""manifest_digest"":" s12 with None => None | Some s13 =>
  match PDF s13 with None => None | Some (_, s14) =>
  match SW ",""policy_hash"":" s14 with None => None | Some s15 =>
  match PDF s15 with None => None | Some (_, s16) => Some s16
  end end end end end end end end end end end end end end end end.

Definition extract_recorded_and_budget (s : string)
  : option (list scr_view * resource_budget_view) :=
  let fuel := String.length s in
  match skip_to_recorded s with None => None | Some s16 =>
  match SW ",""recorded_results"":" s16 with None => None | Some s17 =>
  match parse_recorded_array fuel s17 with None => None | Some (rs, s18) =>
  match SW ",""resource_budget"":" s18 with None => None | Some s19 =>
  match parse_budget_object s19 with None => None | Some (rb, s20) =>
  match SW "}" s20 with
  | Some EmptyString => Some (rs, rb)
  | _ => None
  end end end end end end.

(* [parse_record_impl]-first: on success, [parse_record_impl] accepted the same
   bytes (forward projection only -- the reverse is false, see the header). *)
Definition parse_record_full_impl (r : campaign_record)
  : option campaign_record_full_view :=
  match parse_record_impl r with
  | None => None
  | Some idv =>
      match extract_recorded_and_budget (record_token r) with
      | Some (rs, rb) => Some (mkRecordFull idv rs rb)
      | None => None
      end
  end.

Lemma parse_record_full_impl_projects : forall r v,
  parse_record_full_impl r = Some v -> parse_record_impl r = Some (rf_identity v).
Proof.
  intros r v H. unfold parse_record_full_impl in H.
  destruct (parse_record_impl r) as [idv|] eqn:E; [| discriminate].
  destruct (extract_recorded_and_budget (record_token r)) as [[rs rb]|] eqn:E2;
    [| discriminate].
  injection H as <-. cbn. reflexivity.
Qed.

(* ================= frozen normative vectors ================= *)

Definition full_record_scr_e : scr_view :=
  mkScrView 0 CanonicalV1.d64_b None None ScrValidWitness [].
Definition full_record_scr_f : scr_view :=
  mkScrView 1 CanonicalV1.d64_c None None (ScrNotAWitness InputsEqual)
    [mkFinding "C1" Fail (Some "inputs_equal") None].

Lemma parse_record_full_impl_vector :
  parse_record_full_impl (mkCampaignRecord CampaignRecord.full_record_vector_wire)
  = Some (mkRecordFull CampaignRecord.schema_valid_record
            [full_record_scr_e; full_record_scr_f]
            (mkBudgetView (Some 10) (Some 1024) None None None)).
Proof. vm_compute. reflexivity. Qed.

Lemma parse_record_full_impl_vector_projects :
  parse_record_impl (mkCampaignRecord CampaignRecord.full_record_vector_wire)
  = Some CampaignRecord.schema_valid_record.
Proof.
  pose proof (parse_record_full_impl_projects _ _ parse_record_full_impl_vector) as HP.
  cbn in HP. exact HP.
Qed.

Lemma parse_budget_object_rejects_descending :
  parse_budget_object "{""max_memory_bytes"":1,""max_candidates"":2}" = None.
Proof. vm_compute. reflexivity. Qed.
Lemma parse_budget_object_rejects_leading_zero :
  parse_budget_object "{""max_candidates"":01}" = None.
Proof. vm_compute. reflexivity. Qed.
Lemma parse_budget_object_rejects_unknown_key :
  parse_budget_object "{""max_wobble"":1}" = None.
Proof. vm_compute. reflexivity. Qed.

(* a canonical-JSON but schema-INVALID outcome (unknown reason) is rejected by
   the typed decoder -- so parse_record_full_impl is strictly more restrictive
   than parse_record_impl (the reverse projection is false). *)
Lemma parse_scr_outcome_rejects_unknown_reason :
  parse_scr_outcome "{""k"":""rejected"",""v"":""not_a_real_reason""}" = None.
Proof. vm_compute. reflexivity. Qed.

(* ================= the recorded-result crosscheck ================= *)

Definition mismatch_finding (detail : string) : finding :=
  mkFinding "campaign_record_mismatch" Fail (Some detail) None.
Definition budget_finding (outcome : check_outcome) (detail : string) : finding :=
  mkFinding "budget_advisory" outcome (Some detail) None.

(* the per-submission result the replay produced.  [candidate_id] and
   [semantic_candidate_digest] come from the stage-1 result's own option fields
   (VERDICT_SEMANTICS.md 4.1: [Some] for every parsed candidate, [None] on a
   parse rejection).  [exp_digest] is MANDATORY -- every emitted
   [submission_check_result] carries a [submission_digest] (AUDIT_POLICY 2.2.5). *)
Record expected_scr := mkExpectedScr {
  exp_index        : nat;
  exp_digest       : digest;
  exp_candidate_id : option string;
  exp_semantic     : option digest;
  exp_outcome      : scr_outcome_view;
  exp_findings     : list finding
}.

Definition s2_slot_at (s2 : list stage2_slot) (i : nat) : slot stage2_result :=
  match find (fun sl => Nat.eqb (stage2_slot_index sl) i) s2 with
  | Some sl => stage2_slot_result sl
  | None => NotRun
  end.

(* [None] for a replay slot that produced no [submission_check_result]:
   a stage-1 [NotRun] slot, or a [S1Pending] submission whose stage-2 slot is
   [NotRun].  Such a slot is omitted from [derive_expected] -- the campaign
   record must not carry a result for it. *)
Definition derive_one (s2 : list stage2_slot) (sl : stage1_slot)
  : option expected_scr :=
  match stage1_slot_result sl with
  | NotRun => None
  | Done r1 =>
      let idx := stage1_slot_index sl in
      let dg  := s1_submission_digest r1 in
      let cid := s1_candidate_id r1 in
      let sem := s1_semantic_digest r1 in
      let f1  := s1_findings r1 in
      match s1_verdict r1 with
      | S1Rejected reason =>
          Some (mkExpectedScr idx dg cid sem (ScrRejected reason) f1)
      | S1NotAWitness reason =>
          Some (mkExpectedScr idx dg cid sem (ScrNotAWitness reason) f1)
      | S1Pending p =>
          match s2_slot_at s2 idx with
          | NotRun => None
          | Done r2 =>
              match s2_verdict r2 with
              | ValidWitness w =>
                  Some (mkExpectedScr idx dg cid sem ScrValidWitness (f1 ++ witness_findings w))
              | S2NotAWitness reason =>
                  Some (mkExpectedScr idx dg cid sem (ScrNotAWitness reason) (f1 ++ s2_findings r2))
              | WitnessCheckObstructed reason =>
                  Some (mkExpectedScr idx dg cid sem (ScrObstructed reason) (f1 ++ s2_findings r2))
              end
          end
      end
  end.

Fixpoint derive_expected (s1 : list stage1_slot) (s2 : list stage2_slot)
  : list expected_scr :=
  match s1 with
  | [] => []
  | sl :: rest =>
      match derive_one s2 sl with
      | Some e => e :: derive_expected rest s2
      | None => derive_expected rest s2
      end
  end.

(* [derive_one] never changes the slot index. *)
Lemma derive_one_index : forall s2 sl e,
  derive_one s2 sl = Some e -> exp_index e = stage1_slot_index sl.
Proof.
  intros s2 sl e H. unfold derive_one in H.
  destruct (stage1_slot_result sl) as [r1|]; [| discriminate].
  destruct (s1_verdict r1) as [reason | reason | p].
  - injection H as <-; reflexivity.
  - injection H as <-; reflexivity.
  - destruct (s2_slot_at s2 (stage1_slot_index sl)) as [r2|]; [| discriminate].
    destruct (s2_verdict r2) as [reason | reason | w];
      injection H as <-; reflexivity.
Qed.

Definition slot_ran (s2 : list stage2_slot) (sl : stage1_slot) : bool :=
  match derive_one s2 sl with Some _ => true | None => false end.

(* the derived list is an order- and index-preserving projection of the stage-1
   slot list: it drops the non-run slots and keeps the rest, in order, each with
   its own slot index -- so a recorded result at a filtered slot appears as a
   length / index mismatch, never silently matched. *)
Lemma derive_expected_indices : forall s1 s2,
  map exp_index (derive_expected s1 s2)
  = map stage1_slot_index (List.filter (slot_ran s2) s1).
Proof.
  induction s1 as [| sl rest IH]; intros s2; cbn; [ reflexivity |].
  unfold slot_ran. destruct (derive_one s2 sl) as [e|] eqn:E; cbn.
  - rewrite (derive_one_index _ _ _ E), IH. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma derive_expected_length : forall s1 s2,
  Datatypes.length (derive_expected s1 s2) <= Datatypes.length s1.
Proof.
  induction s1 as [| sl rest IH]; intros s2; cbn; [ constructor |].
  destruct (derive_one s2 sl); cbn.
  - apply le_n_S, IH.
  - apply Nat.le_le_succ_r, IH.
Qed.

(* the recorded result, projected to its replay-derivable fields, must EQUAL the
   replay-derived expectation -- strict option equality for [candidate_id] and
   the semantic digest (an omitted recorded value where the replay has one IS a
   discrepancy), mandatory equality for [submission_digest]. *)
Definition scr_matches_expected (r : scr_view) (e : expected_scr) : bool :=
  Nat.eqb (scr_index r) (exp_index e)
  && String.eqb (scr_digest r) (exp_digest e)
  && oeqb (scr_candidate_id r) (exp_candidate_id e)
  && oeqb (scr_semantic r) (exp_semantic e)
  && scr_outcome_view_eqb (scr_outcome r) (exp_outcome e)
  && findings_eqb (scr_findings r) (exp_findings e).

(* the propositional relation that [scr_matches_expected] decides. *)
Definition scr_agrees (r : scr_view) (e : expected_scr) : Prop :=
  scr_index r = exp_index e
  /\ scr_digest r = exp_digest e
  /\ scr_candidate_id r = exp_candidate_id e
  /\ scr_semantic r = exp_semantic e
  /\ scr_outcome r = exp_outcome e
  /\ scr_findings r = exp_findings e.

(* full two-sided Boolean correspondence. *)
Theorem scr_matches_expected_true_iff : forall r e,
  scr_matches_expected r e = true <-> scr_agrees r e.
Proof.
  intros r e. unfold scr_matches_expected, scr_agrees. split.
  - intro H.
    apply andb_true_iff in H as [H1 Hf]. apply andb_true_iff in H1 as [H1 Ho].
    apply andb_true_iff in H1 as [H1 Hsem]. apply andb_true_iff in H1 as [H1 Hcid].
    apply andb_true_iff in H1 as [Hi Hd].
    apply Nat.eqb_eq in Hi. apply String.eqb_eq in Hd.
    apply oeqb_true in Hcid, Hsem.
    apply scr_outcome_view_eqb_true in Ho. apply findings_eqb_true in Hf.
    repeat split; assumption.
  - intros (Hi & Hd & Hcid & Hsem & Ho & Hf).
    rewrite Hi, Hd, Hcid, Hsem, Ho, Hf.
    rewrite Nat.eqb_refl, String.eqb_refl, !oeqb_refl,
            scr_outcome_view_eqb_refl, findings_eqb_refl.
    reflexivity.
Qed.

(* forward projection, kept under its own name (PrintStage2Assumptions references
   it) -- now one half of the [scr_matches_expected_true_iff] correspondence. *)
Lemma scr_matches_expected_fields : forall r e,
  scr_matches_expected r e = true ->
  scr_index r = exp_index e
  /\ scr_digest r = exp_digest e
  /\ scr_candidate_id r = exp_candidate_id e
  /\ scr_semantic r = exp_semantic e
  /\ scr_outcome r = exp_outcome e
  /\ scr_findings r = exp_findings e.
Proof. intros r e H. apply scr_matches_expected_true_iff in H. exact H. Qed.

Fixpoint crosscheck_list (rs : list scr_view) (exps : list expected_scr)
  : list finding :=
  match rs, exps with
  | [], [] => []
  | r :: rs', e :: exps' =>
      (if scr_matches_expected r e then [] else [mismatch_finding "recorded_result"])
      ++ crosscheck_list rs' exps'
  | _, _ => [mismatch_finding "recorded_result_count"]
  end.

Definition crosscheck_impl (rf : campaign_record_full_view)
  (s1 : list stage1_slot) (s2 : list stage2_slot) : list finding :=
  crosscheck_list (rf_recorded rf) (derive_expected s1 s2).

(* supporting Boolean form. *)
Theorem crosscheck_impl_nil_iff_bool : forall rf s1 s2,
  crosscheck_impl rf s1 s2 = [] <->
  Forall2 (fun r e => scr_matches_expected r e = true)
          (rf_recorded rf) (derive_expected s1 s2).
Proof.
  intros rf s1 s2. unfold crosscheck_impl.
  generalize (derive_expected s1 s2) as exps. generalize (rf_recorded rf) as rs.
  induction rs as [| r rs' IH]; intros [| e exps']; cbn; split; intro H.
  - constructor.
  - reflexivity.
  - discriminate.
  - inversion H.
  - discriminate.
  - inversion H.
  - destruct (scr_matches_expected r e) eqn:E; cbn in H; [| discriminate].
    constructor; [ exact E |]. apply IH. exact H.
  - inversion H as [| ? ? ? ? He Hrest]; subst.
    rewrite He. cbn. apply IH. exact Hrest.
Qed.

(* T26, top-level: [crosscheck_impl] emits no [campaign_record_mismatch] finding
   iff every recorded result AGREES -- field for field ([scr_agrees]) -- with its
   replay-derived expectation, and the two lists have equal length and index
   order (the [Forall2] forces both). *)
Theorem crosscheck_impl_nil_iff : forall rf s1 s2,
  crosscheck_impl rf s1 s2 = [] <->
  Forall2 scr_agrees (rf_recorded rf) (derive_expected s1 s2).
Proof.
  intros rf s1 s2. rewrite crosscheck_impl_nil_iff_bool. split; intro H.
  - induction H as [| r e rs es Hre Hrest IH]; constructor.
    + apply scr_matches_expected_true_iff. exact Hre.
    + exact IH.
  - induction H as [| r e rs es Hre Hrest IH]; constructor.
    + apply scr_matches_expected_true_iff. exact Hre.
    + exact IH.
Qed.

(* ================= the budget crosscheck ================= *)

(* rec.resource_budget is ADVISORY (AUDIT_POLICY 7.2: the effective limits are the
   verifier_config fields).  Only [max_candidates] has an effective counterpart;
   the four fields with none, if present, are flagged NotEvaluated.  Nothing here
   fails closed. *)
Definition crosscheck_budget_impl (rb : resource_budget_view)
  (cfg : verifier_config) : list finding :=
  (match rb_max_candidates rb with
   | Some n => if Nat.eqb n (max_candidates cfg) then []
               else [budget_finding Fail "max_candidates"]
   | None => []
   end)
  ++ (match rb_max_memory_bytes rb with Some _ => [budget_finding NotEvaluated "max_memory_bytes"] | None => [] end)
  ++ (match rb_max_per_candidate_memory_bytes rb with Some _ => [budget_finding NotEvaluated "max_per_candidate_memory_bytes"] | None => [] end)
  ++ (match rb_max_per_candidate_wall_clock_seconds rb with Some _ => [budget_finding NotEvaluated "max_per_candidate_wall_clock_seconds"] | None => [] end)
  ++ (match rb_max_wall_clock_seconds rb with Some _ => [budget_finding NotEvaluated "max_wall_clock_seconds"] | None => [] end).

Definition record_crosscheck_impl
  (parse_full : campaign_record -> option campaign_record_full_view)
  (ac : authenticated_campaign) (s1 : list stage1_slot) (s2 : list stage2_slot)
  (cfg : verifier_config) : list finding :=
  match parse_full (authenticated_record ac) with
  | None => [mkFinding "campaign_record_undecodable" Fail None None]
  | Some rf =>
      crosscheck_impl rf s1 s2 ++ crosscheck_budget_impl (rf_budget rf) cfg
  end.

(* ================= advisory record-finding identifier domain ================= *)

(* The findings [record_crosscheck_impl] emits into [replay_record_findings] draw
   their [check_id] from a CLOSED 3-element family, DISJOINT from the frozen stage
   [check_id] set of VERDICT_SEMANTICS.md 2.  The governing-document erratum that
   authorises this family (grammar + deterministic order) is
   PHASE_1_ADVISORY_FINDING_IDS_ERRATUM.md.  Byte-ascending order. *)
Definition advisory_finding_ids : list string :=
  ["budget_advisory"; "campaign_record_mismatch"; "campaign_record_undecodable"].

Lemma crosscheck_list_ids : forall rs exps f,
  In f (crosscheck_list rs exps) -> finding_check_id f = "campaign_record_mismatch".
Proof.
  induction rs as [| r rs' IH]; intros [| e exps'] f H; cbn in H.
  - contradiction.
  - destruct H as [<- | []]; reflexivity.
  - destruct H as [<- | []]; reflexivity.
  - apply in_app_or in H as [H | H].
    + destruct (scr_matches_expected r e); cbn in H;
        [ contradiction | destruct H as [<- | []]; reflexivity ].
    + eapply IH; exact H.
Qed.

Lemma crosscheck_impl_ids : forall rf s1 s2 f,
  In f (crosscheck_impl rf s1 s2) -> finding_check_id f = "campaign_record_mismatch".
Proof.
  intros rf s1 s2 f H. unfold crosscheck_impl in H.
  eapply crosscheck_list_ids; exact H.
Qed.

Lemma crosscheck_budget_impl_ids : forall rb cfg f,
  In f (crosscheck_budget_impl rb cfg) -> finding_check_id f = "budget_advisory".
Proof.
  intros rb cfg f H. unfold crosscheck_budget_impl in H.
  repeat (apply in_app_or in H as [H | H]);
    repeat match goal with
    | H : In _ (match ?x with _ => _ end) |- _ => destruct x
    | H : In _ (if ?b then _ else _) |- _ => destruct b
    | H : In _ [] |- _ => destruct H
    | H : In _ [_] |- _ => destruct H as [<- | []]
    end; reflexivity.
Qed.

Theorem record_crosscheck_impl_ids : forall parse_full ac s1 s2 cfg f,
  In f (record_crosscheck_impl parse_full ac s1 s2 cfg) ->
  In (finding_check_id f) advisory_finding_ids.
Proof.
  intros parse_full ac s1 s2 cfg f H. unfold record_crosscheck_impl in H.
  destruct (parse_full (authenticated_record ac)) as [rf|].
  - apply in_app_or in H as [H | H].
    + rewrite (crosscheck_impl_ids _ _ _ _ H). cbn; auto.
    + rewrite (crosscheck_budget_impl_ids _ _ _ H). cbn; auto.
  - destruct H as [<- | []]. cbn; auto.
Qed.

(* ================= verdict invariance ================= *)

Definition set_crosscheck (ops : primitive_ops)
  (g : authenticated_campaign -> list stage1_slot -> list stage2_slot ->
       verifier_config -> list finding) : primitive_ops :=
  mkPrimitiveOps
    (op_parse_commitment ops) (op_signer_authorised ops) (op_signature_valid ops)
    (op_manifest_policy_matches ops) (op_manifest_audit_matches ops)
    (op_manifest_context_matches ops) (op_ledger_mismatch ops)
    (op_record_identity_mismatch ops) (op_completeness_wellformed ops)
    (op_stage1_check ops) (op_preflight ops) (op_eval_o3 ops)
    (op_stage2_check ops) g (op_transcript_digest ops).

Lemma run_stage1_set_crosscheck : forall ops g cfg pd p subs i fuel sr pr,
  run_stage1 (set_crosscheck ops g) cfg pd p subs i fuel sr pr
  = run_stage1 ops cfg pd p subs i fuel sr pr.
Proof.
  intros ops g cfg pd p subs.
  induction subs as [| sub rest IH]; intros i fuel sr pr;
    cbn [run_stage1]; [ reflexivity |].
  replace (op_stage1_check (set_crosscheck ops g)) with (op_stage1_check ops)
    by reflexivity.
  destruct (charge fuel (stage1_cost cfg sub)) as [fuel'|]; [| reflexivity].
  rewrite IH. reflexivity.
Qed.

Lemma run_stage2_set_crosscheck : forall ops g rc cfg tr pending fuel sr,
  run_stage2 (set_crosscheck ops g) rc cfg tr pending fuel sr
  = run_stage2 ops rc cfg tr pending fuel sr.
Proof.
  intros ops g rc cfg tr pending.
  induction pending as [| ps rest IH]; intros fuel sr;
    cbn [run_stage2]; [ reflexivity |].
  replace (op_stage2_check (set_crosscheck ops g)) with (op_stage2_check ops)
    by reflexivity.
  destruct (charge fuel (4 * model_call_fuel cfg)) as [fuel'|]; [| reflexivity].
  rewrite IH. reflexivity.
Qed.

Lemma finish_replay_verdict_fields : forall ops ac cfg s1 ctx s2 fuel clo,
  replay_stage1  (finish_replay ops ac cfg s1 ctx s2 fuel clo) = s1  /\
  replay_context (finish_replay ops ac cfg s1 ctx s2 fuel clo) = ctx /\
  replay_stage2  (finish_replay ops ac cfg s1 ctx s2 fuel clo) = s2  /\
  replay_fuel    (finish_replay ops ac cfg s1 ctx s2 fuel clo) = fuel /\
  replay_clo     (finish_replay ops ac cfg s1 ctx s2 fuel clo) = clo.
Proof. intros. cbn. repeat split; reflexivity. Qed.

Local Ltac ffin :=
  cbn [replay_stage1 replay_context replay_stage2 replay_fuel replay_clo
       finish_replay]; repeat split; reflexivity.

Lemma replay_verdict_fields_indep_crosscheck :
  forall ops g ac cb cfg pd p l0 tr,
    replay_stage1  (replay (set_crosscheck ops g) ac cb cfg pd p l0 tr)
      = replay_stage1  (replay ops ac cb cfg pd p l0 tr) /\
    replay_context (replay (set_crosscheck ops g) ac cb cfg pd p l0 tr)
      = replay_context (replay ops ac cb cfg pd p l0 tr) /\
    replay_stage2  (replay (set_crosscheck ops g) ac cb cfg pd p l0 tr)
      = replay_stage2  (replay ops ac cb cfg pd p l0 tr) /\
    replay_fuel    (replay (set_crosscheck ops g) ac cb cfg pd p l0 tr)
      = replay_fuel    (replay ops ac cb cfg pd p l0 tr) /\
    replay_clo     (replay (set_crosscheck ops g) ac cb cfg pd p l0 tr)
      = replay_clo     (replay ops ac cb cfg pd p l0 tr).
Proof.
  intros ops g ac cb cfg pd p l0 tr.
  unfold replay.
  rewrite run_stage1_set_crosscheck.
  replace (op_preflight (set_crosscheck ops g)) with (op_preflight ops) by reflexivity.
  replace (op_eval_o3 (set_crosscheck ops g)) with (op_eval_o3 ops) by reflexivity.
  destruct (Nat.ltb (max_candidates cfg)
              (Datatypes.length (authenticated_submissions ac)));
    [ ffin |].
  destruct (run_stage1 ops cfg pd p (authenticated_submissions ac) 0 l0 [] [])
    as [fuel s1 pending | fuel s1 pending]; [| ffin ].
  destruct pending as [| ps0 pr]; [ ffin |].
  destruct cb as [| reason | lc]; [ ffin | ffin |].
  destruct (charge fuel (preflight_fuel (schedule cfg))) as [fuel1|]; [| ffin ].
  destruct (op_preflight ops lc) as [reason findings | preflight_findings]; [ ffin |].
  destruct (charge fuel1 (model_call_fuel cfg)) as [fuel2|]; [| ffin ].
  destruct (lookup_unique tr (mkCallKey ContextProbe Probe 0)) as [event|]; [| ffin ].
  destruct (op_eval_o3 ops lc event p) as [findings | rc o3_findings]; [ ffin |].
  rewrite run_stage2_set_crosscheck.
  destruct (run_stage2 ops rc cfg tr (ps0 :: pr) fuel2 []) as [[s2 fuel3] clo].
  ffin.
Qed.

Lemma verdict_decide_ignores_record_findings :
  forall ops rr fs ac ti tr tev cev,
    verdict_of (decide ops
      (mkReplayResult (replay_stage1 rr) (replay_context rr) (replay_stage2 rr)
         (replay_fuel rr) (replay_clo rr) fs) ac ti tr tev cev)
    = verdict_of (decide ops rr ac ti tr tev cev).
Proof.
  intros ops rr fs ac ti tr tev cev. unfold decide, verdict_of.
  cbn [replay_stage1 replay_context replay_stage2 replay_fuel replay_clo].
  destruct (valid_witnesses (replay_stage2 rr)); try reflexivity;
  destruct (replay_clo rr); try reflexivity;
  destruct (all_checked_obstructions (replay_stage2 rr)) as [ [[? ?] ?] |];
    try reflexivity;
  destruct (replay_context rr); try reflexivity;
  destruct (authenticated_completeness ac); try reflexivity;
  destruct (valid_completeness_certificate_v0 _ _); reflexivity.
Qed.

Lemma decide_ignores_ops : forall ops ops' rr ac ti tr tev cev,
  decide ops rr ac ti tr tev cev = decide ops' rr ac ti tr tev cev.
Proof. reflexivity. Qed.

Theorem assess_validated_verdict_indep_crosscheck :
  forall ops g ti vr src,
    verdict_of (assess_validated (set_crosscheck ops g) ti vr src)
    = verdict_of (assess_validated ops ti vr src).
Proof.
  intros ops g ti vr src.
  destruct vr as [reason fuel ev | fuel ev | ac l0]; [ reflexivity | reflexivity |].
  unfold assess_validated.
  destruct src as [ tr cb | [ reason wd | tr wd ] cb ].
  - set (rr' := replay (set_crosscheck ops g) ac cb (ti_config ti)
                  (ti_policy_document ti) (ti_policy ti) l0 tr).
    set (rr  := replay ops ac cb (ti_config ti)
                  (ti_policy_document ti) (ti_policy ti) l0 tr).
    rewrite (decide_ignores_ops (set_crosscheck ops g) ops rr').
    replace (op_transcript_digest (set_crosscheck ops g)) with
            (op_transcript_digest ops) by reflexivity.
    destruct (replay_verdict_fields_indep_crosscheck ops g ac cb (ti_config ti)
                (ti_policy_document ti) (ti_policy ti) l0 tr)
      as (H1 & H2 & H3 & H4 & H5).
    fold rr' rr in H1, H2, H3, H4, H5.
    transitivity (verdict_of (decide ops
       (mkReplayResult (replay_stage1 rr) (replay_context rr) (replay_stage2 rr)
          (replay_fuel rr) (replay_clo rr) (replay_record_findings rr'))
       ac ti tr (LiveCapture (op_transcript_digest ops tr))
       (AuthenticatedCommitment (commitment_digest (authenticated_commitment ac))))).
    + destruct rr' as [a b c d e f]; cbn in H1, H2, H3, H4, H5 |- *.
      subst a b c d e. reflexivity.
    + apply verdict_decide_ignores_record_findings.
  - reflexivity.
  - set (rr' := replay (set_crosscheck ops g) ac cb (ti_config ti)
                  (ti_policy_document ti) (ti_policy ti) l0 tr).
    set (rr  := replay ops ac cb (ti_config ti)
                  (ti_policy_document ti) (ti_policy ti) l0 tr).
    rewrite (decide_ignores_ops (set_crosscheck ops g) ops rr').
    replace (op_transcript_digest (set_crosscheck ops g)) with
            (op_transcript_digest ops) by reflexivity.
    destruct (replay_verdict_fields_indep_crosscheck ops g ac cb (ti_config ti)
                (ti_policy_document ti) (ti_policy ti) l0 tr)
      as (H1 & H2 & H3 & H4 & H5).
    fold rr' rr in H1, H2, H3, H4, H5.
    transitivity (verdict_of (decide ops
       (mkReplayResult (replay_stage1 rr) (replay_context rr) (replay_stage2 rr)
          (replay_fuel rr) (replay_clo rr) (replay_record_findings rr'))
       ac ti tr (OfflineTranscript (op_transcript_digest ops tr) wd)
       (AuthenticatedCommitment (commitment_digest (authenticated_commitment ac))))).
    + destruct rr' as [a b c d e f]; cbn in H1, H2, H3, H4, H5 |- *.
      subst a b c d e. reflexivity.
    + apply verdict_decide_ignores_record_findings.
Qed.
