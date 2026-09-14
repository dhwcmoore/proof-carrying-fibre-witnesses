# Phase 1 -- `op_record_crosscheck`: `submission_check_result` equality against the replay-derived result

Date: 2026-09-10 (r14 held; r15 partial; r16 held; this is **r17**)
Baseline: `PHASE_1_CAMPAIGN_RECORD.md` (r13).  Module
`implementation/rocq/RecordCrosscheck.v` (`Qed`, axiom-free); a
**data-representation repair to the frozen `Orchestration.v`** (VERDICT_SEMANTICS
§2 / §4.1 were already ahead -- no `Orchestration.v` governing-document change); additions to
`Stage1Wrapper.v` / `PipelineWiring.v` / `ContextResolution.v`; and a
**consistency erratum**, `PHASE_1_ADVISORY_FINDING_IDS_ERRATUM.md`, for the
advisory `record_findings` identifier domain (reviewer-concurred 2026-09-10,
applied to `VERDICT_SEMANTICS.md` / `AUDIT_POLICY_AND_EVIDENCE.md` /
`THREAT_MODEL.md` -- see §5).

Status: **reviewer-concurred (source inspection, 2026-09-10) and promoted.**
Reviewed r17 ZIP sha256
`476c32c3bbdade74323481ec8b7cba87ac77d1e9e375074d6465f5418de10de1`.  Not a
Phase 1 closure.

## 1. Data-representation repair (frozen `Orchestration.v`)

| type | spec (already ahead) | change |
|---|---|---|
| `finding` | VERDICT_SEMANTICS §2: `{check_id ; outcome ; reason : string option ; offending : canonical_value option}` | `+ finding_offending : option string` (the offending term's raw canonical text) |
| `parsed_candidate` | VERDICT_SEMANTICS §4.1 keys `candidate_id, policy_hash, schema_version, x, y` | `+ pc_candidate_id : string` |
| `stage1_result` | VERDICT_SEMANTICS §4.1: `candidate_id : string option ; semantic_candidate_digest : digest option` -- **`Some` for every parsed candidate**, `None` on a parse rejection | `+ s1_candidate_id : option string ; s1_semantic_digest : option digest` |

`Stage1Wrapper.v` gains an F.3 `candidate_id_of : candidate_submission -> digest`
(alongside the existing `semantic_digest_of`); `op_stage1_wrapper` sets
`s1_candidate_id` / `s1_semantic_digest` to `Some …` on `WireOk` and `None` on
`WireReject` (`wrapper_parsed_ids` / `wrapper_reject_ids`).  `PipelineWiring.v`
threads it into `wired_stage1`.  `ContextResolution.pass_finding` gains the
`offending` argument.  **The promoted r5–r13 theorems are re-proved.**  The
`candidate_id_of` decoder's correctness stays an **F.3 (F.3.2) parser residual**,
like `semantic_digest_of` and `lower_parse`.

The r5–r13 promotion (reviewer-concurred by source inspection of the **r13**
bytes) does **not** automatically extend to the modified files here
(`Orchestration.v`, `Stage1Wrapper.v`, `PipelineWiring.v`, `ContextResolution.v`);
the author re-proves the promoted theorems after the change, and a fresh source
review is required for those bytes.

## 2. Fully typed `submission_check_result` decoder

```
Inductive scr_outcome_view :=
| ScrRejected b_reason | ScrValidWitness | ScrNotAWitness c_reason
| ScrObstructed o_reason.        (* four cases -- NO not_run: see §3 *)

Record scr_view := mkScrView {
  scr_index; scr_digest : digest;
  scr_candidate_id : option string;   (* replay-derived: the stage-1 result's s1_candidate_id *)
  scr_semantic : option digest; scr_outcome : scr_outcome_view;
  scr_findings : list finding }.
```

`parse_scr` decodes the full grammar (canonical key order `candidate_id`?,
`findings`, `outcome`, `semantic_candidate_digest`?, `submission_digest`,
`submission_index`):

- `outcome` -> `scr_outcome_view` via `parse_scr_outcome`; an unknown reason is
  **rejected** (`parse_scr_outcome_rejects_unknown_reason`).
- `findings` -> `list finding`: `check_id` must be in the **frozen closed stage
  set** `check_ids` (`valid_check_id`); an optional `offending` value is
  **captured as its raw canonical text** into `finding_offending`.
- `resource_budget_view`: 5 optional `nat` keys, strictly ascending, dup-free,
  unknown-key-rejecting.

**Decoder relation -- forward projection only.**
`parse_record_full_impl_projects` : `parse_record_full_impl r = Some v` implies
`parse_record_impl r = Some (rf_identity v)`.  The reverse is **false** (r13's
`skip_value` tolerates canonical bytes the typed decoders reject).

## 3. Replay-derived expected results -- filtered, mandatory digest

```
Record expected_scr := mkExpectedScr {
  exp_index; exp_digest : digest;         (* MANDATORY *)
  exp_candidate_id : option string; exp_semantic : option digest;
  exp_outcome : scr_outcome_view; exp_findings : list finding }.

derive_one  : list stage2_slot -> stage1_slot -> option expected_scr
derive_expected : list stage1_slot -> list stage2_slot -> list expected_scr
```

`derive_one` yields `None` for a replay slot that produced **no**
`submission_check_result`:

- a stage-1 `NotRun` slot;
- a `S1Pending` submission whose stage-2 slot is `NotRun`.

`AUDIT_POLICY_AND_EVIDENCE.md` §2.2.5 gives `submission_check_result` a
**mandatory `submission_digest`** and **no `not_run` outcome** -- so such a slot
cannot be represented as a decoded result, and is filtered out rather than
carried as a synthetic `not_run`.  `derive_expected` is the filtered list, in
stage-1 slot order.  Proved:

- **`derive_one_index`** -- `derive_one` never changes the slot index.
- **`derive_expected_indices`** --
  `map exp_index (derive_expected s1 s2) = map stage1_slot_index (filter (slot_ran s2) s1)`
  : the derived list is an **order- and index-preserving projection** of the
  stage-1 slot list with the non-run slots dropped.
- **`derive_expected_length`** -- `length (derive_expected s1 s2) <= length s1`.

A `rec.recorded_results` entry that claims a result for a filtered slot is an
extra entry: it produces a `recorded_result_count` mismatch (or, if it displaces
a later real result, a positional `recorded_result` mismatch).

## 4. The crosscheck -- propositional relation + two-sided theorem

```
scr_agrees r e : Prop :=
  scr_index r = exp_index e /\ scr_digest r = exp_digest e
  /\ scr_candidate_id r = exp_candidate_id e /\ scr_semantic r = exp_semantic e
  /\ scr_outcome r = exp_outcome e /\ scr_findings r = exp_findings e

scr_matches_expected r e : bool :=            (* the decider for scr_agrees *)
  Nat.eqb (scr_index r) (exp_index e)
  && String.eqb (scr_digest r) (exp_digest e)          (* unconditional *)
  && oeqb (scr_candidate_id r) (exp_candidate_id e)     (* strict option equality *)
  && oeqb (scr_semantic r) (exp_semantic e)             (* strict option equality *)
  && scr_outcome_view_eqb (scr_outcome r) (exp_outcome e)
  && findings_eqb (scr_findings r) (exp_findings e)     (* incl. finding_offending *)
```

- **`scr_matches_expected_true_iff`** -- `scr_matches_expected r e = true` **iff**
  `scr_agrees r e` (both directions; the reverse uses the `_refl` deciders).
  `scr_matches_expected_fields` is the forward projection, kept under its own
  name.
- **`crosscheck_impl_nil_iff`** (top level, T26) --
  `crosscheck_impl rf s1 s2 = []` **iff**
  `Forall2 scr_agrees (rf_recorded rf) (derive_expected s1 s2)`
  -- no `campaign_record_mismatch` finding iff every recorded result agrees,
  field for field, with its replay-derived expectation, and the two lists have
  equal length and index order (the `Forall2` forces both).
  `crosscheck_impl_nil_iff_bool` is the supporting Boolean form.

`crosscheck_budget_impl` unchanged -- advisory (`max_candidates` vs
`verifier_config`; the four fields with no effective counterpart -> a
`NotEvaluated` advisory; nothing fails closed).

## 5. Advisory record-finding identifier domain (consistency erratum)

`record_crosscheck_impl`'s findings land only in
`replay_result.record_findings`.  Their `check_id` values --
`campaign_record_mismatch`, `budget_advisory`, `campaign_record_undecodable` --
are **not** in the frozen 19-element stage `check_id` set of VERDICT_SEMANTICS
§2, and never could be (they are not stage checks).  T26 itself named
`campaign_record_mismatch`, so §2 and §6.5/T26 were, read together, inconsistent.

`PHASE_1_ADVISORY_FINDING_IDS_ERRATUM.md` (**reviewer-concurred 2026-09-10**,
applied to `VERDICT_SEMANTICS.md` §2 / §6.5, `AUDIT_POLICY_AND_EVIDENCE.md`
§2.2.5, `THREAT_MODEL.md` T26) reconciles them: `record_findings` findings draw
`check_id` from a **closed advisory family** disjoint from the stage set, with a
fixed grammar (outcome / reason token / no `offending`) and deterministic order.
In the implementation:

- `advisory_finding_ids : list string` -- the closed 3-element family.
- **`record_crosscheck_impl_ids`** -- every finding `record_crosscheck_impl`
  emits has `check_id ∈ advisory_finding_ids` (`Qed`).
- `crosscheck_impl_ids` / `crosscheck_budget_impl_ids` -- the two crosschecks
  emit only `campaign_record_mismatch` / `budget_advisory`.

## 6. Verdict invariance (`Qed`, axiom-free) -- unchanged from r15/r16

`op_record_crosscheck`'s output lands only in `replay_record_findings`, which
`decide` / `verdict_of` never read.  `verdict_decide_ignores_record_findings`,
`run_stage{1,2}_set_crosscheck`, `replay_verdict_fields_indep_crosscheck`,
`assess_validated_verdict_indep_crosscheck`,
`ManifestPipeline.pipeline_verdict_indep_of_crosscheck` -- replacing
`op_record_crosscheck` by **any** function leaves the campaign verdict unchanged
(THREAT_MODEL T26: verdict = the replayed verdict).

## 7. Wiring + harness

`ManifestPipeline.pipeline_ops` sets `op_record_crosscheck` to
`RecordCrosscheck.record_crosscheck_impl parse_record_full_impl`
(`pipeline_ops_crosscheck`).  `op_completeness_wellformed` is out of scope.

`ocaml/test_manifest_authentication.ml`: typed decode of the normative full
record; `parse_finding` captures `offending` and **rejects an out-of-set
`check_id`**; `parse_scr_outcome` rejects an unknown reason; `parse_budget_object`
canonicality; `crosscheck_budget_impl` advisory-only; `crosscheck_impl` against
the replay-derived expectation -- matching -> `[]`, and a **mutation of each
field** (`candidate_id`, a parsed-non-witness `semantic_candidate_digest`, an
`offending` value / omission, an **isolated `submission_digest`**, an isolated
`submission_index`, the outcome, the findings, the index order, the count) ->
a `campaign_record_mismatch`; **`derive_expected` filters** a stage-1 `NotRun`
slot and a pending + stage-2-`NotRun` slot, and a recorded claim for either ->
mismatch; **positive + mutation + `NotRun`-alignment tests run through
`parse_record_full_impl`** (not hand-built views); every
`record_crosscheck_impl` finding's `check_id` is in the closed 3-id family; a
**matching end-to-end** `record_crosscheck_impl` -> no mismatch; an undecodable
record -> the single `campaign_record_undecodable`.

## Effect on the status ledger

`op_record_crosscheck`: **concrete standalone AND integrated** (`pipeline_ops`),
with `crosscheck_impl_nil_iff` over the propositional `scr_agrees`, the filtered
`derive_expected` with its projection lemmas, the advisory-identifier domain
lemma, and the verdict-invariance suite.  **Reviewer-concurred by source
inspection and promoted (2026-09-10; reviewed r17 ZIP sha256
`476c32c3bbdade74323481ec8b7cba87ac77d1e9e375074d6465f5418de10de1`).**  The
advisory-identifier erratum (`PHASE_1_ADVISORY_FINDING_IDS_ERRATUM.md`) is
reviewer-concurred and applied to the governing set.  Residuals: the `offending`
value is compared as raw canonical text (a structural `canonical_value`
comparison would be strictly finer, but text equality is exact); `policy_hash` /
`schema_version` from `parsed_candidate` are not surfaced (checked by stage-1
B-tier, not needed here); the F.3 decoders (`candidate_id_of`,
`semantic_digest_of`, the wire parsers) passed in; retrieval integrity.

Still OPEN: `op_transcript_digest`. `op_completeness_wellformed` is now concrete
(`CompletenessWellformed`, author-reported -- `PHASE_1_COMPLETENESS_WELLFORMED.md`).

`make check` exits 0: `coqchk` covers **19** modules; across `make check`,
**133** `Print Assumptions` "Closed under the global context"; **seven**
`make test` harnesses PASS.

Phase 1 remains **open**; Phase 2 is not authorised; this unit is promoted but
that is **not** a Phase 1 closure.
