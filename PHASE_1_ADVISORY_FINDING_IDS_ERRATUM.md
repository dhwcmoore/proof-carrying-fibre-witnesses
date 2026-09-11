# Consistency erratum: advisory record-finding identifiers

**Status: CONCURRED (reviewer role, 2026-09-10) and APPLIED to the root governing
set — `VERDICT_SEMANTICS.md` §2 / §6.5, `AUDIT_POLICY_AND_EVIDENCE.md` §2.2.5,
`THREAT_MODEL.md` T26. The historical Phase 0 closure package
(`phase0_closure_package_r1/revised/*`) is left unchanged.**

This is a **narrowly bounded consistency erratum**. It does not reopen Phase 0,
does not authorise Phase 2, and changes no verdict, no result type, no control
flow, and no stage-level check. It reconciles two statements that the frozen
Revision-15 documents already make but that, read together, are inconsistent.

## The inconsistency

1. `VERDICT_SEMANTICS.md` §2 fixes the `finding.check_id` domain to a closed
   19-element set of **stage** check labels:

   ```
   { "B6","B1a","B1b","B1c","B2","B3","B4","B5",
     "C1","C2","C3","C5","O1","O2","O3","O6","O4","O5","C4" }
   ```

2. `VERDICT_SEMANTICS.md` §6.5 defines

   ```
   record_findings := crosscheck(ac.rec.recorded_results, stage1, stage2)
                   ++ crosscheck_budget(ac.rec.resource_budget, vcfg)
   ```

   and `THREAT_MODEL.md` T26 / `VERDICT_SEMANTICS.md` §11 (line ~682) require
   that a recorded result inconsistent with the replay produce a
   **`campaign_record_mismatch`** finding in `record_findings`.

`campaign_record_mismatch` is not in the §2 set, and it never could be: it is
not a stage check. The `crosscheck` / `crosscheck_budget` results are a **second,
disjoint population** of `finding` values — advisory, campaign-record-level,
emitted only into `replay_result.record_findings`, which `decide` and
`verdict_of` never read.

## Resolution — a closed advisory identifier family

`finding.check_id : string` carries a value from **one of two closed sets**,
selected by where the finding lives:

| finding population | `check_id` domain |
|---|---|
| `stage1_findings`, `stage2` findings, `context_findings`, `rejection_report.findings` | the frozen 19-element **stage** set (§2, unchanged) |
| `replay_result.record_findings` (the `crosscheck` / `crosscheck_budget` output) | the **advisory** set below |

```
advisory_finding_id =
  | "budget_advisory"
  | "campaign_record_mismatch"
  | "campaign_record_undecodable"
```

The two sets are **disjoint** (every stage label is a 2–3 character tier code;
no advisory identifier matches one). Listed in byte-ascending order, which is
also their canonical enumeration order.

### Grammar

Each advisory finding is a `finding = { check_id ; outcome ; reason ; offending }`
(`VERDICT_SEMANTICS.md` §2). For this family `offending` is **always omitted**,
and `reason`, when present, is a fixed lower-snake-case **token** (not a
`b_/c_/o_reason` constructor name) drawn from the closed list given here — a
`string option`, already schema-valid under §2 and `AUDIT_POLICY_AND_EVIDENCE.md`
§2.2.5.

| `check_id` | `outcome` | `reason` (token) | emitted by | when |
|---|---|---|---|---|
| `campaign_record_mismatch` | `fail` | `recorded_result` | `crosscheck` | a recorded `submission_check_result` disagrees, field for field, with the replay-derived result at the same list position |
| `campaign_record_mismatch` | `fail` | `recorded_result_count` | `crosscheck` | `rec.recorded_results` and the replay-derived list differ in length |
| `budget_advisory` | `fail` | `max_candidates` | `crosscheck_budget` | `rec.resource_budget.max_candidates` present and ≠ `vcfg.max_candidates` |
| `budget_advisory` | `not_evaluated` | `max_memory_bytes` | `crosscheck_budget` | that field present in `rec.resource_budget` (no effective `vcfg` counterpart) |
| `budget_advisory` | `not_evaluated` | `max_per_candidate_memory_bytes` | `crosscheck_budget` | idem |
| `budget_advisory` | `not_evaluated` | `max_per_candidate_wall_clock_seconds` | `crosscheck_budget` | idem |
| `budget_advisory` | `not_evaluated` | `max_wall_clock_seconds` | `crosscheck_budget` | idem |
| `campaign_record_undecodable` | `fail` | *(omitted)* | `op_record_crosscheck` | `ac.rec` does not decode as a canonical campaign record |

### Deterministic order in `record_findings`

- If `ac.rec` does not decode: exactly `[ campaign_record_undecodable ]`, and
  nothing else (the two crosschecks do not run).
- Otherwise: the `crosscheck` findings first — positional
  `campaign_record_mismatch / recorded_result` entries in `rec.recorded_results`
  order, then at most one trailing `campaign_record_mismatch / recorded_result_count`
  when the lengths differ — followed by the `crosscheck_budget` findings in the
  `resource_budget` field order (`max_candidates`, `max_memory_bytes`,
  `max_per_candidate_memory_bytes`, `max_per_candidate_wall_clock_seconds`,
  `max_wall_clock_seconds`).

### `derive_expected` and replay `NotRun`

`crosscheck` compares `rec.recorded_results` position-by-position against the
list of `submission_check_result` values the **replay actually produced**. A
replay slot that produced no result — a stage-1 `NotRun` slot, or a `Pending`
submission whose stage-2 slot is `NotRun` — contributes **no** entry to that
list (`AUDIT_POLICY_AND_EVIDENCE.md` §2.2.5 gives `submission_check_result` a
mandatory `submission_digest` and no `not_run` outcome). The derived list is
therefore an order- and index-preserving projection of the stage-1 slot list
with the non-run slots dropped. A `rec.recorded_results` entry that claims a
result for a dropped slot is an extra entry and surfaces as a
`recorded_result_count` (or, if it displaces a later real result, a positional
`recorded_result`) mismatch.

## Governing-document edits (applied 2026-09-10, on reviewer concurrence)

1. **`VERDICT_SEMANTICS.md` §2** — after the `check_id` set: findings in
   `replay_result.record_findings` (the `crosscheck` / `crosscheck_budget`
   output, §6.5) carry `check_id ∈ { "budget_advisory",
   "campaign_record_mismatch", "campaign_record_undecodable" }` — the closed
   advisory family, disjoint from the stage set; `offending` always omitted,
   `reason` a fixed lower-snake-case token.
2. **`VERDICT_SEMANTICS.md` §6.5** — the `crosscheck` position-by-position rule
   for replay `` `NotRun `` slots, the advisory `check_id` family, and the
   `decide` / `verdict_of` independence (T26), each cross-referenced here.
3. **`AUDIT_POLICY_AND_EVIDENCE.md` §2.2.5** — the `finding` row now distinguishes
   a stage finding (`check_id` from §2 stage set, `reason` a constructor name)
   from a `record_findings` finding (`check_id` from the advisory family,
   `offending` omitted, `reason` a fixed token).
4. **`THREAT_MODEL.md` T26** — no change of substance; `campaign_record_mismatch`
   is cited as a member of the advisory family, landing in
   `replay_result.record_findings`.

The historical `phase0_closure_package_r1/revised/*` copies are **not** touched.

## Implementation state

Applied in `implementation/rocq/RecordCrosscheck.v` (Rocq, `Qed`, axiom-free)
and its OCaml mirror + `make test`:

- `advisory_finding_ids : list string` — the closed 3-element family.
- `record_crosscheck_impl_ids` — **every** finding `record_crosscheck_impl`
  emits has `check_id ∈ advisory_finding_ids` (`Qed`).
- `crosscheck_impl_ids` / `crosscheck_budget_impl_ids` — the two crosschecks
  emit only `campaign_record_mismatch` / `budget_advisory` respectively.
- `assess_validated_verdict_indep_crosscheck` (unchanged) — replacing
  `op_record_crosscheck` by any function leaves the campaign verdict unchanged,
  so nothing in this family is verdict-bearing.

`make check` exits 0 with these results `Closed under the global context`.
