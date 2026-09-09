# Phase 1 — orchestration proof obligations discharged

Date: 2026-09-05/06
Baseline: reviewer-issued Revision 15 (`PHASE_0_CLOSURE_REPORT.md`), implementation
byte-identical to `unit1a_preclosure_compile_candidate_r4.zip` (sha256
`d39db6c5392013a2ac6438e2bd82b74990985e3e5a2679e884cd841f4945139f`).

The Phase 0 closure report listed five `Admitted` orchestration obligations in
`implementation/rocq/Orchestration.v` as open Phase 1 work. They are now
machine-checked proofs of their **unchanged statements**:

| Theorem | What it states | Proof |
|---|---|---|
| `T2_sound` | `verdict_of (assess_validated …) = INADMISSIBLE` ⇒ the campaign is `ValidCampaign`, the source is ready, and a witness is in `valid_witnesses (replay_stage2 (replay …))` | case split on `validation_result` and `transcript_source`, then the helper `decide_inadmissible_iff_witness` |
| `T2_complete` | the converse: a witness in that list ⇒ `INADMISSIBLE` | same helper, other direction |
| `stage1_over_is_terminal` | when `run_stage1` stops on fuel with `\|subs\| ≤ max_candidates`, `replay`'s context is `NoContextNeeded` and `clo = CampaignFuelExhausted` | `Nat.ltb_ge` on the count bound, then rewrite by the `run_stage1` result |
| `exact_unreachable_v0` | `decide …` is never `Exact _` | `valid_completeness_certificate_v0` is constantly `false`, so the `Exact` branch is dead; exhaustive `destruct` + `discriminate` |
| `validation_fuel_obstructed_unreachable_when_sufficient` | if `max_fuel ≥` the sum of the four validation fuel phases, `validate_campaign` never returns `FuelObstructed _ _` | new `Lemma charge_some_ledger` (`k + c ≤ M ⇒ charge (mkFuelLedger M k) c = Some …`), applied to each of the four charges with `lia` against the budget hypothesis; every other result branch closed by `discriminate` |

One helper lemma was added: `decide_inadmissible_iff_witness` (relates
`decide`'s `INADMISSIBLE` verdict to `valid_witnesses` membership), plus
`charge_some_ledger` for the fuel proof. Both are `Qed`, axiom-free.

## What was NOT changed

- Every theorem statement (the five above and the REP1 chain:
  `REP1_not_run_has_no_witness`, `REP1_replay_not_run_has_no_witness`,
  `replay_stage2_wf`, `stage2_slots_wf`, `stage2_witness_index_contract`).
- All operational definitions, the semantic kernel (`FibreWitnessKernel.v`),
  the OCaml mirror, the Revision-15 governing set.

## Verification

Implementation machine (Coq / coqc / coqchk / coqtop 8.18.0, OCaml 4.14.1),
from a fresh extraction:

    cd implementation && make check          # exit 0

- `coqc` builds all four `.v`; `coqchk` → "Modules were successfully checked"
  for `PCFW.FibreWitnessKernel` and `PCFW.Orchestration`;
- `make assumptions`: all **eight** `Print Assumptions` targets report
  **"Closed under the global context"** — no `Axioms:` line for any;
- `grep -nE '\b(Admitted|admit|Axiom|Parameter|Hypothesis)\b'
  rocq/Orchestration.v` → no match;
- kernel `T1` / `A1` → "Closed under the global context"; kernel trust scan
  clean;
- OCaml skeleton compiles; `make test` → `PASS`.

Independent source review (designated reviewer, no `coqc`): statements,
definitions and the REP1 chain unchanged; both supplied diffs reproduce the
candidate exactly; `charge_some_ledger` correctly supports the four successive
charges; no `Admitted`/`admit`/`Axiom`/`Parameter`/`Hypothesis`. Concurred with
promotion.

Evidence status: machine-checking is from the implementation machine only (the
reviewer's environment lacks `coqc`); the reviewer's contribution is independent
source review. "Closed under the global context" does not discharge the explicit
`stage2_witness_index_contract` premise on `REP1`.

## Provenance

- `phase1-proofs.zip` — `phase1_proof_candidate_1`. **Failed** `make check`:
  the `validation_fuel_obstructed_unreachable_when_sufficient` script errored
  "Tactic failure: Cannot find witness". The other four proofs compiled.
- `phase1_proof_candidate_2.zip` (sha256
  `33a3ea20eb563f6dd4689f9f254786448fcb621e16573a0cc4c02d7eb37cd0e9`) —
  candidate 1 plus the `charge_some_ledger` fix. Passed `make check`. Promoted
  into `implementation/` here.

## Still open in Phase 1

Concrete `primitive_ops` and their contracts (including
`stage2_witness_index_contract`), semantic-kernel correspondence, physical
capture/replay correspondence, canonical-encoding and parser/boundary
acceptance, extracted-OCaml compile/link/execute against a real
arbitrary-precision library, and the cross-language agreement battery.
`T2_sound` / `T2_complete` are control-flow theorems, not an execution-
faithfulness or complete operational-assurance claim.
