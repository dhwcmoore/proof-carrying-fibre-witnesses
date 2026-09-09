# Evidence Ledger — Phase 0 closure

Two evidence sources, kept separate. The closure report must reproduce this
separation.

## A. Independently inspected by the designated reviewer

Reviewer environment: source and archive inspection only; **no `coqc`**, so no
build, proof-check or test execution on the reviewer's side.

| # | Claim | How verified | Result |
|---|---|---|---|
| A1 | r4 archive integrity | SHA-256 of `unit1a_preclosure_compile_candidate_r4.zip` = `d39db6c5392013a2ac6438e2bd82b74990985e3e5a2679e884cd841f4945139f`; all 33 `MANIFEST.sha256` entries recomputed | PASS |
| A2 | Frozen Revision 14 governing set unchanged by the implementation work | byte-diff of every governing doc in the r4 archive against r2 | identical except `IMPLEMENTATION_STATUS.md` (addendum only) |
| A3 | T1 / A1 kernel unchanged | byte-diff `FibreWitnessKernel.v` r4 vs r2 | identical |
| A4 | `REP1_not_run_has_no_witness` restated over `stage2_slots_wf` and proved (not `Admitted`) | read `rocq/Orchestration.v` | confirmed — `Qed`, with `replay_stage2_wf` + `REP1_replay_not_run_has_no_witness` |
| A5 | Pending indices orchestration-assigned; stage-2 witness-index contract is an explicit premise | read `run_stage1`, `with_pending_index`, `stage2_witness_index_contract` | confirmed |
| A6 | `ctx_reason` retains exactly its three original constructors | read Rocq + OCaml type decls | confirmed |
| A7 | Bundle inconsistency uses separate nullary `context_state` / `campaign_obstruction` constructors; `CtxUnavailable` / `PreflightFail` cannot carry it | read type decls and the `replay` `CtxNotNeeded` branch | confirmed — the invalid placement is not expressible |
| A8 | Affected `replay` branch returns `ContextBundleInconsistent`, pending slots `NotRun`, `clo = InconsistentContextBundle`, obligation `reconstruct_or_supply_context_bundle` | read `replay` and `obstruction_obligation` | confirmed |
| A9 | OCaml `.ml` / `.mli` mirror the same split | read both | confirmed |
| A10 | No `PHASE_0_CLOSURE_REPORT.md` present in the archive or shared folder | file listing | confirmed absent |
| A11 | This package's `revised/` files differ from Revision 14 only as `diffs/` show | read `diffs/*.rev14-rev15.diff` | (reviewer to confirm) |

## B. Executed only on the implementation-author's machine

Author environment: Coq / coqc / coqchk / coqtop 8.18.0, OCaml 4.14.1, dune,
ocamlfind present (`/usr/bin`). Commands run from
`unit1a_preclosure_candidate_r4/implementation`.

| # | Claim | Command | Result |
|---|---|---|---|
| B1 | All four `.v` files compile | `make rocq` (`coqc -Q rocq PCFW …`) | exit 0 |
| B2 | Whole-development re-check | `coqchk -Q rocq PCFW PCFW.FibreWitnessKernel PCFW.Orchestration` | "Modules were successfully checked" |
| B3 | Kernel `T1` / `A1` axiom-free | `coqtop < rocq/PrintKernelAssumptions.v` | "Closed under the global context" (×2) |
| B4 | Kernel trust scan | `! grep -En '\b(Admitted\|admit\|Axiom\|Parameter\|Hypothesis)\b' rocq/FibreWitnessKernel.v` | no match |
| B5 | `REP1_not_run_has_no_witness`, `REP1_replay_not_run_has_no_witness`, `replay_stage2_wf` axiom-free | `make assumptions` (`coqtop < rocq/PrintOrchestrationAssumptions.v`) | "Closed under the global context" (×3) |
| B6 | The 5 remaining obligations each print as their own sole axiom | same command | `T2_sound`, `T2_complete`, `stage1_over_is_terminal`, `exact_unreachable_v0`, `validation_fuel_obstructed_unreachable_when_sufficient` — no leakage |
| B7 | OCaml skeleton compiles (incl. `-w +8`) | `make ocaml` | exit 0, no warnings |
| B8 | Path check: `InconsistentContextBundle` reported truthfully; `CtxUnavailable ArtifactMismatch` path unchanged; terminal stage-1 exhaustion unchanged; pending index orchestration-assigned | `make test` (`ocaml/test_context_bundle.ml`) | `PASS` |
| B9 | `make check` end-to-end from a fresh extraction of the r4 archive | `unzip … && cd …/implementation && make check` | exit 0 |
| B10 | Extraction regenerates `ocaml/extracted_orchestration.{ml,mli}` carrying the new constructors | `make rocq` | regenerated; `InconsistentContextBundle` / `ContextBundleInconsistent` present |

**Not established on either side:** linking the Coq-*extracted* OCaml against
`zarith` (author environment's `zarith` ships no `.cmi` files). This is a Phase 1
obligation (`CLOSURE_REPORT_CHECKLIST.md` item 5).
