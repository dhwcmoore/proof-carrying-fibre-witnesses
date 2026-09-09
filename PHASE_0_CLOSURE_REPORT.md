# Phase 0 closure report

Date: 2026-09-06
Issued by: ChatGPT/Codex, designated reviewer in this conversation.
Decision: CONCUR with Revision 15; reviewer closure report issued.

## Scope and authority

I accept the three revised governing documents supplied in phase0_closure_package_r1 and the r4 context-bundle amendment. In this reviewer-issued tree, VERDICT_SEMANTICS.md, AUDIT_POLICY_AND_EVIDENCE.md and THREAT_MODEL.md have been replaced by the exact reviewed Revision-15 copies. Their hashes appear in the root MANIFEST.sha256. The remaining governing content is carried forward from the reviewed r4 baseline.

This report is authored and issued by the reviewer, not by the implementation author. The author-prepared package was review input. No author-issued closure report is being adopted.

The shared-folder governance condition remains applicable: this report and the accompanying reviewed files must be transferred unchanged into the actual shared project folder for closure to take effect there. I have issued and placed them in the deliverable tree; I do not have access to the user's machine and do not claim to have replaced files there. Transfer of these reviewer-issued bytes is delivery, not authorship or a fresh closure decision. On that placement, Phase 0 is closed and Phase 1 may begin. Phase 2 is not authorised by this report.

## Ratified amendment

ctx_reason remains ArtifactMismatch | SpecMismatch | RepNotReproduced. context_state gains nullary ContextBundleInconsistent, and campaign_obstruction gains nullary InconsistentContextBundle. Their encodings are respectively "context_bundle_inconsistent" and "inconsistent_context_bundle".

For completed stage 1 with pending candidates and CtxNotNeeded, replay reports ContextBundleInconsistent, marks every pending stage-2 slot NotRun, and returns InconsistentContextBundle with repair obligation reconstruct_or_supply_context_bundle. No context finding is attached. This is distinct from legitimate terminal stage-1 exhaustion. The type split prevents injecting the new obstruction into CtxUnavailable or PreflightFail.

The specification correction, encoding alternatives and T30 are ratified. The unchanged implementation amendment document and input-package documents retain their historical proposal labels as provenance; this report records their acceptance. Historical Revision-14 freeze/open statements and draft headers are superseded only as to status and the explicit Revision-15 delta, not otherwise rewritten. No other semantic change is approved.

## Consistency decision

Run 15 is a PASS for a bounded delta review carrying forward the recorded Run-14 baseline. PHASE_0_CONSISTENCY_AUDIT.md records the checks and limitations. Run 14 is preserved as PHASE_0_CONSISTENCY_AUDIT_RUN14_ARCHIVE.md. This is not a newly executed full historical audit or a full implementation-verification claim.

## Evidence and limits

The closure-input archive SHA-256 is 7c67231215918e9ff50f1a8199709f87b6c656c47b416c80b4b10560357299f9; all 10 manifest entries pass. The implementation reference is unit1a_preclosure_compile_candidate_r4.zip, SHA-256 d39db6c5392013a2ac6438e2bd82b74990985e3e5a2679e884cd841f4945139f; its 33 manifest entries were independently verified. The three patches have now been independently applied and compared byte for byte with revised/.

T1/A1 statements and proof text were inspected and match the specified claims. The kernel is byte-identical to r2. The repaired REP1 proof chain was inspected, including its explicit stage2_witness_index_contract premise. No independent coqc, coqchk, Print Assumptions or OCaml test execution is claimed. Closed under the global context, as reported by the author, does not discharge explicit theorem premises.

The complete author-prepared ledger follows below, preserved without deletion. Reviewer qualifications take precedence over its attribution wording: A10 does not establish independent access to the remote shared folder; A11 is now independently confirmed; B7's -w +8 invocation is an author report not shown in the Makefile. Claims that proofs are Qed-proved in the ledger mean source inspection on the reviewer's side and author-reported machine checking, not a second independent build.

## Open Phase 1 work

- Prove T2_sound, T2_complete, stage1_over_is_terminal, exact_unreachable_v0 and validation_fuel_obstructed_unreachable_when_sufficient. All five remain Admitted; their truth is not established merely by printing their assumptions.
- Implement primitive_ops and establish its required contracts, including stage2_witness_index_contract, and the correspondence to the semantic kernel and specified execution/boundary behaviour.
- Complete extracted-OCaml compilation, linking and execution with the required arbitrary-precision library. Compilation of the handwritten mirror is not extracted-code verification or a cross-language equivalence proof.
- Complete the previously specified implementation acceptance checks, including capture/replay correspondence, canonical encoding, parser/boundary checks and the cross-language agreement battery.

Closure ratifies the Phase 0 specification and accepts the inspected mathematical-core candidate within these evidence limits. It does not establish a completed verified operational pipeline, execution faithfulness, or completion of Phase 1.

## Author-prepared evidence ledger, reproduced verbatim

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
