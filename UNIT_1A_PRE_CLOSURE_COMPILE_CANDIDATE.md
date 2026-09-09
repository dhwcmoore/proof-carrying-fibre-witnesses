# Unit 1A Pre-Closure Compile Candidate — r4

**Status:** technical candidate only. Phase 0 remains open.

This candidate does not issue, imply or presuppose Phase 0 closure. It contains
no `PHASE_0_CLOSURE_REPORT.md` and does not authorise Phase 1. Only the
designated independent reviewer may close Phase 0, separately from the author of
this candidate, by explicit concurrence in the shared project workspace.

The frozen Revision 14 normative set is carried unchanged (only
`IMPLEMENTATION_STATUS.md` gains a dated addendum). All changes below are in
`implementation/`.

## Lineage

- **r2** — semantic kernel `implementation/rocq/FibreWitnessKernel.v` with `Qed`
  proofs of `(T1)` and `(A1)`. Unchanged and module-isolated in r3/r4.
- **r3** — five bounded repairs after a review found
  `REP1_not_run_has_no_witness` false as stated (its `Admitted` made
  `PCFW.Orchestration` inconsistent as an imported theory).
- **r4** — one follow-up: the r3 context reason was added to the shared
  `ctx_reason` type, which also made `CtxUnavailable <it>` constructible (the
  unchanged `CtxUnavailable` branch would then emit it with a fabricated `O1`
  finding). r4 moves the case out of `ctx_reason`.

## Repairs (r3 + r4)

1. **`REP1_not_run_has_no_witness` restated and proved (`Qed`)** over
   `stage2_slots_wf` slot lists (distinct slot indices; every `ValidWitness`
   slot's witness index equals its slot index). `replay_stage2_wf` proves that
   predicate for every `replay` output; `REP1_replay_not_run_has_no_witness` is
   the corollary.
2. **Orchestration-assigned pending indices.** `run_stage1` builds each pending
   submission with `with_pending_index i`; `run_stage1_pending_nodup` proves the
   indices distinct. No index from `op_stage1_check` is trusted.
3. **Stage-2 witness-index contract.** `stage2_witness_index_contract ops`, a
   `primitive_ops` obligation on `op_stage2_check`, used with (2) to close REP1.
   Phase 1 must implement it.
4. **`Stage1Complete ∧ pending ≠ [] ∧ cb = CtxNotNeeded`** now reports via a new
   nullary `campaign_obstruction` `InconsistentContextBundle` and a new nullary
   `context_state` `ContextBundleInconsistent` — OBSTRUCTED, every pending
   stage-2 slot `NotRun`, **no finding of any kind**, obligation
   `reconstruct_or_supply_context_bundle`. `ctx_reason`
   (`ArtifactMismatch | SpecMismatch | RepNotReproduced`) is **unchanged** — it
   is shared by `CtxUnavailable` / `PreflightFail` / `eval_o3`, so
   `CtxUnavailable InconsistentContextBundle` is a type error. Distinct from
   terminal stage-1 fuel exhaustion (`Stage1Stopped` branch, unchanged).
   Proposed frozen constructor-set / canonical-encoding amendment:
   `implementation/CONTEXT_BUNDLE_AMENDMENT.md`.
5. **OCaml mirror** updated to match (orchestration-assigned pending index
   included). `implementation/ocaml/test_context_bundle.ml` (via `make test`)
   exercises the `CtxNotNeeded` path, the real `CtxUnavailable ArtifactMismatch`
   path, and terminal stage-1 exhaustion. `rocq/PrintOrchestrationAssumptions.v`
   + `make assumptions` added.

Five `Admitted` orchestration obligations remain (down from six): `T2_sound`,
`T2_complete`, `stage1_over_is_terminal`, `exact_unreachable_v0`,
`validation_fuel_obstructed_unreachable_when_sufficient`.

## To verify from a fresh extraction

```sh
cd unit1a_preclosure_candidate_r4/implementation
make check
```

Expected (`coqc`/`coqchk`/`coqtop`/`ocamlc` 8.18.0 / 4.14.1):

- all four `.v` files compile; `coqchk` → "Modules were successfully checked"
  for `PCFW.FibreWitnessKernel` and `PCFW.Orchestration`;
- kernel `Print Assumptions` (`T1`, `A1`) → `Closed under the global context`;
  kernel trust scan finds no `Admitted`/`admit`/`Axiom`/`Parameter`/`Hypothesis`;
- `make assumptions`: `REP1_not_run_has_no_witness`,
  `REP1_replay_not_run_has_no_witness`, `replay_stage2_wf` →
  `Closed under the global context`; the five remaining obligations each print
  as their own sole axiom;
- OCaml skeleton compiles; `make test` → `PASS`;
- extraction regenerates `ocaml/extracted_orchestration.{ml,mli}` (not shipped).

Not verified: linking the Coq-*extracted* OCaml against `zarith` (environment
`zarith` ships no `.cmi` files).
