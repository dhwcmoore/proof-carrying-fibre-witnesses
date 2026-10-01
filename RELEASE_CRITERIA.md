# Phase-1 release criteria

**Status: OPEN / NOT YET CLOSED.** Closure Batches 1–2 establish a gate for current
evidence. Its success does not close outstanding Phase-1 acceptance obligations.

## Current automated gate

Run `make release` from the repository root or `implementation/`. Required steps
stop on failure:

1. Verify every manifest entry and coverage of tracked plus non-ignored untracked
   files, except `MANIFEST.sha256` itself. The command never refreshes the manifest.
2. Inventory project-owned Rocq sources; reject forbidden non-comment tokens.
3. Verify Makefile module/`coqchk`/harness coverage against source inventories.
4. Clean build products, then compile all formal modules and regenerate extraction.
5. Run `coqchk` on all substantive modules.
6. Inspect every discovered theorem-like declaration and each legacy requested
   obligation; reject errors, missing results and unexpected global axioms.
7. Compile OCaml and run every existing harness.
8. Parse regenerated OCaml interfaces and required wrappers; reject native `int`
   interface types and historical mirror dependencies/imports/linking.
9. Run the finite Rocq/OCaml differential comparator, including all currently
   executable verdicts and explicitly labelled large-natural `Z` reference cases.
10. Validate execution coverage, generated numeric evidence and source-manifest
    integrity after building.

Python 3, GNU make, Coq 8.18.0, OCaml 4.14.1 and the existing Zarith/sha build
dependencies are required. Library directories retain the existing `OCAML_LIB`,
`ZARITH` and `SHALIB` overrides. Dune is not part of this build.

Generated evidence lives in ignored `implementation/release-audit/`:
`summary.json`, `inventory.json`, `integer-correspondence.json`,
`differential.json`, `differential-oracle.v`, `differential-oracle.log`,
`clean.log`, and `check.log`. An old passing
summary is replaced at the start; failure returns nonzero and records failure.
Counts are discovered, not acceptance thresholds hardcoded into the gate.
For an uncommitted run the summary's SHA identifies the base commit; dirty status
and the manifest digest identify the checked working-tree boundary.

`make gate-tests` exercises negative cases in temporary fixtures, including real
Coq missing-name/axiom inspections, exit-zero error simulations, omitted coverage,
manifest corruption, a failing make command, structural native types/mirror
dependencies, and missing/mismatched differential results. It does not alter project formal
source. These gate regressions are separate from the OCaml harnesses, whose count is generated.

When intentionally updating source, update `MANIFEST.sha256` as a separate
reviewable change to cover the resulting source set. A stale manifest must fail
release; automatic regeneration inside the gate would defeat this check.

## Still required before Phase-1 closure

- Review the arbitrary-precision/domain boundary and bounded integration evidence
  from Batch 2. The full model/witness executable composition remains outstanding.
- Resolve the recorded parser, canonical encoding, concrete transcript-digest,
  loader/artifact binding and capture/replay acceptance obligations.
- Review coverage beyond Batch 2’s finite differential cases; these do not supply
  a general correspondence theorem or huge unary-natural Gallina evaluation.
- Account explicitly for `faithful_transcript` and all retained premises; do not
  rename weaker checks as faithfulness.
- Complete reproducibility/CI arrangements or justify their exact residual scope.
- Review the final claim/trust/nonclaim boundary and existing Phase-1 ledger.
- Obtain the final closure review. Publishing, tagging and pushing require
  separate authorisation.

See [PHASE_1_STATUS.md](PHASE_1_STATUS.md), [TRUST.md](TRUST.md) and
[NONCLAIMS.md](NONCLAIMS.md). Batch 2 changes extraction mappings and executable tests. It adds no formal
statement, parser, concrete digest, cryptographic algorithm, capture mechanism
or Phase-2 work.
