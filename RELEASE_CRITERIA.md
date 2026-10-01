# Phase-1 release criteria

**Status: CLOSED. Policy mode: PARAMETRIC (Closure Batch 7, 2026-10-01).**
Closure Batch 5 adopted the release boundary established by the Batch-4B/4C audits.
It supersedes broader concrete-implementation acceptance wording in the historical Phase-0
closure list and specifications. Batch 7 closes this parametric boundary;
Phase 2 remains unauthorised.

## Parametric acceptance boundary

Results are relative to a supplied functional `Policy`, supplied `AuditContext`,
explicit per-input policy binding and semantic-realisation premises, and the
existing manifest, record, transcript and validation contracts. Closure requires:

- kernel closure, `coqchk` and complete fail-closed assumption inspection;
- exact-integer extraction on every normative extracted path;
- the existing canonical manifest/record/transcript-byte checks, executable
  harnesses and finite differential tests, with their exact scope recorded;
- explicit accounting of theorem premises, including section-generalised premises;
- policy realisation identified as an external semantic contract, distinct from
  local equality of opaque orchestration tokens;
- `faithful_transcript` / capture realisation identified separately as an unresolved
  external observation-faithfulness contract;
- review and acceptance of the stated implementation trust and remaining process
  evidence, followed by a final closure disposition.

A concrete target registry, `SyntheticTargetV0`, `rounddiv`, a concrete quantiser,
a byte-to-kernel semantic policy loader and arbitrary external policy interpretation
are **NOT IN PHASE-1 SCOPE**. Their absence is not a Phase-1 blocker. No digest
agreement is used to derive policy identity. The local `policy_binding` premise
is exactly `ti_policy ti = p_committed`; successful validation does not supply it.
No premise is discharged merely by naming it or by reporting kernel closure.

## Current automated gate

Run `make release` from the repository root or `implementation/`. Required steps
stop on failure:

1. Verify every manifest entry and coverage of tracked plus non-ignored untracked
   files, except `MANIFEST.sha256`. The command never refreshes the manifest.
2. Inventory project-owned Rocq source and reject forbidden non-comment tokens.
3. Verify Makefile compilation/`coqchk`/harness coverage against source inventories.
4. Clean build products, compile all formal modules and regenerate extraction.
5. Run `coqchk` on all substantive modules.
6. Inspect every discovered theorem-like declaration and legacy requested obligation;
   reject errors, missing results and unexpected global axioms.
7. Kernel-typecheck the seven formerly injectivity-dependent interfaces against
   explicit local-binding signatures, including their full parameter sequence.
8. Compile OCaml and run every existing harness, retaining hash-mismatch rejection.
9. Parse regenerated OCaml interfaces and required wrappers; reject native `int`
   interface types and historical mirror dependencies/imports/linking.
10. Run the finite Rocq/OCaml comparator, including currently executable verdicts
    and separately labelled large-natural exact `Z` reference cases.
11. Run the bounded byte/parser/binding harness and independent Python canonical
    transcript/digest-input vectors; confirm byte integration executed.
12. Validate execution coverage and generated numeric/byte/interface evidence;
    recheck source-manifest integrity after building.

Python 3, GNU make, Coq 8.18.0, OCaml 4.14.1 and the existing Zarith/sha build
dependencies are required. Existing `OCAML_LIB`, `ZARITH` and `SHALIB` overrides
remain available. Dune is not part of the build.

Ignored `implementation/release-audit/` contains `summary.json`, `inventory.json`,
`integer-correspondence.json`, `differential.json`, the differential oracle source
and log, `byte-vectors.json`, `clean.log` and `check.log`. The summary reports
`policy_mode: PARAMETRIC` and `concrete_semantic_policy_loader: NOT_IN_PHASE1_SCOPE`,
and records `release_status: CLOSED` only after all required checks and the final
manifest verification succeed. It invalidates a prior passing summary before
required checks; failure returns nonzero without CLOSED evidence. Counts come from
source inventories, interface declarations, harness discovery and recorded test execution.
For an uncommitted run the SHA identifies the base commit; dirty status and the
manifest digest identify the checked working-tree boundary.

`make gate-tests` runs all adversarial gate regressions in temporary fixtures:
real Coq missing-name/axiom failures, exit-zero diagnostics, omitted coverage,
manifest corruption, failing make, native integer/mirror dependencies, missing
or mismatched differential/byte evidence, and an added renamed universal premise
in a policy interface. Gate regressions are separate from the OCaml harness count.
They are required for this batch's verification and final release review.

When intentionally changing source, update `MANIFEST.sha256` separately as a
reviewable change. A stale manifest must fail release; automatic regeneration
inside the gate would defeat this check.

## Closure disposition and retained limits

**CLOSED:** Batch 7 confirms the repaired extraction inventory and accepts current
evidence, all public theorem premises and the supported parametric API boundary.
No BLOCKING item remains. Bounded harness coverage and retained parser/loader/`to_cv`,
domain, metadata/retrieval, policy-realisation and faithfulness contracts remain
explicit; their discharge is not inferred from passing checks. Reproducibility
acceptance is limited to local clean-build evidence with recorded toolchain/source
metadata. CI/dependency locking and byte-identical dependency reproducibility remain
documented residuals. The SHOULD FIX items below are advisory, not closure conditions;
their retention does not claim that the suggested work was performed.

**SHOULD FIX:** relocate root history/batch reports in a separate mechanical
cleanup, preserving references and source-manifest coverage; consider additional
nonempty pipeline coverage within the existing parametric scope. Current tests
exercise an empty integrated campaign and separate witness/Stage-2 harnesses.
This is a test-coverage limit, not a requirement to invent a concrete policy.

**DOCUMENTED RESIDUAL:** policy realisation; unresolved transcript faithfulness;
trusted extraction/compiler/runtime/crypto/I/O and handwritten bounded ASCII
adapters; raw bigint/domain refinements; finite-case rather than general
executable correspondence; absent full Unicode/operational-config loading. These
must remain visible in any release claim. Publishing, tagging and pushing require
separate authorisation.

See [TRUST.md](TRUST.md), [NONCLAIMS.md](NONCLAIMS.md) and
[PHASE_1_STATUS.md](PHASE_1_STATUS.md). Historical unit reports retain their dated
premises and review dispositions; current policy interfaces are the Batch-5 ones.
