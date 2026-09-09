# Phase 0 Closure Package — r1

**Author-prepared input for the designated reviewer. Phase 0 is OPEN.**

This package does not close Phase 0. It assembles the material the designated
reviewer needs in order to (a) accept the r4 context-bundle amendment into the
governing set as **Revision 15**, and (b) issue `PHASE_0_CLOSURE_REPORT.md` in the
shared project folder. Only the reviewer role issues that report; the
implementation-author role (this package's author) does not, and has not.

Nothing here has been applied to the live governing set. The root
`VERDICT_SEMANTICS.md`, `AUDIT_POLICY_AND_EVIDENCE.md` and `THREAT_MODEL.md`
remain at **Revision 14** until the reviewer issues the closure report and the
`revised/` copies replace them.

## Contents

| Path | What it is |
|---|---|
| `CONTEXT_BUNDLE_AMENDMENT.md` | The amendment, already carrying the reviewer's bounded source-review acceptance (r4). |
| `revised/VERDICT_SEMANTICS.md` | Proposed **Revision 15** — full file. |
| `revised/AUDIT_POLICY_AND_EVIDENCE.md` | Proposed **Revision 15** — full file. |
| `revised/THREAT_MODEL.md` | Proposed **Revision 15** — full file (adds T30). |
| `diffs/*.rev14-rev15.diff` | Exact unified diffs, Revision 14 → 15, one per file. |
| `EVIDENCE_LEDGER.md` | What was independently inspected vs. what was executed only on the author's machine. |
| `CLOSURE_REPORT_CHECKLIST.md` | What `PHASE_0_CLOSURE_REPORT.md` must assert. Not a draft of the report. |
| `MANIFEST.sha256` | SHA-256 of every file in this package. |

## Scope of Revision 15

Three governing documents, one concern: the `CtxNotNeeded`-with-completed-stage-1
pairing that a total `replay` must handle but `capture` never produces.

- `ctx_reason` is **unchanged** (`ArtifactMismatch | SpecMismatch | RepNotReproduced`).
- `campaign_obstruction` gains nullary `InconsistentContextBundle`.
- `context_state` gains nullary `ContextBundleInconsistent`.
- §6.4 `CtxNotNeeded` description corrected; §6.5 slot table gains one row; §2.2
  encoding table gains two nullary constructors; THREAT_MODEL gains T30.

No change to the mathematical core (`T1`/`A1`/`E1`), the kernel, the trust
boundary, the claim, or any other governing document. `PHASE_0_DECISIONS.md`,
`PHASE_0_SPECIFICATION_AMENDMENTS.md` and `PHASE_0_CONSISTENCY_AUDIT.md` are
**not** revised here — see `CLOSURE_REPORT_CHECKLIST.md` item 6 for the
consistency-audit decision the reviewer must make.

## Implementation reference

The r4 implementation candidate `unit1a_preclosure_compile_candidate_r4.zip`
(sha256 `d39db6c5392013a2ac6438e2bd82b74990985e3e5a2679e884cd841f4945139f`)
already realises Revision 15's constructors in Rocq and OCaml, with `REP1`
proved. It is a separate artefact; this package is documentation only.

## Reviewer / author separation

- The amendment text and these revised documents were prepared by the
  implementation-author role.
- The bounded source review of r4 (and of this amendment) was performed by the
  designated reviewer.
- The build, proof-checking and test execution were run on the author's machine
  (Coq 8.18.0 / OCaml 4.14.1); the reviewer's environment lacks `coqc`. See
  `EVIDENCE_LEDGER.md`.
- `PHASE_0_CLOSURE_REPORT.md` is to be written and placed in the shared project
  folder by the reviewer role alone.
