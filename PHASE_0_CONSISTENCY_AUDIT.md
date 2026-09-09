# Phase 0 consistency audit: Run 15

Date: 2026-09-06
Reviewer: ChatGPT/Codex, designated reviewer in this conversation, separate from the implementation-author role.
Decision: PASS, bounded Revision-15 delta review against the recorded Run-14 baseline.

This is not a claim that every historical Run-14 check was independently repeated.
The unmodified Run-14 audit is preserved in PHASE_0_CONSISTENCY_AUDIT_RUN14_ARCHIVE.md.
Its historical open-status statements describe that earlier state.

## Independently performed checks

- Closure-input ZIP SHA-256: 7c67231215918e9ff50f1a8199709f87b6c656c47b416c80b4b10560357299f9. All 10 manifest entries pass.
- All three supplied unified diffs apply to the r4 Revision-14 baseline and reproduce the proposed Revision-15 files byte for byte.
- The supplied amendment is byte-identical to the previously reviewed r4 amendment.
- The new context_state and campaign_obstruction constructors agree across the revised type declarations, slot table, repair obligation, canonical encoding table and T30.
- ctx_reason retains its three original constructors. The r3 invalid unavailable/preflight placements remain excluded by the r4 types.
- The added replay branch follows completed stage 1 with pending candidates. Terminal stage-1 exhaustion remains a preceding terminal branch; no context lookup is required there.
- The new branch produces only NotRun stage-2 slots and a campaign obstruction. The existing verdict precedence therefore yields OBSTRUCTED without any ValidWitness.
- T1/A1, their kernel source, and the trust-boundary premises are unchanged. The r4 REP1 repair remains as previously inspected, with the stage-2 contract explicit.
- The governing documents other than the three revised files are carried forward unchanged. The closure report records precedence over their historical draft/open status text.

## Evidence qualifications

The reviewer has inspected source, not executed Rocq or OCaml verification. The previous local make check attempt stopped at missing coqc. Author-reported build and proof-check results remain external evidence, as detailed in the closure report.

The author-prepared evidence ledger is retained verbatim as input. A10 is independently established only for the supplied archives/local extractions; the remote shared folder was not inspected. A11 is now confirmed by actual patch application and byte comparison. B7's explicit -w +8 invocation is not present in the archived Makefile and is treated as a separately reported author check, not a reproduced command.

## Disposition

No unresolved blocker in the bounded amendment. The amendment is accepted into the reviewer-issued Revision-15 set. The five admitted orchestration obligations, primitive implementations/contracts and extracted-runtime verification remain Phase 1 work. Run 15 does not turn these into proved results.
