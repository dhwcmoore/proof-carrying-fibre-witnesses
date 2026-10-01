# Proof-Carrying Fibre Witnesses for Learned Observation Regimes

PCFW verifies claim conditions relative to a formally specified learned observation
regime; it does not thereby verify the learned system in its entirety.

**Phase 1 is CLOSED. Its release boundary is PARAMETRIC. Phase 2 is unauthorised.**
Results are relative to a caller-supplied semantic `Policy` and `AuditContext`,
explicit local policy binding and semantic-realisation premises, and the existing
manifest, record, transcript and validation contracts. Phase 1 does not supply a
concrete semantic policy loader or interpret arbitrary policy bytes.

Phase 1 is closed as a parametric proof-carrying verification framework.
Kernel-checked results hold relative to explicitly supplied semantic policy,
audit context, policy-realisation and transcript-faithfulness premises. The release
includes fail-closed assumption auditing, exact-integer extracted execution on
the identified normative paths, canonical artefact checks, adversarial gate tests
and repeatable local release evidence. It does not claim concrete policy
realisation, physical observation faithfulness, whole-model verification or
certification.

| Document | Purpose |
|---|---|
| [TRUST.md](TRUST.md) | Kernel evidence, executable evidence, external premises and implementation trust |
| [NONCLAIMS.md](NONCLAIMS.md) | Limits of the public claim |
| [RELEASE_CRITERIA.md](RELEASE_CRITERIA.md) | Current parametric acceptance boundary and fail-closed gate |
| [implementation/README.md](implementation/README.md) | Exported API, build and implementation details |

Run `make check` for formal compilation, `coqchk`, extraction regeneration,
complete assumption inspection, policy-interface checks, all OCaml harnesses,
and the integer, differential and byte gates. Run `make gate-tests` for adversarial
checks of the gates. Run `make release` for manifest verification and a clean full
check, with generated evidence in `implementation/release-audit/summary.json`.
Required failures stop the gate. A passing release records the Batch-7
**CLOSED** disposition; a failed run does not emit CLOSED evidence.
Kernel closure does not discharge theorem premises; test agreement does not prove
general executable correspondence.

## Historical specifications and evidence

Phase 0 closed at Revision 15: [closure report](PHASE_0_CLOSURE_REPORT.md).
The [charter](PROJECT_CHARTER.md), [definitions](CLAIM_AND_DEFINITIONS.md) and
[audit specification](AUDIT_POLICY_AND_EVIDENCE.md) preserve the broader design.
`SyntheticTargetV0`, `rounddiv`, positive-width/no-clamping concrete quantisation
and a closed target registry are historical specifications, not implemented
Phase-1 release features. Current scope is governed by [RELEASE_CRITERIA.md](RELEASE_CRITERIA.md).

The [status ledger](PHASE_1_STATUS.md) and [implementation history](IMPLEMENTATION_STATUS.md)
retain dated dispositions. The [Batch-2](PHASE_1_EXACT_INTEGER_CORRESPONDENCE.md)
and [Batch-3](PHASE_1_BYTE_BINDING.md) reports preserve their tested boundaries;
their former policy-injectivity blocker is superseded by the
[Batch-5 parametric report](docs/audits/phase1/BATCH_5_PARAMETRIC_RELEASE.md). Relocating the
existing root history reports is deferred to a separate documentation cleanup.

## Authorship

Sole author: Duston Moore &lt;dhwcmoore@gmail.com&gt;. Licensed under Apache-2.0
(see [LICENSE](LICENSE) / [NOTICE](NOTICE)).
