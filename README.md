# Proof-Carrying Fibre Witnesses for Learned Observation Regimes

Formal-verification project (Rocq/Coq 8.18.0 + OCaml 4.14.1).

- **Phase 0** is closed at Revision 15 — see [`PHASE_0_CLOSURE_REPORT.md`](PHASE_0_CLOSURE_REPORT.md).
- **Phase 1** is in progress; Phase 2 is not authorised.

## Where to start

| Document | Purpose |
|---|---|
| [`PROJECT_CHARTER.md`](PROJECT_CHARTER.md) | Scope, claim boundary, governance |
| [`CLAIM_AND_DEFINITIONS.md`](CLAIM_AND_DEFINITIONS.md) | What is claimed and the definitions it rests on |
| [`AUDIT_POLICY_AND_EVIDENCE.md`](AUDIT_POLICY_AND_EVIDENCE.md) · [`VERDICT_SEMANTICS.md`](VERDICT_SEMANTICS.md) · [`THREAT_MODEL.md`](THREAT_MODEL.md) · [`TRUST_BOUNDARY.md`](TRUST_BOUNDARY.md) | Normative specification (frozen at Rev 15) |
| [`IMPLEMENTATION_STATUS.md`](IMPLEMENTATION_STATUS.md) · [`PHASE_1_STATUS.md`](PHASE_1_STATUS.md) | Current implementation status ledger |
| [`implementation/`](implementation/) | Rocq development + OCaml harnesses |
| [`TRUST.md`](TRUST.md) · [`NONCLAIMS.md`](NONCLAIMS.md) · [`RELEASE_CRITERIA.md`](RELEASE_CRITERIA.md) | Current implementation evidence, residual trust and release gate |

## Building

```
cd implementation
make check
```

runs the project-owned source-token gate, `coqc` / `coqchk`, extraction
regeneration, a fail-closed assumption audit of all substantive theorem-like
declarations plus the legacy requested obligations, and all existing OCaml
harnesses, the structural bigint/mirror audit and the finite differential
comparator. See [the Batch-2 evidence report](PHASE_1_EXACT_INTEGER_CORRESPONDENCE.md).
The [Batch-3 byte-binding report](PHASE_1_BYTE_BINDING.md) records the bounded
ASCII byte adapters, remaining loader premises and concrete digest-input tests.
Kernel closure does not discharge theorem premises.

From the repository root, `make release` verifies `MANIFEST.sha256`, cleans,
runs the full check and records mechanical evidence in
`implementation/release-audit/summary.json`. It fails on any required failure
and always leaves Phase 1 **OPEN / NOT YET CLOSED**. The manifest covers tracked
and non-ignored untracked source/document files, excluding itself. The release
command verifies it without regenerating it. See [`RELEASE_CRITERIA.md`](RELEASE_CRITERIA.md).

## Authorship

Sole author: Duston Moore &lt;dhwcmoore@gmail.com&gt;. Licensed under Apache-2.0
(see [`LICENSE`](LICENSE) / [`NOTICE`](NOTICE)).
