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

## Building

```
cd implementation
make check
```

runs `coqc` / `coqchk` over the Rocq sources, regenerates the extracted OCaml,
prints `Print Assumptions` for every proved obligation, and runs the OCaml test
harnesses. `MANIFEST.sha256` records the SHA-256 of every tracked source and
document file.

## Authorship

Sole author: Duston Moore &lt;dhwcmoore@gmail.com&gt;. Licensed under Apache-2.0
(see [`LICENSE`](LICENSE) / [`NOTICE`](NOTICE)).
