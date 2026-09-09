# Prior Work and Provenance

This project's architecture was informed by four earlier formal-methods projects
by the same author, **Duston Moore**. This document records what was taken from
each and — importantly — what was **not**.

**No source code, formal-definition text, documentation prose, or project-specific
build configuration from any of these projects is incorporated into this
repository.** They are conceptual precedents and structural references. Each is
licensed AGPL-3.0.

Under the frozen reuse dispositions, no source code, formal-definition text,
documentation prose, or project-specific configuration from these AGPL-3.0
projects is incorporated into version 0. The new project is therefore licensed
independently under Apache-2.0 (`PROJECT_CHARTER.md` §8), subject to its declared
dependency obligations (`THIRD_PARTY_NOTICES.md`).

The evidenced, per-entry inspection and decision are in `PHASE_0_REUSE_AUDIT.md`
and `PHASE_0_REUSE_VERIFICATION.md`.

## Proof-Carrying Exactness (PCE) — `dhwcmoore/proof-carrying-exactness`

- **Conceptual precedent:** the untrusted-generator / trusted-verifier split; the
  fail-closed independent-checker posture (a single rejection path, no shared
  solver logic, an explicit written independence boundary); the extraction
  *discipline* (extract only the computational function, use only official
  realisation files, itemise the extraction trusted computing base, regenerate
  rather than commit the extracted code).
- **Not used:** `ExtractR21.v` is not copied — this project's extraction
  configuration is authored independently against its own definitions using
  Rocq's standard `ExtrOcamlZBigInt` facility. `r21_format.ml` is not adapted —
  the wire format is written from this project's frozen schema. The exact-rational
  (`Q`) numeric core is not used; this project uses exact integers (`Z`).

## Proof-Carrying Stream Exactness (PCSE) — `dhwcmoore/proof-carrying-stream-exactness`

- **Structural reference:** the deliverable topology (`PROJECT_CHARTER`,
  `VERDICT_SEMANTICS`, `TRUST_BOUNDARY`, `THREAT_MODEL`, `NON_CLAIMS`,
  `CERTIFICATE_FORMAT`, `MATHEMATICAL_SCOPE`, `THEOREM_LADDER`, `CLOSURE_MODEL`);
  the six-layer trust-boundary shape and its "the adapter code is untrusted, its
  soundness theorem is trusted" device; the proof habit of a typed witness record
  per failure mode, each with a theorem that it precludes the positive property.
- **Not used:** no `.md` prose is copied — the deliverables are authored fresh
  against the shared outline. `ByteString.v` is not reused in v0 (the semantic
  kernel operates on integers, not bytes).

## Proof-Carrying Observability Audit (PCOA) — `dhwcmoore/proof-carrying-observability-audit`

PCOA embeds a copy of `dhwcmoore/lift-descent-exactness`.

- **Conceptual precedent:** the factorisation-equivalence proof architecture
  (vanishing on the kernel ⇔ factorisation through the image ⇔ a unique induced
  map); the `classify` / `_condition` / `_unique` / `_iff` / trichotomy
  lemma-layout convention; the R-numbered theorem-ladder convention.
- **Not used, permanently for v0:** `AdmissibilityGate` and its gated verdict type
  — its `GatedInadmissible` denotes protocol rejection, a different semantic level
  from this project's `INADMISSIBLE` (witnessed non-factorisation); importing it,
  even with a renamed constructor, would carry a verdict vocabulary that inverts
  the central term. The result types `BundleResult` / `WitnessResult` /
  `CampaignVerdict` are defined from first principles. `QDescentFactorisation.v` is
  a *linear* factorisation theorem (`QLinearMap` over `Qc`) with no assumption-free
  generic lemma to lift; the generic witness-implies-non-factorisation theorem is
  proved afresh over `FibreConstant`.

## VeriBound (VBF) — `dhwcmoore/veribound-formal-verification`

- **Conceptual reference:** the classification-theorem shape (soundness,
  complete coverage, mutual exclusion) for domain-boundary predicates; fail-closed
  boundary-handling ideas.
- **Not used:** the Flocq / `float64` numeric core — it reintroduces floating
  point into the trusted path, which this project's exact-integer v0 design
  forbids.

## Verification evidence

Every prior source proposed for any form of reuse was built and checked at
Coq/Rocq 8.18.0: `coqc` builds succeeded; `coqchk` reported no project-introduced
axioms; `Print Assumptions` returned "Closed under the global context" for the
inspected theorems; every inspected git repository is single-author
(`dhwcmoore@gmail.com`). See `PHASE_0_REUSE_VERIFICATION.md` for the per-entry
rows.
