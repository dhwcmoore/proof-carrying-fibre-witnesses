# Phase 0 — Reuse Verification Report (§K.4b, §K.4c)

**Companion to:** `PHASE_0_REUSE_AUDIT.md` §5 (manifest) and §6 (checklist).
**Status: CLOSED.** §K.4b and §K.4c are settled.

## FINAL DECISION (frozen)

**Every manifest entry is authored afresh. Nothing is copied — no source, no
formal-definition text, no documentation prose, no build configuration. Project
licence: Apache-2.0.**

| Entry | Final disposition |
|---|---|
| M2 `ExtractR21.v` | Author the extraction configuration independently using Rocq's standard `ExtrOcamlZBigInt` facility. Not copied. |
| M8 `QDescentFactorisation.v` | Reject. Re-prove `(T1)` afresh over `FibreConstant`. |
| M9 `r21_format.ml` | Write the wire-format implementation from this project's frozen schema. Not adapted. |
| M10 `r21_verifier.ml` | Conceptual precedent only (fail-closed architecture, written independence boundary). |
| M11 `ByteString.v` | No v0 reuse. Reconsider only if a later kernel theorem requires bytes. |
| PCOA `AdmissibilityGate` | Permanent v0 rejection. No import, no constructor rename. |

Licensing consequence: none. Under these dispositions no AGPL-covered text is
incorporated, so the Apache-2.0 choice is unconstrained
(`PROJECT_CHARTER.md` §8.1).

---

**Scope of the evidence pass below:** manifest entries M2, M8, M9, M10, M11 —
every entry that was *proposed* for theorem, source, or configuration reuse.

> The per-entry rows record the *inspection evidence* (builds, `coqchk`,
> assumptions, ownership, semantic fit) and, in the "Evidence permitted" line,
> what the evidence *would have allowed*. The **decision** is the table above:
> nothing is copied. The mode labels (`mode 5`, `mode 4`, …) in the rows describe
> the evidence category, not an adopted disposition.

## Toolchain used

| Tool | Version |
|---|---|
| Coq / Rocq | 8.18.0 |
| OCaml | 4.14.1 |
| zarith | 1.14 |
| yojson | 3.0.0 |
| sha | 1.15.4 |

`ByteString.v` (M11) declares its baseline as "Coq 8.18.0" — exact match. All
builds and checks below were run at that toolchain.

## Ownership — repository level

Every git repository inspected has a **single author across its entire history**:
`Duston Moore <dhwcmoore@gmail.com>`. No file among M2/M8/M9/M10/M11 carries a
file-level copyright or SPDX header; the governing licence for each is therefore
the repository `LICENSE`.

| Repo | Licence | Commit |
|---|---|---|
| `proof-carrying-exactness` (PCE) | AGPL-3.0 | `01b3114411c0d12520196bfaff36c14b41d2cad4` |
| `proof-carrying-stream-exactness` (PCSE) | AGPL-3.0 | `164ca7042134fd91e149807bddcc5a0b28e8fe83` |
| `proof-carrying-observability-audit` (PCOA) | AGPL-3.0 | `6851293a5421a3131d6bb6331d1b6d5b342b0d70` |

**One ownership gap:** PCOA's `kernel/` is a snapshot copy of
`dhwcmoore/lift-descent-exactness` (AGPL-3.0). The local archive
(`/data/lift-descent-exactness-main.zip`, dated 2026-08-03) contains **no `.git/`
history and no `CITATION.cff`**, so the full contributor list of that upstream
cannot be confirmed from local evidence. It must be checked against the GitHub
repository before any mode-3 copy from it. This gap only affects M8, which is
rejected for copying anyway (below).

## Dependency licences

| Dependency | Licence | Used by |
|---|---|---|
| Coq stdlib + official extraction realisation files | LGPL-2.1-only | M2, M8, M11 |
| zarith | LGPL-2.0-only WITH OCaml-LGPL-linking-exception | M2 (extracted target), M9, M10 |
| yojson | BSD-3-Clause | M9, M10 |
| sha | ISC | M9, M10 |

None of these constrains the project licence choice (all permit use under any
downstream licence; the OCaml-LGPL linking exception covers static linking).

---

## Per-entry rows

### M2 — PCE extraction configuration → **author afresh** (evidence category: mode 5)

| Field | Finding |
|---|---|
| Proposed mode | 5 — build / extraction configuration reuse |
| Repo / commit / file | PCE `01b31144` — `rocq/ExtractR21.v` (requires `rocq/ExactRationalRepairOrSeparator.v`) |
| Build result | `make extract-r21` → exit 0; regenerates `ocaml/r21_extracted.ml` / `.mli` from a clean state |
| `coqchk` result | `coqchk ExactRationalRepairOrSeparator` → "Modules were successfully checked"; **no `Axioms:` section** |
| Assumption inventory | `Print Assumptions compute_repair_or_separator` → **"Closed under the global context"** (zero axioms, zero admits) |
| Forbidden-token scan | `ExtractR21.v`, `ExactRationalRepairOrSeparator.v`: no `Admitted` / `admit` / `Axiom` / `Parameter` / `Hypothesis`. Repo enforces this repo-wide via `make check-rocq-scan` + `check-rocq-trust`. |
| Extraction result | Produces `Big_int_Z.big_int` for `Z` / `nat` / `positive` (confirmed in generated `.mli` and `.ml`). Uses only `ExtrOcamlBasic`, `ExtrOcamlZBigInt`, `ExtrOcamlNatBigInt` — **no project `Extract Constant` / `Extract Inductive` directives.** |
| Fixed-vector agreement | n/a for the configuration itself (see M10) |
| Contributor / ownership | `git log -- rocq/ExtractR21.v` → sole author Duston Moore. Whole-repo history: single author. |
| Source licence | AGPL-3.0 (repo `LICENSE`; no file header) |
| Dependency licences | Coq realisation files LGPL-2.1-only; extracted code targets zarith (LGPL-2.0 + linking exception) |
| Semantic-compatibility finding | **Positive.** `Extraction Language OCaml` + `Extraction "<path>" <fn>` over the three official realisation files is exactly what §E.1 / §F.1.1 require. `Z → Big_int_Z.big_int` is the same-representation Zarith mapping the integer-model decision assumes — no runtime conversion. Only adaptation: the extracted function is *our* kernel checker, not `compute_repair_or_separator`. |
| **Final decision** | **Author afresh — not copied.** Write the extraction directive block independently against this project's definitions using the standard `ExtrOcamlZBigInt` facility; transcribe the extraction-TCB itemisation into `TRUST_BOUNDARY.md` §F.1.1 in our own words. |
| Evidence permitted | Mode-5 reuse of the directive block would have been sound (clean build, no axioms). Not taken. |

### M8 — PCOA generic factorisation lemma → **reject; re-prove afresh** (evidence category: mode 3 candidate)

| Field | Finding |
|---|---|
| Proposed mode | 3 — theorem / definition reuse (candidate) |
| Repo / commit / file | PCOA `6851293a` — `kernel/rocq/QDescentFactorisation.v` (kernel copied from `lift-descent-exactness`) |
| Build result | `kernel/` `make` → exit 0; 41 `.vo` present and consistent; `QDescentFactorisation.vo` builds |
| `coqchk` result | `coqchk LiftDescent.QDescentFactorisation` → "Modules were successfully checked"; **no `Axioms:` section** |
| Assumption inventory | `Print Assumptions kernel_vanishing_iff_ambient_factorisation` → **"Closed under the global context"** |
| Forbidden-token scan | `kernel/rocq/*.v`: no `Admitted` / `admit` / `Axiom` hits |
| Extraction result | n/a — the results are propositional, not extracted |
| Contributor / ownership | PCOA git log for the file → sole author Duston Moore. **Upstream `lift-descent-exactness` full contributor history not verifiable locally** (snapshot archive, no `.git/`). |
| Source licence | AGPL-3.0 (PCOA and lift-descent-exactness both) |
| Semantic-compatibility finding | **Negative.** The file header states it proves the **finite-rational** form and explicitly *not* "generalisation beyond finite rational coordinate spaces". Every result is over `QLinearMap` / `Qc` / `image_subspace D` / elimination-derived projections. "Factors through" here means **linear** factorisation through `im D`. Our `M̃_{A,P}` is a nonlinear map on `list Z`, `Φ_P : X → 𝔹`, and `FibreConstant` has no linear structure. There is **no assumption-free generic lemma** to lift. |
| **Final decision** | **Reject.** Re-prove `(T1)` afresh over `FibreConstant`. PCOA's proof *architecture* (vanishing-on-kernel ⇔ factor-through-image ⇔ unique induced map) is a conceptual precedent only; nothing is imported. Upstream-authorship gap is moot. |
| Evidence permitted | Nothing — the file is a *linear* factorisation theorem with no assumption-free generic lemma to lift (semantic fit negative). |

### M9 — PCE `r21_format.ml` → **author afresh** (evidence category: mode 4)

| Field | Finding |
|---|---|
| Proposed mode | 4 — source-code copying / close adaptation |
| Repo / commit / file | PCE `01b31144` — `ocaml/r21_format.ml` |
| Build result | `make check-r21-ocaml` → exit 0 (compiles with `r21_verifier.ml` against `zarith,yojson,sha` from a clean state) |
| `coqchk` result | n/a (OCaml) |
| Assumption inventory | n/a. Note: the module's own header places it **outside the mathematical-soundness TCB** — it is provenance-binding only (canonical serialisation / schema / hashing); the verdict does not depend on it being correct, only on digests matching. |
| Forbidden-token scan | n/a (OCaml) |
| Extraction result | n/a |
| Fixed-vector agreement | Module provides `input_digest` canonicalisation; PCE `tests/test_r21_cross_language_agreement.py` exercises Python↔OCaml digest + verdict agreement. **Not run here** (needs the Python/pytest environment); PCE CI runs it. Must be re-run after adaptation. |
| Contributor / ownership | `git log -- ocaml/r21_format.ml` → sole author Duston Moore; whole-repo single author; no file header |
| Source licence | AGPL-3.0 |
| Dependency licences | yojson BSD-3-Clause, zarith LGPL-2.0 + linking exception, sha ISC |
| Semantic-compatibility finding | **Partial fit.** Structure — schema tags, duplicate-key rejection, closed-schema validation, resource limits, canonical `(D,r)` digest — maps directly onto our bundle-processing layer (§C.1) and the untrusted-generator / trusted-verifier split. Mismatches: built around `Zarith.Q` (rationals) where we need `Zarith.Z` (integers); schema is R21's `repair-or-separator/v1`, ours is the fibre-witness bundle. This is adaptation, not verbatim copy: reuse the module *shape* and the canonicalisation discipline; rewrite the schema and swap `Q → Z`. |
| **Final decision** | **Author afresh — not adapted.** Write the wire-format module (schema tags, duplicate-key rejection, closed-schema validation, resource limits, canonical digest) from this project's frozen schema, over `Zarith.Z`. The cross-language agreement battery is an implementation-phase acceptance obligation (`AUDIT_POLICY_AND_EVIDENCE.md` §10). |
| Evidence permitted | Mode-4 adaptation was viable (clean build; module is outside the soundness TCB) but only a partial semantic fit (`Zarith.Q` vs `Zarith.Z`; R21 schema vs ours). Not taken. |

### M10 — PCE `r21_verifier.ml` skeleton → **conceptual precedent only** (evidence category: mode 1)

| Field | Finding |
|---|---|
| Proposed mode | 1 (conceptual) or 4 (if the skeleton / helpers are copied) |
| Repo / commit / file | PCE `01b31144` — `ocaml/r21_verifier.ml` |
| Build result | `make check-r21-ocaml` → exit 0 |
| `coqchk` / assumptions / tokens | n/a (OCaml) |
| Contributor / ownership | sole author Duston Moore; no file header |
| Source licence | AGPL-3.0; deps as M9 |
| Semantic-compatibility finding | **Architecture fits; body does not.** The fail-closed pattern — a single `Reject` exception caught once at the top of `verify`, direct recomputation, no solver import, an explicit written independence boundary — is exactly our verifier's posture. But our verifier re-executes the integer model and evaluates the registry predicate (a much larger body), and it invokes the *extracted kernel* rather than recomputing "two certificate equations". No line-level correspondence. |
| **Final decision** | **Conceptual precedent only.** Follow the fail-closed architecture (single rejection path, no solver import, written independence boundary); write our own verifier. No helper functions copied. |

### M11 — PCSE `ByteString.v` → **no v0 reuse; re-derive if ever needed** (evidence category: mode 3 conditional)

| Field | Finding |
|---|---|
| Proposed mode | 3 — theorem / definition reuse (conditional) |
| Repo / commit / file | PCSE `164ca704` — `rocq/ByteString.v` |
| Build result | `coqc -Q rocq PCSE rocq/ByteString.v` → exit 0 |
| `coqchk` result | `coqchk -Q . PCSE PCSE.ByteString` → "Modules were successfully checked"; **no `Axioms:` section** |
| Assumption inventory | `Print Assumptions byte_string_eq_dec` → "Closed under the global context"; same for `append_byte_string_assoc` |
| Forbidden-token scan | none |
| Extraction result | Not run; `list byte` + `list_eq_dec byte_eq_dec` are pure stdlib and extract cleanly by construction |
| Contributor / ownership | sole author Duston Moore; whole-repo single author; no file header |
| Source licence | AGPL-3.0 |
| Dependency licences | Coq stdlib LGPL-2.1-only |
| Semantic-compatibility finding | **Clean fit if needed — but probably not needed.** The file is ~40 lines of stdlib wrappers (`list byte`, `++`, `concat`, assoc / identity lemmas, `list_eq_dec`), fully generic, zero assumptions, exact toolchain match. However, the v0 design keeps digest binding as a **system-binding obligation outside the kernel** (§F.3); the semantic kernel operates on `list Z`, not bytes. Unless Phase 1 finds a kernel-level theorem that needs canonical bytes, the kernel needs no `ByteString`. |
| **Final decision** | **No v0 reuse.** The semantic kernel operates on `list Z`, not bytes; digest binding is a system-binding obligation outside the kernel (`TRUST_BOUNDARY.md` §F.3). If a later kernel theorem genuinely needs a byte substrate, re-derive the ~40 lines of stdlib wrappers rather than copy. |
| Evidence permitted | Clean build, zero axioms, exact toolchain match — a mode-3 transcription would have been sound, but the need does not exist in v0. |

---

## Licence-consequence summary

Under the frozen decision (top of this document), **nothing is copied**, so
licensing is not engaged for any entry:

| Entry | Final decision | Text incorporated? |
|---|---|---|
| M2 | author extraction config afresh via standard `ExtrOcamlZBigInt` | none |
| M8 | reject; re-prove `(T1)` afresh | none |
| M9 | write wire format afresh from frozen schema | none |
| M10 | conceptual precedent only | none |
| M11 | no v0 reuse; re-derive if ever needed | none |

Mode-1 / mode-2 items elsewhere (extraction discipline as method, PCSE deliverable
topology, `Admissibility.v` / `FailureWitness.v` proof-organisation patterns, PCOA
lemma-layout convention, trust-boundary shape, VBF theorem-shape) adopt structure
and method, not text — licensing not engaged.

Rationale and charter language: `PROJECT_CHARTER.md` §8; `PRIOR_WORK.md` records
influence; `THIRD_PARTY_NOTICES.md` records dependency licences.

## Caution on "structural template" (per the freeze review)

Following the same **abstract document organisation** — the section list of
`VERDICT_SEMANTICS.md`, the six-layer trust-boundary shape, the R-numbered theorem
ladder convention, the "typed witness record + preclusion theorem" proof habit —
is licence-neutral: it is method and structure, not expression.

**Copying actual prose, template files, or substantial expressive passages from
PCSE/PCOA `docs/` is not licence-neutral** and would engage AGPL. The seven
deliverables must therefore be **authored fresh against the shared outline**, not
produced by copying the prior projects' `.md` files and editing them. The audit
manifest records these as mode 2 (structural) explicitly on that basis; any entry
that slips into copied prose must be reclassified mode 4.

## Status

§K.4b and §K.4c are **closed**. All dispositions are "author afresh"; the project
licence is **Apache-2.0** (`PROJECT_CHARTER.md`).

Carried forward (not Phase 0 blockers):

1. **Cross-language digest+verdict agreement battery** — reassigned as an
   acceptance obligation on the wire-format / standalone-verifier implementation
   phase. It must eventually cover: canonical policy encoding agreement; candidate
   encoding agreement; SHA-256 digest agreement; integer parsing agreement;
   rejection of malformed and duplicate-key JSON; policy-binding agreement;
   witness-result agreement; certificate encoding agreement; adversarial boundary
   vectors; and Python↔OCaml agreement over a generated corpus. It cannot run
   during Phase 0 because the implementation does not exist; Phase 0 records the
   obligation, the implementation phase discharges it.
2. **lift-descent-exactness upstream authorship** — only relevant if a *future*
   phase wants the linear kernel; not required for v0 (M8 rejected).

This report and the `PHASE_0_REUSE_AUDIT.md` §5 manifest are **ratified**; the
consistency audit treats both as records, not open items.
