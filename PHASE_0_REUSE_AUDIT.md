# Phase 0 — Reuse Audit

**Companion to:** `PHASE_0_PROPOSED_ANSWERS.md` §B.2 / §K.4, and
`PHASE_0_REUSE_VERIFICATION.md` (the evidenced per-entry pass).
**Status: RATIFIED.** Final dispositions are in §5. **The v0 implementation copies
no source code, formal-definition text, documentation prose, or project-specific
build configuration from any prior project. Project licence: Apache-2.0**
(`PROJECT_CHARTER.md` §8).
**Reading guide:** §3 is the *inspection record* — what each prior component is and
why. §5 is the *decision*. Where §3 and earlier revisions discuss conditional
reuse, adaptation, or "verification still required", that language is a **historical
record of the analysis**; it is superseded by §5 and by
`PHASE_0_REUSE_VERIFICATION.md`.

---

## 0. Classification scheme

The freeze review requires reuse modes to be distinguished by their licensing and
verification consequences, not by a single "reuse / adapt" axis. Six modes:

| Mode | Meaning | Licensing engaged? | Verification burden |
|---|---|---|---|
| **1 · conceptual precedent** | an idea or posture is adopted; nothing is copied | No | none |
| **2 · structural template** | project layout, document topology, or a proof-organisation convention is followed | No | none |
| **3 · theorem / definition reuse** | a Rocq definition, lemma, or theorem is imported or transcribed and depended on | Yes (source text) | full — build, `coqchk`, `Print Assumptions`, semantic-fit finding |
| **4 · source-code copying** | OCaml / Python / Rocq source is copied or closely adapted | Yes (source text) | full — build, tests, contributor history, per-file licence |
| **5 · build / extraction configuration reuse** | extraction directives, `dune`/opam config, realisation-file selection | Yes (configuration text) | build + extraction reproduction + TCB itemisation |
| **6 · no reuse** | rejected; may still be cited as prior art | No | none |

Every manifest entry (§5) carries a mode plus the licensing fields in §7.

Method of the inspection pass: `grep` of every
`Definition`/`Theorem`/`Inductive`/`Record` in the relevant Rocq files, plus
reading of the foundation, theorem-ladder, trust-boundary, extraction, and
provenance documents and the OCaml verifier headers. The subsequent evidenced pass
(`PHASE_0_REUSE_VERIFICATION.md`) compiled every mode-3/4/5 candidate at Coq 8.18.0
and ran `coqchk` / `Print Assumptions` / contributor-history / licence checks. The
outcome of both passes is that **nothing is copied**; §6's checklist was the
verification plan and is retained as a record of what was done.

---

## 1. Sources inspected

| Short name | Path | Commit | Date | Licence |
|---|---|---|---|---|
| **PCE** — Proof-Carrying Exactness | `/data/proof-carrying-exactness` | `01b3114411c0d12520196bfaff36c14b41d2cad4` | 2026-07-22 | AGPL-3.0 |
| **PCSE** — Proof-Carrying Stream Exactness | `/data/proof-carrying-stream-exactness` | `164ca7042134fd91e149807bddcc5a0b28e8fe83` | 2026-08-10 | AGPL-3.0 |
| **PCOA** — Proof-Carrying Observability Audit | `/data/proof-carrying-observability-audit-working-tree/proof-carrying-observability-audit` | `6851293a5421a3131d6bb6331d1b6d5b342b0d70` | 2026-08-04 | AGPL-3.0 |
| **VBF** — VeriBound formal verification | `/data/veribound-formal-verification-main` | (not a git repo in this tree) | — | (unverified) |

PCOA embeds a byte-for-byte copy of `dhwcmoore/lift-descent-exactness` (AGPL-3.0,
Phases 1–6 complete) under `kernel/rocq/` (files prefixed `Q*`), per its
`UPSTREAM_PROVENANCE.md`. PCE's Rocq/OCaml foundation is a snapshot `cp -a` import
of `dhwcmoore/regional-obstruction-calculus` at `a9d68c34dbed7546d1cfb4e797d72e3af4c73278`,
with no shared git history, per its `docs/UPSTREAM_PROVENANCE.md`. The standalone
`lift-descent-exactness` archive was not separately unpacked; the PCOA copy is
treated as authoritative here.

---

## 2. Headline findings

**Post-verification decision (frozen): the v0 implementation copies nothing from
any prior project. Project licence: Apache-2.0.** The findings below record the
inspection; §5 records the ratified dispositions.

1. **PCOA's `AdmissibilityGate` is NOT reused (mode 6, permanent for v0).**
   Renaming its `GatedInadmissible` constructor is insufficient: that constructor
   denotes *protocol rejection*, a different semantic level from our `INADMISSIBLE`
   (witnessed non-factorisation). The three-level result types are defined
   independently in `PHASE_0_PROPOSED_ANSWERS.md` §C; PCOA is cited as prior formal
   work only. See §3.2.
2. **PCOA's factorisation kernel is re-proved, not reused.** It is specialised to
   linear maps over `Qc`; verification (§`PHASE_0_REUSE_VERIFICATION.md` M8)
   confirmed it is a *linear* factorisation theorem with no assumption-free generic
   lemma to lift. `(T1)` is proved afresh over `FibreConstant`. See §3.1.
3. **PCSE is a structural reference only (mode 2)** for deliverable topology, the
   failure-witness proof habit, and the trust-boundary shape. No prose or file is
   copied; the deliverables are authored fresh against the shared outline.
4. **PCE's extraction is authored afresh.** The discipline is adopted as method
   (mode 1); the extraction configuration is written independently against this
   project's definitions using Rocq's standard `ExtrOcamlZBigInt` facility
   (`Z` → OCaml big integers via `Big_int_Z`) — not copied from `ExtractR21.v`.
5. **No numeric core is reusable.** PCE is exact-rational (`Q`); VBF is Flocq /
   `float64`. Both contradict the accepted unbounded-integer (`Z`) v0 design.
6. **`ByteString.v` — no v0 reuse.** The semantic kernel operates on `list Z`, not
   bytes; digest binding is a system-binding obligation outside the kernel (§F.3).
   Revisit only if a later kernel theorem genuinely requires a byte substrate.

---

## 3. Component-by-component

### 3.1 Factorisation / descent / fibre theory

| Component | Source | Mode | Notes |
|---|---|---|---|
| `image_preimage_vanishing_iff_descent_vanishing`, `kernel_vanishing_iff_ambient_factorisation`, `intrinsic_image_factorisation_exists_unique` | PCOA `kernel/rocq/QDescentFactorisation.v` | **1 (conceptual) → possibly 3 for one lemma** | The factorisation-equivalence *architecture* (vanishing-on-kernel ⇔ factor-through-image ⇔ unique induced map) is the conceptual precedent for `(T1)`. The statements are `QLinearMap`-specific; our `M̃_{A,P}` is a nonlinear quantised integer map, `Φ_P` is Boolean, and "factors through" is set-level fibre constancy. **Action:** during Phase 1, check whether any single lemma (e.g. an `image_preimage` set-theoretic core) is stated generically enough for mode-3 transcription; if not, re-prove from scratch. Do not import the linear-algebra scaffolding to get it. |
| `separator_witness`, `not_image_iff_separator_witness`, `separator_witness_sound/complete` | PCOA `kernel/rocq/QSeparatorWitness.v` | **1 (conceptual)** | Their obstruction witness is a dual vector `y` with `yD = 0`, `y r ≠ 0`. Ours is a pair `(x,y)`. Same role, incompatible representation. Borrow the *sound + complete lemma pairing* as a proof-organisation habit, nothing more. |
| `pce_underdetermined_witness` + `operational_..._iff_..._exists` | PCOA `kernel/rocq/QPCEWitnessPredicates.v` | **1 (conceptual)** | "operational condition ⇔ witness exists" is the shape of our `(T1)`/`(T2)`. Conceptual only. |
| `operational_verdict` inductive, `classify_operational_verdict`, `operational_three_way_trichotomy` | PCOA `kernel/rocq/QVerdictClassification.v` | **2 (structural template)** | The `classify` / `_condition` / `_unique` / `_iff` / trichotomy lemma *layout* is a good template for §C.3. The inductive itself is rebuilt: our set is `{INADMISSIBLE, EXACT, UNDERDETERMINED, OBSTRUCTED}` with witness-dominates-obstruction precedence. No source copied. |
| R3 canonical value; `structurally_exact_transfer` uniqueness | PCOA ladder R3; PCSE `rocq/StructuralExactness.v` | **1 (conceptual, deferred)** | Relevant only to a future `EXACT`. Revisit when completeness certificates enter scope. |

### 3.2 Bundle processing and the two-level verdict — defined independently

| Component | Source | Mode | Notes |
|---|---|---|---|
| `AdmissibilityGate` record; `admissibility_gated_verdict` (`GatedInadmissible` \| `GatedAdmissible verdict`); `classify_after_admissibility` | PCOA `kernel/rocq/QAdmissibilityGate.v` | **6 (no reuse)** | `GatedInadmissible` = "evidence not admissible" = our `REJECTED_BUNDLE`. Our `INADMISSIBLE` is a positive campaign verdict. A rename hides rather than resolves the level confusion, and the borrowed soundness lemmas would then be phrased against the wrong meaning. **Define `BundleResult` / `WitnessResult` / `CampaignVerdict` from first principles** (see §3.2a). PCOA is cited in `VERDICT_SEMANTICS.md` as independent prior formal work on gated classification. |
| `admissible_assessment_input` conjunction + `*_precludes_admissibility` theorem family | PCSE `rocq/Admissibility.v` | **2 (structural template)** | The *pattern* — a conjunction of independent acceptance conditions, each with its own "failure ⇒ not admissible" theorem — is the template for `BundleResult` and the per-obligation `WitnessResult` findings. Conditions and proofs are ours. No source copied. |

#### 3.2a Independent result-type definitions (to appear in `VERDICT_SEMANTICS.md`)

```text
BundleResult    := REJECTED_BUNDLE | ACCEPTED_BUNDLE
WitnessResult   := VALID_WITNESS | NOT_A_WITNESS | WITNESS_CHECK_OBSTRUCTED
CampaignVerdict := INADMISSIBLE | EXACT | UNDERDETERMINED | OBSTRUCTED
```

`WitnessResult` is defined only on an `ACCEPTED_BUNDLE`. `CampaignVerdict` is
computed from a multiset of `WitnessResult`s plus a `campaign_record` by the frozen
precedence of `PHASE_0_PROPOSED_ANSWERS.md` §C.3. None of these is an instance of a
borrowed gate type.

### 3.3 Typed failure / finding witnesses

| Component | Source | Mode | Notes |
|---|---|---|---|
| `MissingChunkWitness`, `ConflictingChunkWitness`, `OutOfRangeChunkWitness`, `DeclaredLengthMismatchWitness`, `CompletionBoundaryAbsenceWitness`, `CommitmentRefutationWitness`, `CommitmentUnresolvedWitness` — records with `*_precludes_structural_exactness` theorems | PCSE `rocq/FailureWitness.v` | **2 (structural template)** | The "typed record witness for each failure mode, each with a theorem that it precludes the positive property" discipline is the template for our per-obligation findings (§A.2 obligations 1–9). `OutOfRangeChunkWitness` parallels "raw observation outside expected range ⇒ obstruction". Records and proofs are rewritten for our obligations; no source copied. |
| `TypedDiagnosticCalculus.v` (`SoundL`/`SoundR`, `no_silent_soundness_gain`, `RefinesByEvidence`) | PCE `rocq/TypedDiagnosticCalculus.v` | **6 (no reuse, v0)** | A diagnostic-combination calculus, heavier than v0's flat finding list needs. Reconsider only if findings acquire a combination semantics. |
| `ConflictDiagnostic` / `QuotientVerdictClosure` / `AbstractSeparation` | PCE `rocq/*.v` | **6 (no reuse, v0)** | Rational-conflict-resolution machinery; no v0 role. |

### 3.4 Bytes, digests, canonicalisation

| Component | Source | Mode | Notes |
|---|---|---|---|
| `ByteString := list byte`, `append_byte_string` (+ lemmas), `byte_string_eq_dec` | PCSE `rocq/ByteString.v` | **3 (theorem reuse) — conditional** | Reuse **only if** the semantic kernel ends up needing an in-kernel byte substrate with a proof-level role (e.g. a lemma that canonical bytes determine the policy). If digest binding stays a system-binding obligation checked outside the kernel (the current §F.3 position), the kernel needs no `ByteString` and this is **mode 6**. Decision deferred to the Phase 1 kernel-objects design. Do not pull hashing or transport lemmas into the kernel without a theorem that requires them. |
| `CommitmentDiagnosticContext`, `manifest_commitment_{confirmed,refuted,unresolved}` + `_represents` theorems | PCSE `rocq/CommitmentDiagnostics.v` | **1 (conceptual)** | The three-valued (confirmed / refuted / unresolved) digest-binding outcome is the conceptual precedent for obligation 5 and its `OBSTRUCTED` branch. |
| `r21_format.ml` — schema validation, `input_digest` canonicalisation, resource limits, fixtures | PCE `ocaml/r21_format.ml` | **4 (source-code copying) — candidate** | Its header explicitly designs it for sharing between independent checkers ("schema / canonicalisation / limits only, no solver logic") — exactly our untrusted-generator / trusted-verifier split. Strong candidate for adaptation, but this is source copying: contributor history and per-file licence must be checked (§6, §7), and the concrete schema is ours. |

### 3.5 Extraction and independent verification method

| Component | Source | Mode | Notes |
|---|---|---|---|
| Extraction discipline: extract only the computational function (no `Prop` wrappers); official `ExtrOcaml*` realisation files only; itemise every realisation line as extraction TCB; regenerate, never commit, the extracted `.ml` | PCE `rocq/ExtractR21.v` + `docs/design/R21_EXTRACTION_TCB.md` | **1 (conceptual / method)** | Adopt as the project's extraction *policy*. No text is copied to adopt a discipline. |
| `ExtrOcamlZBigInt` / `ExtrOcamlBasic` / `ExtrOcamlNatBigInt` realisation-file selection; the `Extraction Language OCaml` + `Extraction "..." <fn>` directive form | PCE `rocq/ExtractR21.v` | **5 (build / extraction configuration reuse)** | If we copy the directive block, that is configuration text under AGPL. Directly supports §E.1: `Z`→Zarith `Z.t`, no runtime conversion. Requires extraction-reproduction and TCB itemisation (§6). |
| Independent fail-closed OCaml verifier skeleton: direct recomputation, single `Reject` exception caught once, shares only the published spec, imports no generator | PCE `ocaml/r21_verifier.ml` | **1 (conceptual) or 4 (if skeleton copied)** | The architecture is exactly our verifier's. If only the architecture and the independence-boundary documentation style are followed → mode 1. If the module skeleton or helper functions are copied → mode 4, with the §6/§7 checks. |
| Cross-language agreement tests (Python vs OCaml checker must match accept/reject on a fixture battery) | PCE (referenced in `r21_verifier.ml` header) | **1 (conceptual)** | The differential-testing half of the §F.1.1 validation strategy. |

### 3.6 Domain membership / boundary classification

| Component | Source | Mode | Notes |
|---|---|---|---|
| `classify_flocq`, `boundary_distance_flocq`, `flocq_classification_soundness`, `flocq_complete_coverage`, `flocq_mutual_exclusion` | VBF `flocq_engine/FlocqClassification.v` | **1 (conceptual)** | The soundness / complete-coverage / mutual-exclusion triad is the right *specification shape* for `x ∈ D_P` decidability and registry-predicate totality. Built on Flocq / `float64`; statements' structure is the precedent, fresh proofs over `Z`. |
| VBF as precedent for a declared Boolean / threshold boundary predicate | VBF `flocq_engine` | **1 (conceptual)** | `SyntheticTargetV0` (§E.5) can be a VeriBound-style box/threshold classifier, re-specified over integer inputs with a Rocq decidability proof. |
| VBF numeric core (Flocq, `float64`, real `boundary_distance`) | VBF | **6 (no reuse)** | Reintroduces floating point into the trusted path; contradicts §E.1–E.3. |
| VBF fail-closed / domain-boundary tests | VBF | **1 (conceptual)** | Selectively adapt test ideas without the numeric core. |

### 3.7 Trust-boundary and document structure

| Component | Source | Mode | Notes |
|---|---|---|---|
| Six-layer trust model; "adapter code is untrusted, its *soundness theorem* is trusted (R13a)"; generator-may-search / verifier-may-only-check | PCSE `docs/TRUST_BOUNDARY.md` (follows PCE) | **2 (structural template)** | Precedent for §F. Our four-category taxonomy + §F.1.1 is a refinement. Copy the "adapter soundness theorem" device and the honesty that it "does not exist yet". |
| Deliverable set: `PROJECT_CHARTER.md`, `VERDICT_SEMANTICS.md`, `TRUST_BOUNDARY.md`, `THREAT_MODEL.md`, `NON_CLAIMS.md`, `CERTIFICATE_FORMAT.md`, `MATHEMATICAL_SCOPE.md`, `THEOREM_LADDER.md`, `CLOSURE_MODEL.md` | PCSE `docs/`, PCOA `docs/` + `kernel/docs/` | **2 (structural template)** | Almost one-to-one with the seven Phase 0 deliverables (specification §15). Follow the topology; write our own content. |
| `THEOREM_LADDER.md` convention ("statements only; proofs complete in `rocq/`; phase in which each was formalised") | PCOA `kernel/docs/THEOREM_LADDER.md` | **2 (structural template)** | Adopt for `(T1)`, `(T2)`, and the seven-part decomposition (specification §11.3). |

---

## 4. The `INADMISSIBLE` terminology collision — resolved by independent definition

| Meaning | This project | PCOA | PCSE |
|---|---|---|---|
| pre-classification rejection of malformed / unauthenticated input | `REJECTED_BUNDLE` | `INADMISSIBLE` / `GatedInadmissible` | `¬ admissible_assessment_input` |
| validated target-divergent fibre collision | `INADMISSIBLE` | (no equivalent) | (no equivalent) |
| no realising state / factorisation obstructed | `OBSTRUCTED` | `OBSTRUCTED` | — |

**Resolution:** do not instantiate or rename PCOA's gate. Define `BundleResult`,
`WitnessResult`, `CampaignVerdict` independently (§3.2a). `VERDICT_SEMANTICS.md`
records the PCOA and PCSE vocabularies side by side as a "prior art and why our
terms differ" note, so a reader crossing between the projects is not misled.

---

## 5. Reuse manifest — ratified

Each entry: component → final mode → final disposition (full fields in §7). This
manifest is **ratified**; the per-entry ownership/licensing review named in §6 was
completed in `PHASE_0_REUSE_VERIFICATION.md`.

Verified in `PHASE_0_REUSE_VERIFICATION.md`; **final dispositions ratified** — the
v0 implementation copies **no source, definition text, prose, or build
configuration** from any prior project, and is licensed **Apache-2.0**
(`PROJECT_CHARTER.md`).

| # | Component | Final mode | Final disposition |
|---|---|---|---|
| M1 | PCE extraction *discipline* (policy) | 1 | Adopt as method |
| M2 | PCE extraction directive block | ~~5~~ → 1 | **No copy.** Author the extraction config independently via Rocq's standard `ExtrOcamlZBigInt` |
| M3 | PCSE deliverable topology + trust-boundary shape | 2 | Structural reference; deliverables authored fresh |
| M4 | PCSE `Admissibility.v` conjunction pattern | 2 | Proof-organisation reference only |
| M5 | PCSE `FailureWitness.v` typed-witness discipline | 2 | Proof-organisation reference only |
| M6 | PCOA `QVerdictClassification.v` lemma layout | 2 | Proof-organisation reference only |
| M7 | PCOA factorisation architecture | 1 | Conceptual precedent for `(T1)` |
| M8 | PCOA `QDescentFactorisation.v` | ~~3~~ → 1 | **Reject.** Verified clean but a *linear* theorem — no generic lemma to lift; re-prove `(T1)` afresh |
| M9 | PCE `r21_format.ml` | ~~4~~ → 1 | **No source adaptation.** Write the wire format from this project's frozen schema |
| M10 | PCE `r21_verifier.ml` fail-closed skeleton | 1 | Conceptual precedent only |
| M11 | PCSE `ByteString.v` | ~~3~~ → 6 (v0) | **No v0 reuse.** Revisit only if a later kernel theorem requires bytes |
| M12 | VBF classification-theorem shape | 1 | Conceptual reference only |

**Permanent v0 rejections (mode 6):**
- PCOA `AdmissibilityGate` / `admissibility_gated_verdict` — no import, no
  constructor rename (§3.2).
- Any Flocq / `float64` / `Q` numeric core (PCE, VBF) — contradicts §E.1–E.3.
- PCE `TypedDiagnosticCalculus.v` and rational-conflict-resolution modules.

No manifest entry now copies licensed text, so nothing is blocked on licensing.
Any future proposal to copy or adapt prior material reopens the per-entry
ownership and licensing review before it enters the repository.

---

## 6. Verification checklist (performed — see `PHASE_0_REUSE_VERIFICATION.md`)

This was the verification plan for every mode-3/4/5 candidate. It was carried out;
the results are in `PHASE_0_REUSE_VERIFICATION.md` and the net outcome is in §5
(nothing copied). Retained here as a record of scope.

For each pinned source proposed for theorem, source, or configuration reuse:

- record the full commit hash of the exact tree;
- run its documented build and verification gate;
- run `coqchk` on the relevant `.vo` files;
- grep for `Admitted`, `admit`, `Axiom`, `Parameter`, and `Hypothesis`;
- run `Print Assumptions` on every theorem in the dependency cone of a reused item;
- record the Rocq and OCaml (and Zarith) versions the proofs and extraction assume;
- reproduce extraction and confirm `Z`/`positive`/`nat` map to Zarith as expected;
- for byte/digest utilities: test agreement on fixed vectors against the `sha`
  package PCE's verifier uses;
- list the exact files proposed for copying or close adaptation;
- inspect the git contributor history of those specific files;
- record the licence and any file-level copyright notice governing each file;
- **write a semantic-compatibility finding**: a successful upstream build does not
  show the component fits our semantics. Each mode-3/4 entry needs an explicit
  statement of what is imported, what our types require, and why the fit holds
  (or what adapter theorem closes the gap).

Compilation coverage must span M2, M8, M9, M10 (if mode 4), and M11 — not PCOA
alone.

---

## 7. Licensing — a deliberate project decision

The earlier claim that this project "must be AGPL-3.0" is too categorical. It is
true only if AGPL-covered **source or configuration text** is copied and
distributed under its existing licence (modes 3, 4, 5). Adopting a method (mode 1)
or a structure (mode 2) engages no licence.

If the project copies AGPL text, two paths exist:

1. **License this project AGPL-3.0 too.** Simple; but AGPL's network-use copyleft
   may deter commercial verification vendors from integrating the checker, which
   may matter for adoption.
2. **Relicense the copied material.** Available only if every copied file is owned
   solely by the user. That must be confirmed, not assumed, against:
   - the complete git contributor history of each copied file;
   - any third-party code copied or vendored into those files upstream;
   - file-level copyright notices;
   - the licences of build/runtime dependencies the copied code pulls in
     (Zarith LGPL-2.1-with-linking-exception, `yojson`, `sha`, Coq/Rocq stdlib);
   - the exact ownership of the `lift-descent-exactness` kernel (PCOA states no
     file was modified on copy and names `dhwcmoore` as upstream — confirm sole
     authorship there specifically before any mode-3 use of M8).

**Manifest licensing fields** (attach to every mode-3/4/5 entry):

```text
reuse_mode:                 conceptual | structural | theorem | source | configuration
source_repo_and_commit:
source_files:
source_licence:
target_licence:                 (this project's chosen licence)
copyright_owner_confirmed:       yes | no  (basis: git history + notices reviewed on <date>)
third_party_contributors:        none | <list>
vendored_or_upstream_third_party: none | <list>
relicensing_basis:               n/a (same licence) | sole-owner relicence | dual-licence
dependency_licences_reviewed:    yes | no
```

### 7.1 Decision (frozen)

**The project is licensed under the Apache License, Version 2.0.** The v0
implementation copies no source code, formal-definition text, documentation prose,
or project-specific build configuration from the author's earlier AGPL-3.0
projects (M2, M8, M9, M11 all reclassified to "author afresh"; M10 conceptual).

Under the frozen reuse dispositions, no source code, formal-definition text,
documentation prose, or project-specific configuration from the prior AGPL-3.0
projects is incorporated into version 0. The new project is therefore licensed
independently under Apache-2.0, subject to its declared dependency obligations
(`THIRD_PARTY_NOTICES.md`). The relicensing / sole-ownership analysis is not
needed for v0.

Rationale: Apache-2.0 permits commercial use, modification, distribution and
sublicensing; carries an explicit patent grant; is familiar to commercial
engineering organisations; and avoids the network-copyleft integration concern
AGPL could raise for EDA or industrial-tool vendors. This is a project
recommendation, not a legal opinion; it depends on the files actually being
authored afresh and on honouring the notices of distributed dependencies
(Coq/Rocq stdlib LGPL-2.1, zarith LGPL-2.0 + OCaml linking exception, yojson
BSD-3-Clause, sha ISC — all compatible with an Apache-2.0 distribution).

The charter language is in `PROJECT_CHARTER.md` §"Licence and Prior-Work Reuse";
`PRIOR_WORK.md` and `NOTICE` record the architectural influence of PCE, PCSE,
PCOA and VBF without implying code incorporation.

---

## 8. Status (this document)

**This reuse audit is complete and ratified.** Its outputs:

- the six-mode classification (§0);
- the inspection record (§3);
- the final manifest (§5) — **nothing copied**;
- the verification checklist (§6), carried out in `PHASE_0_REUSE_VERIFICATION.md`
  (all prior source builds clean at Coq 8.18.0; `coqchk` / `Print Assumptions`
  report zero project axioms for the inspected items; every inspected repo is
  single-author `dhwcmoore@gmail.com`);
- the licence decision (§7.1) — **Apache-2.0**, recorded in `PROJECT_CHARTER.md`
  §8 and `PHASE_0_DECISIONS.md` (D-REUSE, D-LIC).

No further work is required in this document. The Phase 0 deliverables are drafted
(`PHASE_0_DECISIONS.md` §4); the cross-document consistency audit is
`PHASE_0_CONSISTENCY_AUDIT.md`. The cross-language agreement battery is an
implementation-phase obligation (`AUDIT_POLICY_AND_EVIDENCE.md` §10), not a Phase 0
blocker.
