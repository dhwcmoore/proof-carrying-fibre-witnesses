# Phase 0 — Proposed Answers  *(ARCHIVED)*

> ## ARCHIVED — decision-process record only
>
> This document records the Phase 0 decision *process* (three review rounds). It
> is **not** a governing document and **must not be cited as current**. Sections
> §A–§M below mix current and superseded material and are retained for provenance.
>
> **Governing set:** `PHASE_0_DECISIONS.md` (frozen-decision index),
> `PROJECT_CHARTER.md`, `CLAIM_AND_DEFINITIONS.md`, `TRUST_BOUNDARY.md`,
> `VERDICT_SEMANTICS.md`, `AUDIT_POLICY_AND_EVIDENCE.md`, `THREAT_MODEL.md`,
> `NON_CLAIMS.md`, `PHASE_0_SPECIFICATION_AMENDMENTS.md`.
> **Still-live content that was moved out of this document:** the §16 manual
> examples now live in `VERDICT_SEMANTICS.md` §9; the frozen-decision register
> now lives in `PHASE_0_DECISIONS.md`.
>
> `§0.3` below is a useful change-log of the closure-review rounds; read it as
> history.

**Companion to:** `PHASE_0_CLAIM_SCOPE_TRUST_BOUNDARY.md` (also a historical
baseline).
**Implementation status:** No implementation is authorised by this document.

---

## 0.3 Revision 2 — closure-review amendments

The independent closure review raised eight blockers. All are resolved in the
deliverables; the resolutions are:

| # | Blocker | Resolution | Governing document |
|---|---|---|---|
| 1 | The original specification is normatively contradictory (still has authoritative candidate observations, `CANDIDATE_ACCEPTED`, old trust/result structure) | Specification marked a historical baseline with an amendment notice; every superseded element itemised | `PHASE_0_SPECIFICATION_AMENDMENTS.md`; banner in `PHASE_0_CLAIM_SCOPE_TRUST_BOUNDARY.md` |
| 2 | Kernel `ValidWitness` (uses real `M_A`) vs. "T1 does not establish observations came from A" | Split: `CheckedWitness(P,x,y,o_x,o_y)` (kernel, over supplied observations), `ObservationBinding(A,P,x,o_x)` (system-binding premise), `ValidWitness` (verifier composite). `(T1)` is `CheckedWitness → ∀ g, g x = o_x → g y = o_y → ¬FibreConstant(P,g)`; `(A1)` adds the bindings | `CLAIM_AND_DEFINITIONS.md` §4–§5 |
| 3 | Raw / preprocessed / predicate input type confusion | `X_raw`, `X_model`, `N_P : X_raw → X_model`; `M̃_{A,P} = Q_P ∘ M_A ∘ N_P`; **frozen: `Φ_P` consumes raw inputs** | `CLAIM_AND_DEFINITIONS.md` §2 |
| 4 | Evidence-obligation → result mapping contradictory (parse failure → `NOT_A_WITNESS`; inequality at obl. 7 → obstruction; obl. 9 mixes levels) | Three tiers: B (bundle → `REJECTED_BUNDLE`), C (candidate-fault → `NOT_A_WITNESS`), O (obstruction → `WITNESS_CHECK_OBSTRUCTED`). Parsing/type/shape → tier B; distinctness/domain/quantised-equality/target-divergence → tier C; artifact binding/reproducible execution/internal failures → tier O | `AUDIT_POLICY_AND_EVIDENCE.md` §6, `VERDICT_SEMANTICS.md` §2–§3 |
| 5 | Relied-upon parser / schema validator / normalisation layer classified untrusted (F.4) | Moved to the F.3 system-binding TCB; future proof-checked raw-byte boundary noted as the way out | `TRUST_BOUNDARY.md` §F.3, §F.3.2 |
| 6 | Numerical / model-execution semantics not complete enough to freeze | `rounddiv` fully defined for negatives and half-ties (4 modes); `rescale_rounding_mode` and `quantisation_rounding_mode` declared separately; `inference_spec_digest` binds the interpreter semantics; shape/width/validity rules stated | `CLAIM_AND_DEFINITIONS.md` §6, `AUDIT_POLICY_AND_EVIDENCE.md` §2, §2.1, §5 |
| 7 | `T2` and `EXACT` cross the kernel/campaign boundary | `(T2)` is verified-orchestration, not a kernel theorem; `EXACT` contract is `(E1) valid_completeness_certificate(P, c) → FibreConstant(P)`, not "exhaustive coverage" | `CLAIM_AND_DEFINITIONS.md` §5.3–§5.4, `VERDICT_SEMANTICS.md` §5 |
| 8 | Reuse documents retain live pre-freeze dispositions | `PHASE_0_REUSE_AUDIT.md` marked RATIFIED with a reading guide; `PHASE_0_REUSE_VERIFICATION.md` leads with the frozen "author afresh" decision table; per-entry cells relabelled "Final decision" / "Evidence permitted" | `PHASE_0_REUSE_AUDIT.md`, `PHASE_0_REUSE_VERIFICATION.md` |

Plus corrections: `NON_CLAIMS.md` #21 (a certificate stays valid *about its bound
historical artifacts*; it does not *extend* to changed ones); `LICENSE` appendix
restored to the canonical bracketed form; `THIRD_PARTY_NOTICES.md` reworded as
"anticipated dependencies".

Sections §A–§M below are the decision record as of the freeze review; read them
with §0.3 and the governing deliverables.

---

## 0. Revision record

### 0.1 First-review corrections (all applied)

| # | Correction | Section |
|---|---|---|
| 1 | The "decidable equality ⟹ total decoder" equivalence is false; fibre constancy is primitive | §A.1, §B.1 |
| 2 | Separate bundle, witness, and campaign result types; `UNDERDETERMINED` is not a witness-checker output | §A.5, §C |
| 3 | Reduce the candidate to policy binding plus the input pair | §A.2, §D |
| 4 | Do not claim NumPy bit-reproducibility; prefer an exact integer model | §E.1 |
| 5 | `list Z → list Z` quantisation fits only an integer model | §E.2 |
| 6 | Four trust categories | §F |
| 7 | Digest + one signed tag; no detached signature | §G.1 |
| 8 | Separate semantic policy bounds from operational verifier limits | §G.3 |
| 9 | Freshness is unused infrastructure in v0 | §G.4 |
| 10 | Ship a replay package | §H.1 |
| 11 | Decide saturation explicitly | §E.3 |
| 12 | Confirmed decisions retained | §I |

### 0.2 Freeze-review rulings

| Ruling | Disposition | Section |
|---|---|---|
| §K.1 integer/fixed-point model | **Frozen** — arbitrary-precision integer semantics, scaling and rounding specified exactly | §B.3, §E.1, §E.2 |
| §K.2 saturation | **Frozen** — `Q_P` performs no clamping in v0 | §E.3 |
| §K.3 in-kernel target | **Frozen** — closed registry of Rocq-defined predicates, no policy-supplied code | §B.4, §E.5 |
| §K.4 reuse audit + licence decision | **Frozen** — audit (`PHASE_0_REUSE_AUDIT.md`) and per-entry verification (`PHASE_0_REUSE_VERIFICATION.md`) done; **no prior source is copied**; project licensed **Apache-2.0** | §B.2, `PROJECT_CHARTER.md` |
| §K.5 campaign completeness | **Frozen** — campaign record + separate completeness status; frozen verdict precedence | §C.3 |
| Eight internal inconsistencies | **Corrected** | §C.1, §D.2, §E.6, §F.1.1, §G.2, §H.2, §J |
| Result types defined independently of PCOA's gate | **Applied** | §C |
| Reuse-mode / licensing consequence separated | **Applied** | `PHASE_0_REUSE_AUDIT.md` §0, §7 |
| Every manifest entry reimplemented afresh; Apache-2.0 | **Frozen** | `PROJECT_CHARTER.md`, `PRIOR_WORK.md` |

The eight inconsistency corrections, itemised:

1. Bundle validation removed from the witness obligation set; it is now a stated
   precondition (§A.2, §C.1).
2. Identical well-typed inputs are `ACCEPTED_BUNDLE` → `NOT_A_WITNESS`, not
   `REJECTED_BUNDLE` (§J).
3. The minimal candidate cannot carry a model digest; a model-bytes/policy-digest
   mismatch is an environmental obstruction (§D.2, §J).
4. "Candidate selects a different quantiser/domain/target" is restated as
   "candidate carries a prohibited authoritative override field" (§D.2, §J).
5. `REJECTED_BUNDLE` yields a rejection report, not a certificate (§H.2, §H.5).
6. Generator hints do not enter the semantic certificate; only the candidate
   digest does (§D.1, §E.6, §H.2).
7. The compiled OCaml execution chain (compiler, linker, Zarith, packaging) is
   added to the trusted execution chain with a validation strategy (§F.1.1).
8. The demonstration fixes the quantiser before the search; a deliberately
   collision-seeded quantiser is labelled a constructed positive control (§G.2).

---

## A. The five framing questions (§1)

### A.1 What exactly is the claim being assessed?

For a fixed authorised policy `P` — committed model artifact `A`, one named
representation, an axis-aligned box domain `D_P`, a Boolean target predicate `Φ_P`
drawn from a closed registry, and a quantiser `Q_P` — the audit assesses whether

    Φ_P  factors through  M̃_{A,P} = Q_P ∘ M_A ∘ N_P   on   D_P,

equivalently whether `Φ_P` is constant on every fibre of `M̃_{A,P}` within `D_P`.
(Rev 2: the operational map includes the committed preprocessing `N_P`;
`Φ_P` is on raw inputs. `CLAIM_AND_DEFINITIONS.md` §2 governs.)

The v0 formal primitive is fibre constancy, not a decoder:

    FibreConstant(P) :=
      ∀ x y, x ∈ D_P → y ∈ D_P →
             M̃_{A,P}(x) = M̃_{A,P}(y) →
             Φ_P(x) = Φ_P(y).

The system's positive output is a **refutation** of this proposition. An
`INADMISSIBLE` certificate asserts a validated pair `x ≠ y` with
`M̃_{A,P}(x) = M̃_{A,P}(y)` and `Φ_P(x) ≠ Φ_P(y)`, hence `¬FibreConstant(P)` on
`D_P`, relative to every parameter listed in §4.2 of the specification.

The claim is not that a decoder `Φ̂ : Õ → 𝔹` exists or fails to exist. See §B.1.

### A.2 What constitutes a valid witness?

**Precondition:** the object is an `ACCEPTED_BUNDLE` — schema recognised, structure
well formed, no duplicate keys, no unknown critical field, within operational
limits, `policy_hash` equal to the authoritative policy digest. Bundle validity is
established at the bundle-processing level (§C.1) and is *not* a witness obligation.

Given an `ACCEPTED_BUNDLE`, `(x, y)` is a `VALID_WITNESS` iff **every** obligation
holds:

1. `x`, `y` parse to values of the declared exact input type and shape;
2. `x ≠ y`;
3. `x ∈ D_P`;
4. `y ∈ D_P`;
5. the artifact resolved from `P` matches the policy's model digest, and the
   committed preprocessing spec matches the policy's preprocessing digest;
6. independent re-execution of `M_A` on the preprocessed `x` yields raw observation
   `o_x` within the policy's expected observation range; likewise `o_y` for `y`;
7. `Q_P(o_x) = Q_P(o_y)`, computed by the kernel;
8. `Φ_P(x) ≠ Φ_P(y)`, computed by the kernel from the registry predicate bound by
   `P`;
9. no prohibited numeric value or malformed encoding encountered at any step.

A failed obligation among 1–4, 8 yields `NOT_A_WITNESS`. A failure among 5–7, 9
that reflects an environmental defect (artifact mismatch, non-reproducible
representation, out-of-range or non-deterministic re-execution) yields
`WITNESS_CHECK_OBSTRUCTED` (§C.2). Neither yields `INADMISSIBLE`.

### A.3 Which facts are computed, and which enter as assumptions?

**Computed by the verifier and its extracted kernel:**
domain membership; distinctness; quantisation; quantised equality; target
evaluation (kernel-side, from the registry predicate on the raw input); target
divergence; all structural and numeric checks — together `CheckedWitness`; the
kernel inference `(T1)`; the verdict-function step `(T2)`. (Rev 2: preprocessing
`N_P` and model re-execution are performed by the verifier to discharge the
`ObservationBinding` premises of `(A1)`, tier O — they are system-binding, not
kernel-proved. `CLAIM_AND_DEFINITIONS.md` §5 governs.)

**Entering as assumptions or authenticated evidence** (residual, non-kernel-proved
premises of the end-to-end claim):

- the model-execution component faithfully computes the committed artifact `A`
  under the committed export;
- the preprocessing implementation matches its committed spec;
- re-execution is deterministic;
- the artifact-hashing implementation is sound;
- the JSON parser, schema validator, and normalisation layer are non-differential
  and fail closed;
- extraction from Rocq to OCaml preserves semantics, subject to the declared
  extraction assumptions;
- the compiled OCaml checker implements the extracted term (§F.1.1);
- the mechanism that passes normalised values into the kernel is faithful;
- the formal definitions capture the intended notions, and the policy expresses
  the authority's intended question (§F.2).

Because the v0 target is a registry predicate evaluated in-kernel (§B.4), target
evaluation is a *computed* fact, not a system-binding assumption. Whether the
chosen registry predicate is *appropriate* remains a §F.2 assumption.

### A.4 Which components and actors are trusted, for what, with what limits?

See §F for the four-category taxonomy plus the compiled-execution chain. In brief:
the Rocq kernel, extraction, extracted checker, and — via a validation strategy —
the OCaml build chain are the logical/execution TCB; the formal definitions and
the policy carry specification-and-authority assumptions; the model loader,
preprocessing implementation, inference implementation, hashing, and value-passing
interface are the system-binding TCB; the generator, its hints, search metadata,
transport, and UI are untrusted; the JSON parser, schema validator, normalisation,
CLI, filesystem, and limit enforcement are security-critical fail-closed components
outside the proved core.

Actors: the audit authority declares the policy; the candidate generator is
untrusted and searches only; the verifier checks and issues certificates but holds
no authority to modify or disable the audited system; the relying party decides
what a certificate may do.

### A.5 Which results, and what does each warrant?

Three result types at three levels (§C):

- `REJECTED_BUNDLE` / `ACCEPTED_BUNDLE` — bundle-processing outcome, no epistemic
  content; `REJECTED_BUNDLE` yields a rejection report, not a certificate.
- `VALID_WITNESS` / `NOT_A_WITNESS` / `WITNESS_CHECK_OBSTRUCTED` — outcome of
  checking one candidate pair.
- `INADMISSIBLE` — a `VALID_WITNESS` was checked; warrants `¬FibreConstant(P)` on
  `D_P` relative to the stated parameters, subject to the discharged bindings.
- `EXACT` — a checked completeness certificate establishes exhaustive coverage and
  no valid witness exists; unreachable in v0; never from a negative heuristic
  search.
- `UNDERDETERMINED` — a recorded, non-complete campaign established no valid
  witness; warrants only that limited statement, nothing about `FibreConstant(P)`.
- `OBSTRUCTED` — a required audit obligation is unavailable, contradictory, or
  defeated; the obstruction certificate names the defect and the repair obligation.

---

## B. Open questions — formal (§18.1)

### B.1 Constructive decoder or propositional fibre constancy?

**Propositional fibre constancy**, as in §A.1. It is the whole of what v0 needs,
because v0 only ever refutes it.

The first draft claimed that decidable equality on `Õ` and `𝔹` makes fibre
constancy equivalent to the Σ-typed decoder
`{ Φ̂ : Õ → 𝔹 | Φ_P|_{D_P} = Φ̂ ∘ M̃_{A,P}|_{D_P} }`. **This is false as stated and
is withdrawn.** Building a total `Φ̂ : Õ → 𝔹` requires, for arbitrary `o : Õ`,
either exhibiting `x ∈ D_P` with `M̃_{A,P}(x) = o` or deciding none exists — needing
one of: a finite enumerable `D_P`; decidable membership in `Im(M̃_{A,P}|_{D_P})`; a
computable section; a constructive choice principle; or restriction of the decoder
to the image.

**Deferred plan.** If a decoder is later wanted, define it first on the image
subtype `Φ̂ : Im(M̃_{A,P}|_{D_P}) → 𝔹`, constructible from fibre constancy plus a
representative choice per inhabited fibre. A total decoder on `Õ` follows only under
an explicit finiteness or decidable-image assumption. None of this is on the v0
path.

**v0 theorem obligations** (rev 2 — `CLAIM_AND_DEFINITIONS.md` §5 governs):

    (T1)  CheckedWitness(P, x, y, o_x, o_y) →
          ∀ g, g x = o_x → g y = o_y → ¬ FibreConstant(P, g)      [kernel]
    (A1)  (T1) with the two ObservationBinding premises (M_A ∘ N_P)(x)=o_x,
          (M_A ∘ N_P)(y)=o_y  →  ¬ FibreConstant(P)               [assurance corollary]
    (T2)  the verdict function emits INADMISSIBLE iff a CheckedWitness is
          kernel-decided with both ObservationBinding obligations discharged,
          and never otherwise                                     [verified orchestration]
    (E1)  valid_completeness_certificate(P, c) → FibreConstant(P) [EXACT contract; no producer in v0]

### B.2 Which parts reuse existing developments?

**Status: frozen.** Conceptual similarity is not reuse. The four prior developments
— Proof-Carrying Exactness (PCE), VeriBound formal verification (VBF),
Proof-Carrying Stream Exactness (PCSE), Proof-Carrying Observability Audit (PCOA) —
were inspected definition by definition (`PHASE_0_REUSE_AUDIT.md`) and every
theorem/source/configuration candidate was build- and `coqchk`-verified
(`PHASE_0_REUSE_VERIFICATION.md`). **Final decision: the v0 implementation copies
no source code, formal-definition text, documentation prose, or project-specific
build configuration from any prior project.** Every item is reimplemented afresh:

- **PCOA's `AdmissibilityGate`** — permanent v0 rejection; no import, no constructor
  rename. Result types `BundleResult` / `WitnessResult` / `CampaignVerdict` are
  defined from first principles (§C).
- **PCOA's `QDescentFactorisation.v`** — verified clean but semantically a *linear*
  factorisation theorem; no generic lemma to lift. The generic
  witness-implies-non-factorisation theorem `(T1)` is proved afresh.
- **PCE's `ExtractR21.v`** — not copied. The extraction configuration is authored
  independently against this project's definitions using Rocq's standard
  `ExtrOcamlZBigInt` facility (`Z` → OCaml big integers via `Big_int_Z`), which
  Rocq itself treats as part of the unproved extraction boundary — consistent with
  §F.1 / §F.1.1.
- **PCE's `r21_format.ml`** — not adapted. The wire-format implementation is
  written from this project's frozen schema.
- **PCE's `r21_verifier.ml`** — conceptual precedent only (fail-closed architecture,
  written independence boundary).
- **PCSE** — structural/organisational reference only (deliverable topology,
  failure-witness proof habit, six-layer trust-boundary shape); no prose copied.
- **PCSE `ByteString.v`** — no v0 reuse; reconsider only if a later kernel theorem
  actually requires bytes.
- **VBF** — Flocq/`float64` core rejected; classification-theorem shape is a
  conceptual reference.

Prior projects are AGPL-3.0. Under the frozen reuse dispositions, no source code,
formal-definition text, documentation prose, or project-specific configuration
from those projects is incorporated into version 0; **this project is licensed
independently under Apache-2.0** (`PROJECT_CHARTER.md` §8), subject to its declared
dependency obligations. Any future proposal to copy or adapt prior material
reopens the per-entry ownership and licensing review before it enters the
repository.

New to this project regardless of the audit outcome:

- the quantisation-map representation and its totality / shape-preservation proofs;
- the `FibreConstant` proposition and `(T1)`;
- target divergence over the exact input type using a registry predicate.

### B.3 How is `Q_P` represented in Rocq?

A total, deterministic pure function on the kernel's exact internal representation,
parameterised only by explicit policy values.

With the integer model (§E.1), observations are integer vectors and

    Q_P : list Z → list Z

is component-wise `q_i = rounddiv(o_i, w)` where `w : Z`, `w > 0` is the bin width
and `rounddiv` uses one declared rounding rule, an inductive
`Round := Floor | Ceil | HalfEven | TowardZero`. Parameters may be uniform or
per-component. `Q_P` performs **no saturation** (§E.3). Proved properties:
totality, determinism, `length (Q_P v) = length v`. `Õ = list Z` is equipped with
decidable list equality.

Because `Z` is unbounded, `Q_P` is total without an output range. The policy's
expected observation range is checked against the *raw* `o_x`, `o_y` before `Q_P`
(obligation 6); an out-of-range value is a model/policy/execution mismatch and
yields `WITNESS_CHECK_OBSTRUCTED`, never a clamp.

`Q_P` never sees NaN or infinity: with the integer model these cannot arise.

### B.4 Does the kernel accept quantised observations, or quantise itself?

**The kernel quantises itself**, from the exact raw observation values produced by
independent re-execution. If it compared generator-supplied quantised values,
obligation 7 would be trivially forgeable and the re-execution binding would attach
to unquantised activations.

Flow: verifier re-executes `M_A` → exact integer observation vectors →
normalisation → kernel checks expected range → kernel applies `Q_P` → kernel
compares with decidable equality.

The generator supplies **no** observations or quantised values as evidence (§D).
Optional diagnostic hints are kept in a separate log, never entered into the
checker (§E.6).

**Target evaluation** is likewise kernel-side: `Φ_P` is one predicate from a closed
registry (§E.5), evaluated in Rocq on the normalised inputs. This keeps the target
evaluator out of the system-binding TCB for v0.

### B.5 Which conditions produce obstruction rather than protocol rejection?

Governing rule:

- **`REJECTED_BUNDLE`** — the fault is in the submission; a corrected resubmission
  is possible.
- **`WITNESS_CHECK_OBSTRUCTED`** (witness level) → **`OBSTRUCTED`** (campaign level)
  — the bundle is well formed and policy-bound, but the audit environment cannot
  deliver a required binding; the fault is external and needs a repair action.

| Situation | Result |
|---|---|
| Unsupported schema version; duplicate JSON keys; unknown critical field | `REJECTED_BUNDLE` |
| Wrong `policy_hash`; prohibited authoritative override field present | `REJECTED_BUNDLE` |
| `x` or `y` fails to parse to the declared type/shape | `REJECTED_BUNDLE` |
| Operational ceiling exceeded (size, nesting, recursion) | `REJECTED_BUNDLE` |
| Policy-named model artifact unavailable or unloadable | `OBSTRUCTED` |
| Resolved artifact bytes do not match the policy's model digest | `OBSTRUCTED` |
| Declared representation absent from the artifact; runtime cannot reproduce it | `OBSTRUCTED` |
| Re-execution non-deterministic across repeats | `OBSTRUCTED` |
| Raw observation outside the policy's expected range | `OBSTRUCTED` |
| Conflicting or defeated target provenance (post-v0 targets only) | `OBSTRUCTED` |

---

## C. Result types — three levels

Frozen in Phase 0 because it fixes the API and the theorem statements. These three
types are **defined from first principles**, not instantiated from any borrowed
gate abstraction (see `PHASE_0_REUSE_AUDIT.md` §3.2 — PCOA's `AdmissibilityGate` is
explicitly not reused, because its `GatedInadmissible` denotes protocol rejection,
not our witnessed non-factorisation).

```
BundleResult    := REJECTED_BUNDLE | ACCEPTED_BUNDLE
WitnessResult   := VALID_WITNESS | NOT_A_WITNESS | WITNESS_CHECK_OBSTRUCTED
CampaignVerdict := INADMISSIBLE | EXACT | UNDERDETERMINED | OBSTRUCTED
```

### C.1 Bundle processing — `BundleResult`

```
REJECTED_BUNDLE   → rejection report (parser diagnostic / protocol findings)
ACCEPTED_BUNDLE   → proceed to witness checking
```

Establishes: schema recognised, structure well formed, no duplicate keys, no
unknown critical field, within operational limits, `policy_hash` equals the
authoritative policy digest, no prohibited authoritative override field.

### C.2 Witness checking — `WitnessResult` (defined only on an `ACCEPTED_BUNDLE`)

```
VALID_WITNESS              → all §A.2 obligations 1–9 hold
NOT_A_WITNESS              → an obligation among 1–4, 8 fails (candidate defect)
WITNESS_CHECK_OBSTRUCTED   → an environmental defect blocks obligations 5–7, 9
```

The kernel theorem `(T1)` is stated at this level.

### C.3 Campaign assessment — `CampaignVerdict`

A campaign consumes zero or more witness checks plus a campaign record with a
completeness status.

```ocaml
type completeness_status =
  | Complete   of completeness_certificate
  | Incomplete of limitation list
  | Unknown

type campaign_record = {
  campaign_id          : string;
  policy_hash          : digest;
  generator_digest     : digest;
  configuration_digest : digest;
  method_description    : string;
  random_seeds          : Z list;
  resource_budget       : resource_budget;
  termination_reason    : termination_reason;
  candidate_digests     : digest list;
  witness_result_digests: digest list;
  completeness          : completeness_status;
  recorded_failures     : campaign_failure list;
}
```

**Frozen verdict precedence:**

1. If any checked candidate is a `VALID_WITNESS` → `INADMISSIBLE`.
2. Otherwise, if a blocking obligation prevented the required audit from being
   performed → `OBSTRUCTED`.
3. Otherwise, if a checked `completeness_certificate` establishes exhaustive
   coverage and no valid witness exists → `EXACT`.
4. Otherwise → `UNDERDETERMINED`.

A valid witness dominates an unrelated search obstruction: once one valid witness
exists, non-factorisation is established. `UNDERDETERMINED` warrants only:

> No valid witness was established by the recorded, non-complete campaign.

It warrants no claim that `FibreConstant(P)` holds.

Consequences:

- The single-candidate checker **cannot** return `UNDERDETERMINED`. That verdict is
  a statement about a campaign and needs the campaign record above.
- `CANDIDATE_ACCEPTED` from the specification is renamed `ACCEPTED_BUNDLE`.
- Campaign vocabulary is verifier/orchestration logic, not kernel logic.

---

## D. Candidate bundle — minimal form

### D.1 Shape

```ocaml
type candidate = {
  schema_version  : int;
  policy_hash     : digest;                     (* = authoritative policy digest *)
  candidate_id    : string;
  x               : input;                      (* exact declared integer input type *)
  y               : input;
  search_metadata : search_metadata option;     (* never evidence *)
  hints           : observation_hints option;   (* diagnostic only; separate log *)
}
```

The verifier computes, and the `INADMISSIBLE` certificate records:

    M_A(x), M_A(y),  Q_P(M_A(x)), Q_P(M_A(y)),  Φ_P(x), Φ_P(y).

Removed relative to specification §6.2 as authoritative fields: claimed
observations, claimed target values, model-execution evidence, target-evaluation
evidence. `hints` may carry generator-computed observations for triage; they are
excluded from the semantic checker, from `(T1)`, and from the certificate's proof
obligations. The certificate records the candidate digest and may note that
non-authoritative diagnostics existed, without reproducing them (§E.6, §H.2).

Rationale: do not transmit a value the trusted side derives. Every transmitted
authoritative value is a parsing and comparison obligation and an attack surface.

### D.2 What the minimal candidate cannot do

- It has no `model_digest` field, so it cannot select or substitute a model. A
  mismatch between the resolved artifact bytes and the policy's model digest is an
  **environmental obstruction** (`WITNESS_CHECK_OBSTRUCTED` → `OBSTRUCTED`), not a
  bundle rejection.
- It has no quantiser, tolerance, domain, or target fields. Any authoritative
  override field, or an unsupported critical extension, is detected at
  bundle-processing and yields `REJECTED_BUNDLE`.
- Diagnostic hints must never acquire override semantics.

The prohibited-field rule from §6.2 stands: no `domain_check_passed`,
`equivalence_verified`, `predicate_divergence_verified`, or similar.

---

## E. Open questions — execution (§18.2)

### E.1 Which model format for the first deterministic demonstration?

**An exact integer / fixed-point learned MLP.** Train a small MLP in Python (the
training may use floating point); export integer weights and biases with an
explicit scale. The audited artifact is the exported integer model — training is
not part of the trusted inference semantics.

v0 inference semantics:

    z^{(k+1)} = ReLU( rounddiv( W^{(k)} z^{(k)} + b^{(k)} , s_k ) )

where weights, biases, and activations are mathematical integers; `s_k > 0` is an
explicit per-layer scale; `rounddiv` has one declared rounding rule; all
intermediate arithmetic is over `Z`; no overflow, wrapping, host float, or implicit
cast is permitted; the observable layer is a numbered structural checkpoint. The
Python reference uses arbitrary-precision integers; the Rocq/OCaml checker uses `Z`
backed by Zarith.

Advantages: genuinely deterministic on any platform; no NaN or infinity; no float
parser in the trusted path; no IEEE-754 decomposition in the kernel; small trust
surface; straightforward Python/OCaml cross-check; still a learned neural
representation.

**Alternative (not chosen for v0): pinned floating-point execution.** A pinned
container, exact model bytes, exact runtime versions, fixed operation order, no
BLAS, no fast-math, recorded platform descriptor. More representative of deployed
models but an explicitly assumed execution environment; it must not be described as
platform-independent, because platform, compiler, processor, math library, and
floating-point control state can still affect results.

**ONNX / onnxruntime** is deferred to a later phase, when the objective shifts from
proving the architecture to demonstrating compatibility with deployed models.

The first draft's claim that a NumPy reference pass is "bit-reproducible across
platforms" is withdrawn.

### E.2 How are exact observation values serialised, and do the numeric types match?

Observations are exact integer vectors. The wire format is decimal integers with a
declared component count and shape, in declared row-major traversal order. The
kernel reads them as `list Z`. `Q_P : list Z → list Z` as in §B.3. No dyadic type,
no IEEE handling, no NaN/infinity path in normal operation.

(For the deferred floating-point alternative only: `list Z → list Z` would not
match; the kernel would need an explicit
`type dyadic = { significand : Z; exponent : Z }` parsed from IEEE bit patterns by
integer bit manipulation, with `Q_P` over `dyadic` and a separately verified
`dyadic`→fixed-scale rounding step. This is one more reason the integer model is
preferred.)

### E.3 Does saturation belong to the audited observation map?

**No. `Q_P` performs no clamping in v0.** With unbounded `Z` and the integer model,
`Q_P` is total without an output range, so binning alone suffices. Clamping would
manufacture fibre collisions (large activations all mapping to a boundary value)
that the deployed model does not exhibit, making an `INADMISSIBLE` verdict an
artefact of the audit.

Any permitted-range restriction in the policy is a **validity condition on the raw
observation** (obligation 6): a value outside it indicates a model/policy/execution
mismatch and yields `WITNESS_CHECK_OBSTRUCTED`, not a collision.

Saturation may later be added as a distinct policy constructor, only when the
audited interface genuinely saturates and the policy's `justification` explains
which feature it models.

### E.4 Runtime and determinism to commit

Integer model: pin the Python and library versions used for **export only**, and
record the export toolchain digest; inference itself is environment-independent.
(Floating-point alternative would additionally pin interpreter, libraries, BLAS
backend or reference matmul, `OMP_NUM_THREADS=1`, no fast-math, and the platform
descriptor.)

### E.5 The target predicate registry

`Φ_P` is not policy-supplied code. It is one constructor of a closed, versioned
registry of Rocq-defined decidable Boolean functions:

```ocaml
type predicate_id =
  | SyntheticTargetV0            (* v0 demonstration predicate *)
  (* future: | PredicateA | PredicateB ... each a proved decision function *)
```

The policy selects an authorised constructor and binds its version or digest. The
kernel computes `Φ_P(x)` and `Φ_P(y)` directly. Target divergence is then a genuine
kernel result. Whether the chosen predicate is *appropriate* to the audit question
is a §F.2 specification-and-authority assumption.

Later target authorities — authenticated labels, calibrated measurements,
institutional records — reintroduce a provenance and authority model and a
system-binding obligation; they are out of scope for v0.

### E.6 Generator hints

Hints are retained in a separate diagnostic log, addressed by the candidate digest.
They are excluded from the semantic checker, from `(T1)`, and from the certificate's
proof obligations. Hint/re-execution disagreement is logged, not fatal, and does not
appear as a certificate finding. The certificate may state that non-authoritative
diagnostics existed without reproducing them.

### E.7 Observable layer identification and preprocessing

- **Layer id:** a structural identifier, never a human label — a numbered
  checkpoint in a spec that enumerates every intermediate tensor with index, shape,
  and dtype. The policy commits `layer_id + shape + dtype`; the verifier asserts an
  exact match.
- **Preprocessing:** in-process for v0, a committed pure function with its own
  digest, invoked by the verifier (never the generator), a small deterministic
  integer transform. It is in the system-binding TCB; its digest is in the
  certificate. A separately sandboxed component is deferred.

---

## F. Trust taxonomy — four categories plus the execution chain

### F.1 Logical trusted computing base

- Rocq kernel and accepted foundational libraries.
- The extraction mechanism and its declared extraction assumptions.
- The extracted checking kernel (as an OCaml term).
- Required OCaml runtime behaviour relied on by the extracted code.

Failure here breaks the mechanical soundness of `(T1)`.

#### F.1.1 Compiled execution chain (not covered by extraction)

Rocq extraction produces an OCaml term; it does not establish that the final
machine-code binary implements that term. If the relying party runs a compiled
binary, the result additionally depends on:

- the OCaml compiler and linker;
- the Zarith implementation and its C bindings;
- the platform C runtime;
- the build configuration and flags;
- executable packaging.

**Validation strategy for v0:** reproducible builds (pinned compiler and library
versions, recorded build flags, byte-identical rebuild) plus differential testing
of the compiled checker against the Python reference on a fixture battery. These
components are named in the certificate's assumption section. This is an assurance
argument, not a proof.

### F.2 Specification and authority assumptions

- The formal definitions (`D_P`, `M̃_{A,P}`, `Q_P`, `Φ_P`, `FibreConstant`,
  `ValidWitness`) capture the intended notions.
- The audit policy expresses the question the authority intended.
- The selected registry predicate is appropriate to that question.
- The selected quantisation has operational meaning.

A policy may be authoritative — correctly the authority's stated question — without
being scientifically or ethically correct. Formal verification cannot close this
gap; the certificate must make it visible.

### F.3 System-binding trusted computing base

- Model loader.
- Preprocessing implementation.
- Inference implementation.
- Artifact hashing.
- The value-passing interface between the host side and the kernel.

Tested and reviewed, not proved. Each contributes a named residual-risk line to the
certificate. (The target evaluator is **not** here for v0 — it is in-kernel, §E.5.)

### F.4 Untrusted environment

- The witness generator.
- Candidate claims and `hints`.
- Search metadata.
- Transport channel.
- Any user interface or dashboard.
- External storage.

Plus the security-critical host components that must **fail closed** and are not
part of the proved core: JSON parser, schema validator, normalisation layer, CLI,
filesystem layer, operational-limit enforcement.

---

## G. Open questions — policy (§18.3)

### G.1 Who commits the policy in the demonstration?

A single "audit authority" role held by the project team. Mechanism:

1. canonicalise the policy to a fixed byte encoding;
2. compute its SHA-256 digest;
3. commit the canonical bytes and the digest to the repository;
4. create **one** signed git tag if authorship authentication is wanted.

The digest establishes identity and binding; the signed tag establishes authority
endorsement. The first draft's detached-signature-plus-signed-tag combination is
withdrawn. Production key management is a later institutional problem.

### G.2 How is the quantisation resolution justified, and in what order?

The demonstration proceeds in this fixed order, so the policy cannot appear to have
been chosen after finding a desired failure:

1. define a synthetic operational interface with a naturally motivated resolution;
2. commit the policy and quantiser;
3. commit the model artifact;
4. run the untrusted search;
5. check the resulting candidate.

The resolution rationale is recorded in the policy's `justification` field. It is an
explicit non-claim (specification §14.5) that the quantiser is uniquely correct.

If a quantiser is deliberately chosen to create a known regression fixture, that
test is labelled a **constructed positive-control case**, not an empirical
discovery.

### G.3 Which resource limits are policy-bound, and which are verifier limits?

**Semantic policy bounds** — part of the mathematical object, identical for every
candidate under `P`, digest-bound: input dimension and model-input schema;
observation shape; quantisation parameters; domain bounds; the expected observation
range.

**Operational verifier limits** — host protections that do not change the meaning of
the factorisation claim: maximum JSON nesting depth; maximum wire-bundle size;
parser recursion limit; wall-clock timeout; memory ceiling; temporary storage;
process parallelism.

A bundle exceeding an operational ceiling is rejected, but the certificate must not
imply that changing a parser memory limit changes the factorisation claim. The
certificate records both categories, clearly labelled.

### G.4 Are freshness requirements necessary for the offline demonstration?

No. The model digest and policy digest already defeat substitution and
replay-across-policies. A witness does not become mathematically false with age.
The policy carries `"expiry": null` explicitly. A `created_at` field is metadata
only, not trusted evidence unless bound to a trusted clock or authority — which v0
does not provide.

---

## H. Open questions — certificate (§18.4)

### H.1 What is required for independent replay?

A digest plus a URL identifies bytes but does not guarantee availability. The
Phase-1+ release ships a **replay package**: the canonical policy; the model
weights; the reference inference specification; the preprocessing specification;
the in-kernel target definition (registry version); the candidate inputs; the
certificate; kernel and verifier version information; build and execution
instructions. Digests confirm identity; the package supplies availability. Where a
model cannot be redistributed, the certificate states that replay requires
separately obtaining an artifact matching the recorded digest.

### H.2 Certificate content, by result

- **`INADMISSIBLE`:** the complete witness — inputs `x`, `y`; the verifier-computed
  exact observations; the verifier-computed quantised observations; the target
  values; all findings — plus the candidate digest. Independently replayable from
  the release package without the original bundle.
- **`EXACT`:** the completeness certificate and the checked coverage argument, plus
  the campaign record digest.
- **`OBSTRUCTED`:** an obstruction certificate — the named defect, the failed
  obligation, and the repair obligation.
- **`UNDERDETERMINED`:** a campaign report referencing the `campaign_record` and its
  `completeness_status`. Not an epistemic certificate.
- **`REJECTED_BUNDLE`:** a rejection report — parser diagnostic or protocol
  findings. Not a certificate. "Certificate" is reserved for assessment results.

### H.3 Binding to verifier and kernel versions

The certificate carries: verifier version and binary digest; extracted-kernel
version and digest; Rocq development commit hash; the extraction-assumptions list;
the compiled-execution-chain descriptor (§F.1.1). All covered by the certificate's
own digest. A verdict is meaningful only with respect to the recorded kernel digest.

### H.4 Which assumptions are rendered for a human reader?

An explicit section headed "This certificate depends on the following unproved
assumptions", listing the §F.2 specification assumptions and the §F.3 system-binding
assumptions actually in force, plus the §F.1.1 execution-chain assumption: faithful
model re-execution; preprocessing matches spec; re-execution determinism; hashing
soundness; parser / schema / normalisation fail closed and non-differential;
Rocq→OCaml extraction fidelity; compiled binary implements the extracted term;
value-passing fidelity.

### H.5 Terminology

| Result | Artefact issued |
|---|---|
| `INADMISSIBLE`, `EXACT`, `OBSTRUCTED` | certificate (assessment / obstruction) |
| `UNDERDETERMINED` | campaign report |
| `REJECTED_BUNDLE` | rejection report |

---

## I. Confirmed decisions retained from the first draft

- propositional fibre constancy as the v0 primitive;
- the kernel performs quantisation itself;
- quantisation is fixed by policy before candidate evaluation;
- exact operational equality after quantisation replaces any informal notion of
  closeness;
- candidate faults are separated from environmental obstruction;
- preprocessing runs independently of the generator;
- the model and representation are identified structurally, not by human label;
- `EXACT` is unreachable through incomplete heuristic search;
- the complete assumption set appears in the human-readable certificate;
- an `INADMISSIBLE` certificate carries the complete successful witness;
- the project begins with a deliberately narrow synthetic demonstration.

---

## J. Manual examples — expected outcomes under the three-tier scheme

Updates specification §16 to the tier ids of `AUDIT_POLICY_AND_EVIDENCE.md` §6
(B = bundle, C = candidate-fault, O = obstruction) and the result types of
`VERDICT_SEMANTICS.md`.

| Case | `BundleResult` | `WitnessResult` | `CampaignVerdict` |
|---|---|---|---|
| Valid target-divergent operational collision | `ACCEPTED_BUNDLE` | `VALID_WITNESS` | `INADMISSIBLE` |
| One input outside `D_P` | `ACCEPTED_BUNDLE` | `NOT_A_WITNESS` (C2/C3) | none from this candidate |
| Quantised observations differ (`Q_P(o_x) ≠ Q_P(o_y)`) | `ACCEPTED_BUNDLE` | `NOT_A_WITNESS` (C4) | — |
| Target values agree | `ACCEPTED_BUNDLE` | `NOT_A_WITNESS` (C5) | — |
| Identical well-typed inputs (`x = y`) | `ACCEPTED_BUNDLE` | `NOT_A_WITNESS` (C1) | none from this candidate |
| Candidate carries a prohibited authoritative override field, or an unsupported critical extension | `REJECTED_BUNDLE` (B2) | — | — |
| `x` or `y` fails to parse to the declared type/shape | `REJECTED_BUNDLE` (B4) | — | — |
| Malformed numeric encoding in the candidate | `REJECTED_BUNDLE` (B5) | — | — |
| Unsupported schema version; duplicate keys | `REJECTED_BUNDLE` (B1) | — | — |
| Wrong `policy_hash` | `REJECTED_BUNDLE` (B3) | — | — |
| Operational limit exceeded | `REJECTED_BUNDLE` (B6) | — | — |
| Resolved model artifact bytes do not match `model_artifact_digest` | `ACCEPTED_BUNDLE` | `WITNESS_CHECK_OBSTRUCTED` (O1) | `OBSTRUCTED` |
| Policy-named model artifact unavailable | `ACCEPTED_BUNDLE` | `WITNESS_CHECK_OBSTRUCTED` (O1) | `OBSTRUCTED` |
| Inference spec digest mismatch | `ACCEPTED_BUNDLE` | `WITNESS_CHECK_OBSTRUCTED` (O2) | `OBSTRUCTED` |
| Runtime cannot reproduce the declared representation | `ACCEPTED_BUNDLE` | `WITNESS_CHECK_OBSTRUCTED` (O3) | `OBSTRUCTED` |
| Re-execution non-deterministic | `ACCEPTED_BUNDLE` | `WITNESS_CHECK_OBSTRUCTED` (O4) | `OBSTRUCTED` |
| Raw observation outside `expected_observation_range` | `ACCEPTED_BUNDLE` | `WITNESS_CHECK_OBSTRUCTED` (O5) | `OBSTRUCTED` |
| Candidate `hints` disagree with re-execution | `ACCEPTED_BUNDLE` | assessed on re-execution; disagreement logged only | per re-execution |
| Campaign: heuristic search returns no candidate | n/a | n/a | `UNDERDETERMINED` |
| Campaign: checked `valid_completeness_certificate(P, c)`, no valid witness | n/a | n/a | `EXACT` (post-v0) |

Malformed policy (e.g. `w_i ≤ 0`, `s_k ≤ 0`, shape disagreement,
`representation_id` unknown) is an authority-side error: the policy does not load
and no assessment runs (`AUDIT_POLICY_AND_EVIDENCE.md` §2.1). With the integer
model, NaN/infinity cases cannot arise; the O6 guard is a regression guard for the
deferred floating-point alternative.

---

## K. Decision status

| # | Decision | Status |
|---|---|---|
| 1 | Exact integer / fixed-point model; arbitrary-precision `Z`; scaling and rounding specified | **Frozen** |
| 2 | `Q_P` performs no saturation; expected range is a raw-observation validity check | **Frozen** |
| 3 | In-kernel target from a closed registry; no policy-supplied predicate code | **Frozen** |
| 4a | Reuse audit — first evidenced pass | **Done** (`PHASE_0_REUSE_AUDIT.md`) |
| 4b | Reuse audit — per-entry verification (`coqchk`, `Print Assumptions`, contributor history, semantic-fit finding) | **Done** (`PHASE_0_REUSE_VERIFICATION.md`) |
| 4c | Project licence + prior-work reuse | **Frozen** — **Apache-2.0**; **no prior source, definition text, prose, or build config copied**; every manifest entry reimplemented afresh (`PROJECT_CHARTER.md`) |
| 5 | Campaign record + `completeness_status`; frozen verdict precedence; limited `UNDERDETERMINED` warrant | **Frozen** |

**Final manifest dispositions** (`PHASE_0_REUSE_AUDIT.md` §5, `PROJECT_CHARTER.md`):

| Entry | Final disposition |
|---|---|
| M2 `ExtractR21.v` | No copy — author the extraction config independently via Rocq's standard `ExtrOcamlZBigInt` |
| M8 `QDescentFactorisation.v` | Reject — re-prove the generic theorem `(T1)` |
| M9 `r21_format.ml` | No source adaptation — write the wire format from this project's frozen schema |
| M10 `r21_verifier.ml` | Conceptual precedent only |
| M11 `ByteString.v` | No v0 reuse; revisit only if a later kernel theorem requires bytes |
| PCOA `AdmissibilityGate` | Permanent v0 rejection — no import, no constructor rename |

---

## L. Path to Phase 0 closure

All decision groups §K.1–§K.5 are frozen. Status of the remaining production work:

1. **Deliverables drafted (rev 2):** `PROJECT_CHARTER.md`,
   `CLAIM_AND_DEFINITIONS.md`, `TRUST_BOUNDARY.md`, `VERDICT_SEMANTICS.md`,
   `AUDIT_POLICY_AND_EVIDENCE.md`, `THREAT_MODEL.md`, `NON_CLAIMS.md` — authored
   fresh, no prior prose copied. Plus `PHASE_0_SPECIFICATION_AMENDMENTS.md`
   (reading key against the historical specification), `PRIOR_WORK.md`, `NOTICE`,
   `THIRD_PARTY_NOTICES.md`, `LICENSE`.
2. **Closure review round 1 (independent):** eight blockers + two corrections
   raised. All resolved in rev 2 — see §0.3 and
   `PHASE_0_CONSISTENCY_AUDIT.md` (Run 2) §0.
3. **Consistency audit Run 2:** PASS. Two locatability notes (N1, N2), neither a
   closure blocker.
4. **Pending:** the independent closure reviewer's concurrence with rev 2, then
   `PHASE_0_CLOSURE_REPORT.md` authorising the Phase 1 objective — define the Rocq
   semantic objects and prove `(T1)` for policy-bound, quantised fibre witnesses
   over a fixed-dimensional exact integer domain (`X_raw`), with `(T2)` as verified
   orchestration.

Phase 1 does not begin until the closure gate passes.

---

## M. Cross-reference to the Phase 0 specification

| Specification item | Answered in |
|---|---|
| §1 Q1 claim | §A.1, §B.1 |
| §1 Q2 valid witness | §A.2, §C.2 |
| §1 Q3 computed vs assumed | §A.3, §F |
| §1 Q4 trusted components | §A.4, §F |
| §1 Q5 verdicts | §A.5, §C |
| §18.1 formal questions | §B |
| §18.2 execution questions | §E |
| §18.3 policy questions | §G |
| §18.4 certificate questions | §H |
| §16 manual examples | §J |
| §17 recommended decisions | §I, §K |
| §19 exit criteria | §L (checklist discharge tracked in the closure report) |
