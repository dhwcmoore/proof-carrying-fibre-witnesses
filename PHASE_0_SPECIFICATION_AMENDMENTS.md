# Phase 0 — Specification Amendments

**Purpose:** `PHASE_0_CLAIM_SCOPE_TRUST_BOUNDARY.md` is the original framing
specification and a historical baseline. It contains structure that the frozen
Phase 0 deliverables have since replaced. This document itemises every point on
which the specification is superseded, and names the governing document. Where the
specification and a governing document disagree, **the governing document wins.**

Nothing in the specification is deleted; this table is the reading key.
**Count: 23 itemised rows — A1–A6 (6), B1–B3 (3), C1–C4 (4), D1–D6 (6), E1–E3 (3),
F1 (1) — plus the §G "not superseded" list.**

---

## A. Result / verdict structure

| # | Specification says (historical) | Superseded by | Governing document |
|---|---|---|---|
| A1 | §12 single verdict list: `REJECTED_BUNDLE`, `CANDIDATE_ACCEPTED`, `INADMISSIBLE`, `UNDERDETERMINED`, `OBSTRUCTED`, `EXACT` | Three result types at three levels: `BundleResult` / `WitnessResult` / `CampaignVerdict` | `VERDICT_SEMANTICS.md` §1 |
| A2 | §12 `INADMISSIBLE` is issued directly from "witness obligations and bindings" | `INADMISSIBLE` is a `CampaignVerdict` produced by the total `assess_validated` (a certificate in every non-`Underdetermined` constructor) under `(T2)` and the frozen precedence; the kernel proves only `(T1)` at the witness level | `VERDICT_SEMANTICS.md` §6–§7, `CLAIM_AND_DEFINITIONS.md` §6 |
| A3 | §12.1 `CANDIDATE_ACCEPTED` | renamed `ACCEPTED_BUNDLE`; a bundle-processing outcome only | `VERDICT_SEMANTICS.md` §1, §7 |
| A4 | §12.2 `UNDERDETERMINED` may be issued by an "incomplete search that finds no witness" at assessment time | `UNDERDETERMINED` is campaign-level only; the single-submission checker cannot return it; it is the last branch of the total `decide` (§6.7), reached only when `validate_campaign` returned `Valid, `rr.clo = None`, no replayed `` `ValidWitness ``, and `completeness` did not yield `EXACT`; dominated by a replayed witness and by any `clo` | `VERDICT_SEMANTICS.md` §6 |
| A5 | §12.2 `EXACT` "reserved for a complete proof that the target predicate factors through the operational observation map" | `EXACT` reserved for a checked `valid_completeness_certificate(rc.ctx, c)` meeting `(E1) valid_completeness_certificate(C, c) → FibreConstant(C)`; type and contract defined, no producer in v0, provably dead code (empty scheme registry) | `CLAIM_AND_DEFINITIONS.md` §6.4, `VERDICT_SEMANTICS.md` §6.7, §6.9 |
| A6 | §16 manual-example verdicts (`REJECTED_BUNDLE` for identical inputs; `REJECTED_BUNDLE`/`OBSTRUCTED` for model digest; etc.) | re-tabulated in the two-stage scheme (identical inputs → `NOT_A_WITNESS` (C1) in stage 1, before any context; model-digest mismatch → campaign-level `OBSTRUCTED` from `preflight_O1_O2` (O1) — no probe call; …) | `VERDICT_SEMANTICS.md` §11 |

## B. Candidate bundle

| # | Specification says (historical) | Superseded by | Governing document |
|---|---|---|---|
| B1 | §6.2 the bundle contains "claimed model observations", "claimed target values", "model-execution evidence", "target-evaluation evidence" as bundle contents | Minimal bundle: `schema_version`, `policy_hash`, `candidate_id`, `x`, `y`, optional `search_metadata`, optional diagnostic `hints`. The verifier computes `o_x`, `o_y`, `Q_P(·)`, `Φ_P(·)`. | `AUDIT_POLICY_AND_EVIDENCE.md` §3, `CLAIM_AND_DEFINITIONS.md` §5 |
| B2 | §6.3 "Checked findings" flat list mixing bundle, witness, and binding checks | Three tiers B / C / O with a frozen **two-stage** evaluation order (stage 1 = tier B + C1/C2/C3/C5, no context; `resolve_context` = O1–O3, once; stage 2 = O6 (input-correctness + success) / O4 (repeatability) / O5, per candidate, issued only after `ContextResolved`), each mapping to one result level | `AUDIT_POLICY_AND_EVIDENCE.md` §6, `VERDICT_SEMANTICS.md` §4–§5 |
| B3 | §13.1 T14/T15 threats reference candidate-supplied target claims | no candidate target claims exist in the minimal bundle; `Φ_P` is in-kernel | `THREAT_MODEL.md` T15–T16 |

## C. Trust boundary

| # | Specification says (historical) | Superseded by | Governing document |
|---|---|---|---|
| C1 | §10 four buckets: "trusted for logical correctness", "trusted for system binding", "untrusted", "security-critical but outside the logical kernel" | Four categories `F.1` (+`F.1.1`), `F.2`, `F.3` (+`F.3.1`, `F.3.2`), `F.4` | `TRUST_BOUNDARY.md` §2 |
| C2 | §10.3/§10.4 the JSON parser, schema validator, normalisation layer are "untrusted" / "security-critical outside the kernel" | the parser, schema validator, and canonicalisation layer are in the **F.3 system-binding TCB** — they validate wire lengths, construct the `Vec`/`Mat` values, and produce the `policy_hash` comparison input | `TRUST_BOUNDARY.md` §F.3 |
| C3 | §9.3 / §10.2 the target evaluator is a "trusted for system binding" component | the target evaluator is **in-kernel** for v0 (`Φ_P` a registry predicate on raw inputs); not in F.3 | `TRUST_BOUNDARY.md` §F.3, `CLAIM_AND_DEFINITIONS.md` §8 |
| C4 | §10.1 "extraction path" trusted, no mention of the compiled binary | `F.1.1` adds the OCaml compiler / linker / `zarith` / packaging, covered by reproducible-build + differential-testing assurance | `TRUST_BOUNDARY.md` §F.1.1 |

## D. Claim and definitions

| # | Specification says (historical) | Superseded by | Governing document |
|---|---|---|---|
| D1 | §3 `M_A : X → O` on a single input space `X` | three spaces `X_raw = Vec Z n_in`, `X_model = Vec Z n_pre`, `O = Vec Z n_obs`; `N_P : X_raw → X_model`; and an **audit context** `C = { policy, preproc, model }`. `M̃_C x = Q_P (model C (preproc C x))`; `Φ_P : Vec Z n_in → bool` | `CLAIM_AND_DEFINITIONS.md` §2–§3 |
| D2 | §11.1 kernel theorem phrased over the model | `(T1)` is `CheckedWitness(P, x, y, o_x, o_y) → ∀ g, g x = o_x → g y = o_y → ¬FibreConstantObs(P, g)` — pure, **policy only**; `(A1)` (context) adds the `ObservationBinding(C, ·, ·)` premises | `CLAIM_AND_DEFINITIONS.md` §6.1–§6.2 |
| D3 | §11.2 "system-level theorem" | `(A1)` (assurance corollary, context) plus `(T2)` (verdict-function soundness, verified orchestration, context) | `CLAIM_AND_DEFINITIONS.md` §6.2–§6.3 |
| D4 | §7.3 / §8 rounding "direction" named but not defined | `rounddiv` fully specified for all `Z` operands and half-ties, four modes | `CLAIM_AND_DEFINITIONS.md` §7.2 |
| D5 | §6.1 "quantisation or operational-resolution specification" (one item); "model format and runtime version" | split: `quantisation` + `quantisation_rounding_mode` (policy); `rescale_rounding_mode`, layer shapes, and the observable-checkpoint enumeration are content of the **inference specification** bound by `inference_spec_digest`; `representation_id` is a selector only. `policy_digest` is over an unsigned `policy_payload` (`canonicalise_v1`), not self-referential | `AUDIT_POLICY_AND_EVIDENCE.md` §2 |
| D6 | §3 states a decoder equation `∃ Φ̂ : Õ → 𝔹 . Φ_P|_{D_P} = Φ̂ ∘ M̃_{A,P}|_{D_P}` and §3 / early drafts treat it as **equivalent** to fibre constancy | v0 **defines** "factors through" to mean `FibreConstant(C)` by stipulation. The decoder equivalence is **withdrawn** — it is false without a finiteness / decidable-image / computable-section / choice assumption. v0 asserts neither the existence nor the non-existence of a total `Φ̂` | `CLAIM_AND_DEFINITIONS.md` §4.1, `PROJECT_CHARTER.md` §2, `NON_CLAIMS.md` #10 |

## E. Terminology

| # | Specification term (historical) | Current term | Governing document |
|---|---|---|---|
| E1 | `CANDIDATE_ACCEPTED` | `ACCEPTED_BUNDLE` | `VERDICT_SEMANTICS.md` |
| E2 | "trusted computing base" as a single bucket | four categories `F.1`–`F.4` | `TRUST_BOUNDARY.md` |
| E3 | "validated counterexample" / "validated witness" used loosely | `CheckedWitness` (kernel, policy), `ObservationBinding` (premise, context), `ValidWitness` (verifier composite, context) | `CLAIM_AND_DEFINITIONS.md` §5 |

## F. Non-claims (§14)

| # | Specification says (historical) | Superseded by | Governing document |
|---|---|---|---|
| F1 | §14.16 "The project does not claim that … a valid past certificate remains valid after the model, policy, preprocessing, target, or runtime changes" | Refined: a certificate **does** remain valid as a statement about the exact artifacts, policy, and versions it binds by digest; it does **not extend** to any changed system, which requires a fresh assessment. A change does not invalidate the historical statement | `NON_CLAIMS.md` #21 |

(The rest of §14 is not superseded — it is expanded in `NON_CLAIMS.md`.)

## G. What is NOT superseded

The specification remains authoritative for: the phase objective (§1); the working
title and its terminology constraint (§2); the constructive asymmetry (§4.3); the
v0 demonstration scope, included and excluded (§5); the audit-authority /
generator / relying-party actor roles (§9, subject to C3); the direction of §14
(refined only on item 16, per F1); the work-unit list (§15); the exit criteria
(§19); the definition of done (§20); and the Phase 1 objective (§21).
