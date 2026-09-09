# Project Charter

**Working title:** Proof-Carrying Fibre Witnesses for Learned Observation Regimes
**Deliverable:** Phase 0, Unit 0A
**Status:** Draft for Unit 0G ratification. **Revision 14** — §4.3 `(T2)` over `assess_validated` (`loaded_context` threaded through capture/replay; `transcript_source` keeps entry-point provenance), verbatim from `CLAIM_AND_DEFINITIONS.md` §6.3. §4.2:
`ObservationBinding` conditional on O6 + the assumed `faithful_transcript` (O4 =
repeatability only). §8 frozen; the rest authored fresh.
**Implementation status:** No implementation is authorised by this document.

---

## 1. Problem statement

A learned model, observed at a declared interface, may fail to preserve a
distinction that a downstream target predicate requires. When that happens the
model's operational observations cannot in principle support the target decision,
regardless of how the decision is computed downstream.

This project builds a proof-carrying audit system that, given an authorised policy
and a committed model artifact, independently validates whether a submitted
candidate demonstrates such a failure on a declared input domain.

## 2. Central problem, in factorisation and fibre language

Three input types are kept distinct (`CLAIM_AND_DEFINITIONS.md` §2–§3), all
length-indexed integer vectors: `X_raw = Vec Z n_in` (parsed raw inputs),
`X_model = Vec Z n_pre` (the model's input after preprocessing), and
`Õ = Vec Z n_obs` (quantised observations). A policy `P` fixes: the box domain
`D_P` on `X_raw`; the quantiser `Q_P : Õ-carrier → Õ-carrier`; and the Boolean
target `Φ_P : X_raw → bool`, evaluated on **raw** inputs. An **audit context** `C`
adds the resolved semantics: `preproc C : X_raw → X_model` (the committed `N_P`)
and `model C : X_model → O` (the committed `M_A` at the declared checkpoint). The
operational observation map is `M̃_C x = Q_P (model C (preproc C x))`.

**In version 0, "`Φ_P` factors through `M̃_C` on `D_P`" is *defined* to mean**

    FibreConstant(C) :=
      ∀ x y, D_P x → D_P y → M̃_C x = M̃_C y → Φ_P x = Φ_P y.

No stronger characterisation is claimed — in particular **not** an equivalence
with the existence of a total decoder `Φ̂ : Õ → bool` (that is false without extra
assumptions; `CLAIM_AND_DEFINITIONS.md` §4.1, `PHASE_0_SPECIFICATION_AMENDMENTS.md`
D6).

A **validated fibre witness** is a pair `x, y` with `D_P x`, `D_P y`, `x ≠ y`,
`M̃_C x = M̃_C y`, `Φ_P x ≠ Φ_P y`. Such a pair refutes `FibreConstant(C)`.

The term **fibre witness** is used only because v0 fixes a quantisation map and
compares observations by exact equality after quantisation, so `M̃_C` induces
genuine fibres. A distance-threshold relation would instead give an
**observational-confusability witness**; v0 does not use one.

## 3. Intended contribution

An untrusted search process may propose a witness; an independent, formally
grounded assurance process determines whether the submitted evidence establishes
target-relevant observational collapse under a declared audit policy. The
contribution is that assurance architecture and its kernel-level soundness
theorem — not a search heuristic.

### 3.1 Constructive asymmetry (governing rule)

    validated fibre witness  ⟹  relative inadmissibility on D_P

but

    no witness found by heuristic search  ⇏  exactness.

A single validated witness establishes relative inadmissibility. Failure to find a
witness never establishes `FibreConstant(C)`, unless a separate, checked
completeness argument is supplied — which v0 does not attempt.

## 4. Three-part assurance claim

Full statements: `CLAIM_AND_DEFINITIONS.md` §6.

### 4.1 Kernel-level theorem `(T1)` — pure, policy only

    (T1)  CheckedWitness(P, x, y, o_x, o_y) →
          ∀ g : Vec Z n_in → Vec Z n_obs,
            g x = o_x → g y = o_y → ¬ FibreConstantObs(P, g)

where `CheckedWitness` is `D_P x`, `D_P y`, `x ≠ y`, `Q_P o_x = Q_P o_y`,
`Φ_P x ≠ Φ_P y`, over observations `o_x`, `o_y` **supplied to** the kernel, and
`FibreConstantObs(P, g) := ∀ u v, D_P u → D_P v → Q_P (g u) = Q_P (g v) → Φ_P u = Φ_P v`.
`(T1)` mentions no context, model, or execution.

### 4.2 System-level corollary `(A1)` — adds the binding premises (context `C`)

    (A1)  CheckedWitness(policy C, x, y, o_x, o_y)
        → model C (preproc C x) = o_x
        → model C (preproc C y) = o_y
        → ¬ FibreConstant(C)

by instantiating `(T1)`'s `g` with `fun x => model C (preproc C x)`. The two
`ObservationBinding` premises follow **conditionally** from O6 (an `` `Ok ``
transcript event whose `input = preproc C x` / `preproc C y`) plus the assumed
F.3 premise `faithful_transcript tr C` — O4 gives repeatability only, not
faithfulness (`CLAIM_AND_DEFINITIONS.md` §3.2.2, `TRUST_BOUNDARY.md` §F.3.1).
`(A1)` is what an `INADMISSIBLE` verdict warrants, conditional on those premises.

### 4.3 Verdict-function soundness `(T2)` — verified orchestration

Scoped to `validate_campaign` (`VERDICT_SEMANTICS.md` §5–§6), reproduced verbatim
from `CLAIM_AND_DEFINITIONS.md` §6.3; `V := validate_campaign ti` (once per
pipeline), `R := replay ac cb ti.vcfg ti.AR.policy_document ti.AR.policy L0 tr` (`cb` the captured `context_bundle`) for `V = ` `Valid {campaign = ac ; fuel = L0}``:

    (T2)  verdict_of (assess_validated ti V src) = INADMISSIBLE
          ⟺  (∃ ac L0, V = `Valid {campaign = ac ; fuel = L0})
              ∧ (∃ {_, `Done s} ∈ R.stage2, ∃ wd, s.verdict = `ValidWitness wd)

    (T2-sound)     INADMISSIBLE ⟹ that right-hand side
    (T2-complete)  that right-hand side ⟹ INADMISSIBLE

`assess_validated` re-uses the given `V` (no re-validation) and evaluates `R`
once. `(T2-sound)` plus `(A1)` — O6 for the witness's `x`, `y` plus the assumed
`faithful_transcript tr rc.ctx` (where `rc.ctx = r.context.ctx` for
`R.context = ContextResolved r`) — gives `¬ FibreConstant(rc.ctx)`. A `` `Done ``
stage-2 `` `ValidWitness `` slot only exists for a candidate whose gate opened
after `ContextResolved` (`(REP1)`, which holds for every certificate; `(CAP1)` only when `transcript_evidence = LiveCapture`); a witness under an `` `Invalid `` / `` `FuelObstructed `` campaign, a `` `Malformed `` transcript, or a `` `NotRun `` slot returns `OBSTRUCTED`. `(T2)` is a campaign-level property,
checked separately from `(T1)`, not a kernel theorem.

## 5. Relative character of every result

No result is reported without identifying the **audit context**: the model
artifact and version; the inference specification (`inference_spec_digest`); the
preprocessing pipeline `N_P` (`preprocessing_digest`); the observable
representation selector; the input domain; the target predicate and registry
version; the operational-resolution map and `quantisation_rounding_mode`; the
numerical semantics; the model- and target-binding methods; and the policy
document version and digest.

## 6. Version 0 demonstration class

Frozen decisions (`PHASE_0_DECISIONS.md`):

- **Exact integer / fixed-point learned MLP.** Training may use floating point;
  the audited artifact is the exported integer model plus its committed inference
  specification (`inference_spec_digest`). Inference is
  `z^{(k+1)} = ReLU(rounddivᵥ(W^{(k)}·z^{(k)} + b^{(k)}, s_k, rescale_rounding_mode))`
  over mathematical integers, with `W^{(k)} : Mat Z rows_k cols_k`, no overflow,
  wrapping, or host float.
- **Quantiser `Q_P : Vec Z n_obs → Vec Z n_obs`** (length-indexed, so total),
  component-wise binning with `quantisation_rounding_mode` (independent of
  `rescale_rounding_mode`, which lives in the inference spec), **no saturation**.
  `rounddiv` is fully specified for negative operands and half-ties
  (`CLAIM_AND_DEFINITIONS.md` §7.2). The policy's expected observation range is a
  validity check on the raw observation, never a clamp.
- **In-kernel target predicate from a closed, versioned registry.** No
  policy-supplied predicate code.
- **Fixed-dimensional axis-aligned box domain `D_P`.**
- **Three result types**, defined from first principles: `BundleResult`,
  `WitnessResult`, `CampaignVerdict` (`VERDICT_SEMANTICS.md`).
- **Campaign record + `completeness_status`**, with a frozen verdict precedence in
  which a valid witness dominates an unrelated search obstruction.
- Strict JSON wire format; exact normalised integers inside the semantic checker;
  the extracted OCaml checker is the authoritative semantic implementation; the
  Python search process is wholly untrusted; `EXACT` is unreachable in v0.

## 7. Scope

**Included (v0):** one fixed-dimensional numerical input space; one small
deterministic integer model with a cryptographic digest; one committed
preprocessing spec; one named representation; one Boolean registry predicate; one
box domain; a deterministic unsaturated quantiser; exact equality after
quantisation; an untrusted Python witness generator; independent model
re-execution; in-kernel target evaluation; an extracted OCaml checking kernel
derived from Rocq definitions; a typed assessment result with explicit findings.

**Excluded (v0):** natural-language target predicates; unauthenticated human
labels; live sensor claims; large language models; medical diagnosis; autonomous
control; general neural-network verification; global robustness; topological or
persistent-homology claims; zero-knowledge proof of execution; TEE attestation;
Protobuf; autonomous repair. (Specification §5.2.)

## 8. Licence and Prior-Work Reuse

This project is licensed under the Apache License, Version 2.0.

The version 0 implementation copies no source code, formal definition text,
documentation prose, or project-specific build configuration from the author's
earlier AGPL-3.0 projects.

Prior projects are used as conceptual precedents and structural references only,
except where this charter explicitly records otherwise.

The extraction configuration will be independently authored against the current
project's definitions using Rocq's standard `ExtrOcamlZBigInt` facility. It will
not be copied from PCE's `ExtractR21.v`.

The wire-format implementation will be written afresh from this project's frozen
schema. It will not adapt PCE's `r21_format.ml`.

The generic witness-implies-non-factorisation theorem will be proved afresh.
PCOA's linear `QDescentFactorisation.v` and its `AdmissibilityGate` are not reused.

Any later proposal to copy or adapt material from an earlier project reopens the
per-entry ownership and licensing review before that material enters the
repository.

### 8.1 Rationale

Apache-2.0 permits commercial use, modification, distribution and sublicensing;
carries an explicit patent grant; is familiar to commercial engineering
organisations; and avoids the network-copyleft integration concern AGPL-3.0 could
raise for EDA or industrial-tool vendors.

Under the frozen reuse dispositions, no source code, formal-definition text,
documentation prose, or project-specific configuration from the prior AGPL-3.0
projects is incorporated into version 0. The new project is therefore licensed
independently under Apache-2.0, subject to its declared dependency obligations.

This is a project recommendation, not a legal opinion. It depends on the files
actually being authored afresh and on honouring the notices and conditions of any
distributed dependencies. Dependency licences are recorded in
`THIRD_PARTY_NOTICES.md`.

### 8.2 Documentation roles

- `PRIOR_WORK.md` — intellectual and architectural influences.
- `NOTICE` — copyright and attribution notices relevant to the distributed work.
- `THIRD_PARTY_NOTICES.md` — dependency licences and notices.
- `PHASE_0_REUSE_AUDIT.md`, `PHASE_0_REUSE_VERIFICATION.md` — the evidenced
  per-entry reuse decision.

## 9. Actors

- **Audit authority** — declares the policy; determines which distinctions matter
  and which operational resolution is relevant.
- **Candidate generator** — searches for witnesses; untrusted; may not determine
  the verdict, alter the policy, authorise its own tolerance, certify its own
  model outputs, or convert a null search result into an exactness claim.
- **Verifier** — parses and binds policy and bundle, obtains independently bound
  model observations, evaluates the registry predicate in-kernel, invokes the
  extracted semantic checker, and issues a typed result. It holds no authority to
  modify or disable the audited system.
- **Relying party** — decides how a certificate affects deployment, escalation,
  repair, publication, or governance.

## 10. Audience

Reviewers of formal-methods assurance claims; auditors of learned components;
downstream relying parties deciding deployment, escalation, or governance actions.

## 11. Relationship to the Phase 0 specification and to prior work

This charter is Unit 0A of the Phase 0 gate described in
`PHASE_0_CLAIM_SCOPE_TRUST_BOUNDARY.md` (a historical baseline — see
`PHASE_0_SPECIFICATION_AMENDMENTS.md`). The other governing deliverables are
`CLAIM_AND_DEFINITIONS.md` (0B), `TRUST_BOUNDARY.md` (0C), `VERDICT_SEMANTICS.md`
(0D), `AUDIT_POLICY_AND_EVIDENCE.md` (0E), `THREAT_MODEL.md` and `NON_CLAIMS.md`
(0F). The frozen decisions are consolidated in `PHASE_0_DECISIONS.md`;
`PHASE_0_PROPOSED_ANSWERS.md` is the archived decision-process record. Phase 0
closes with `PHASE_0_CLOSURE_REPORT.md` (0G) after a read-only cross-document
consistency audit (`PHASE_0_CONSISTENCY_AUDIT.md`).

The relationship to Proof-Carrying Exactness, Proof-Carrying Stream Exactness,
Proof-Carrying Observability Audit, and VeriBound is recorded in `PRIOR_WORK.md`:
conceptual and structural influence only, with no incorporation of their material.
