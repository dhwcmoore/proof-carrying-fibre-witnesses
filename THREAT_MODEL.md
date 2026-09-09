# Threat Model

**Deliverable:** Phase 0, Unit 0F (with `NON_CLAIMS.md`)
**Status:** Draft for Unit 0G ratification. **Revision 15** — adds T30
(context-bundle / stage-1 inconsistency), mitigated by the new
`InconsistentContextBundle` obstruction; see
`phase0_closure_package_r1/CONTEXT_BUNDLE_AMENDMENT.md`. Revision 14 —
`validate_campaign`
runs before any model call; the gated capture charges every fuel unit before its work and bounds the runner calls, so a hostile campaign consumes no model time
before authentication. O6 checks each transcript event's input equals
`preproc ctx x/y` (`ExecInputMismatch`). Manifest tampering → typed
`RecordIntegrity` (frozen first-failure precedence). Stage-2 order O6→O4→O5;
`\|subs\| > max_candidates` is an authentic oversized campaign (T14), not tampering
(T24).
**Assumption:** the candidate generator may be buggy, opportunistic, or malicious.

---

## 1. Threat inventory

Result column uses the tier ids of `AUDIT_POLICY_AND_EVIDENCE.md` §6
(B = bundle, C = candidate-fault, O = obstruction).

| # | Threat | Primary mitigation | v0 result on detection |
|---|---|---|---|
| T1 | **Fabricated observations** — the candidate reports activations the model never produced | The candidate supplies no authoritative observations; the verifier computes `o_x = model C (preproc C x)` by re-execution (tier O) | n/a (no such field) |
| T2 | **Fabricated targets** — reported target values not from the authorised predicate | `Φ_P` evaluated in-kernel from the bound registry predicate on the raw input | n/a (no such field) |
| T3 | **Policy substitution** — a permissive domain, quantiser, rounding mode, or target | `policy_hash` compared to `policy_digest` (B3); prohibited override fields (B2) | `REJECTED_BUNDLE` |
| T4 | **Model substitution** — candidate generated against a different artifact/version | `preflight_O1_O2` checks the policy-named artifact and checks bytes against `model_artifact_digest` (O1), once | `OBSTRUCTED` / `clo = ContextObstruction ArtifactMismatch` (O1) — the whole campaign, not one candidate; or `REJECTED_BUNDLE` (override field, B2) |
| T5 | **Representation substitution** — names one layer, values come from another | Structural `representation_id`; `eval_O3` asserts shape/type; the declared checkpoint must re-execute to `Vec Z n_obs` (O3) | `OBSTRUCTED` / `clo` (`RepNotReproduced`, O3) |
| T6 | **Preprocessing mismatch** — search and verification apply different `N_P` | Committed `N_P` with `preprocessing_digest`, checked once by `preflight_O1_O2` / `eval_O3` (O2) | `OBSTRUCTED` / `clo` (`SpecMismatch`, O2) |
| T7 | **Interpreter substitution** — same weights, different inference semantics (op order, rounding, ReLU placement) | `inference_spec_digest` binds the interpreter semantics, checked once by `preflight_O1_O2` / `eval_O3` (O2) | `OBSTRUCTED` / `clo` (`SpecMismatch`, O2) |
| T8 | **Numerical ambiguity** — rounding, half-ties, negatives, overflow | `rounddiv` fully defined for negatives and half-ties (`CLAIM_AND_DEFINITIONS.md` §7.2); `rescale_rounding_mode` and `quantisation_rounding_mode` declared separately; no float; overflow-free `Z`; B5 checks each literal is representable in its component `integer_type` (`AUDIT_POLICY_AND_EVIDENCE.md` §2.5.1) | `REJECTED_BUNDLE` (candidate literal, B5) / `WITNESS_CHECK_OBSTRUCTED` (re-execution failure, O6) |
| T9 | **Shape confusion** — arrays truncated, broadcast, reordered | Exact structural check (B4 for the candidate `x`/`y`); `eval_O3` shape/probe check; declared traversal order; no broadcasting | `REJECTED_BUNDLE` (B4, stage 1) / `OBSTRUCTED` `clo` (O3) |
| T10 | **Stale evidence** — a witness for an earlier model presented as evidence about a later one | `model_artifact_digest` binding, checked once by `preflight_O1_O2` / `eval_O3` (O1) | `OBSTRUCTED` / `clo` (`ArtifactMismatch`, O1) |
| T11 | **Replay across policies** — a bundle for one audit reused under another | `policy_digest` binding (B3); certificate binds the exact policy | `REJECTED_BUNDLE` (B3) |
| T12 | **Parser differential** — Python and OCaml interpret the same wire object differently | Strict closed schema; single canonicalisation rule; parser/schema/canonicaliser are in the F.3 TCB (blocker 5); the implementation-phase cross-language agreement battery | `REJECTED_BUNDLE` on the strict side; battery is the standing check; residual risk R4 |
| T13 | **Duplicate-key ambiguity** | Duplicate-key rejection (B1) | `REJECTED_BUNDLE` (B1) |
| T14 | **Resource exhaustion** — excessive dimensions, nesting, integer sizes, long re-execution, a campaign with too many candidates or that never terminates | Semantic bounds (§7.1); `verifier_config` limits (`AUDIT_POLICY_AND_EVIDENCE.md` §7.2) — bundle (§7.2.1), per-candidate **fuel** (§7.2.2), campaign **fuel** + `max_candidates` (§7.2.3); the normative campaign limit is a deterministic operation count, so the verdict is machine-independent given a fixed transcript; fail closed | bundle → `REJECTED_BUNDLE` (B6); per-candidate fuel → `WITNESS_CHECK_OBSTRUCTED` (O6, `ExecFuelExhausted`); campaign fuel → `OBSTRUCTED` (`clo = CampaignFuelExhausted`, crossing step `` `NotRun ``); `\|subs\| > max_candidates` → `OBSTRUCTED` (`clo = CampaignCandidateCountExceeded`) — **an authentic oversized campaign, not manifest tampering (cf. T24)** |
| T15 | **Target self-certification** — the model or generator supplies the alleged ground truth | `Φ_P` is an in-kernel registry predicate; no external target input in v0 | n/a (no such field) |
| T16 | **Identical-input contradiction** — the same input misreported as a collision | Check C1 (`x ≠ y`); no candidate target claims exist | `NOT_A_WITNESS` (C1) |
| T17 | **Unsupported-field smuggling** — hidden semantics in extension fields | Closed-schema validation; unknown critical field rejected (B2) | `REJECTED_BUNDLE` (B2) |
| T18 | **Certificate detachment** — a valid certificate displayed beside a different model/policy/bundle | The certificate binds policy digest, model digest, inference-spec digest, candidate digest, kernel digest; the UI is untrusted | detectable by re-checking the bindings in the certificate |
| T19 | **Kernel/binary divergence** — the compiled checker does not implement the extracted term | Reproducible builds + differential testing (`TRUST_BOUNDARY.md` §F.1.1); certificate records the execution-chain descriptor | assurance argument, not eliminated; residual risk R3 |
| T20 | **Search-result laundering** — a null heuristic search reported as `EXACT` | `EXACT` requires `valid_completeness_certificate(rc.ctx, c)` (`(E1)`), which in v0 always returns false (empty completeness-scheme registry — `VERDICT_SEMANTICS.md` §6.9); the `decide` precedence (§6.7) is replay-based, and the EXACT branch is only reachable on a `ContextResolved` context | `UNDERDETERMINED` (step 3 is dead code) |
| T21 | **Saturation-manufactured collision** — a quantiser clamp maps distinct large activations to one boundary value | `Q_P` performs no saturation in v0; `expected_observation_range` is a validity check, not a clamp | `WITNESS_CHECK_OBSTRUCTED` (O5) |
| T22 | **Preprocessing-target confusion** — a defect in `N_P` silently changes the target value | `Φ_P` consumes the **raw** input `x`, independent of `N_P` (`CLAIM_AND_DEFINITIONS.md` §3) | target value unaffected by `N_P`; an `N_P` defect surfaces as O2 / O3 |
| T23 | **Schema substitution** — a candidate written against a different (recognised) wire schema submitted under this policy | tier B1 requires `candidate.schema_version = policy_payload.bundle_schema_version` | `REJECTED_BUNDLE` (B1) |
| T24 | **Manifest / submission-set tampering** — an omitted / added submission, a reordered ledger, or a `rec.manifest_digest` / `policy_hash` mismatch | `validate_campaign` (`VERDICT_SEMANTICS.md` §5): `parse_commitment MCW` (frozen hex encodings, `AUDIT_POLICY_AND_EVIDENCE.md` §2.4.1) then `authenticate_manifest` (PureEdDSA/Ed25519 over `utf8(mc.digest)`, unique-signer trust anchor); `M.submission_digests` must equal `mapi submission_digest subs` **exactly, element-wise, in order, multiplicity preserved**; `rec` identity/manifest fields re-checked fail-closed; the committed append-only ledger is in the F.3 TCB | `OBSTRUCTED` / `RecordIntegrity <first-failure integrity_reason>` — a typed sum with frozen precedence |
| T25 | **Domain-separation confusion** — a digest of one object type presented as another (e.g. a `submission_digest` passed off as a `result_digest`) | every digest is `digest_v1(tag,·)` or `digest_bytes_v1(tag,·)` with a type-specific tag (`AUDIT_POLICY_AND_EVIDENCE.md` §2.2.4) | tag mismatch → the recomputed digest differs → the relevant integrity check fails closed |
| T26 | **Advisory-result forgery** — fabricated, detached, or policy-mismatched entries in `rec.recorded_results` (as opposed to the manifest, T24) | `rec.recorded_results` is **advisory**: the verdict is computed by replay, not from the record. A recorded result inconsistent with the replay sets a `campaign_record_mismatch` **finding** in the campaign report | verdict unchanged (= the replayed verdict); `campaign_record_mismatch` recorded |
| T27 | **Execution-resource abuse before authentication** — a hostile party submits a huge or unauthenticated campaign to make the verifier run the model | `validate_campaign` (once per pipeline; **charges each fuel phase before its work**) runs **before any model call**; the **gated capture** (`VERDICT_SEMANTICS.md` §6.4) then `charge`s each `stage1_check` / `preflight` / probe / candidate batch *before* doing it and stops at the first `` `Over ``; `\|subs\| > max_candidates` short-circuits to all-`` `NotRun ``; `parse_transcript` is bounded by `bundle_limits.max_transcript_bytes` | no model call on an `` `Invalid `` campaign; `OBSTRUCTED` (`RecordIntegrity …` / `TranscriptMalformed` / `CampaignCandidateCountExceeded` / `CampaignFuelExhausted`) |
| T28 | **Context bypass** — a hostile offline transcript carries stage-2 candidate events even though O1/O2/O3 would fail, hoping the verifier accepts a witness without a resolved context | The gated capture issues **no** candidate `call_request` before `eval_O3 lc = `Ok rc`; `replay` runs the same `charge`/gate sequence over the same `context_bundle` and marks every pending stage-2 slot `` `NotRun `` on any context failure, so a `` `Done `` `` `ValidWitness `` slot cannot exist without `ContextResolved` — `(REP1)`, `VERDICT_SEMANTICS.md` §6.6 | `OBSTRUCTED` / `clo = ContextObstruction …`; stray candidate events ignored |
| T29 | **Detached malformed transcript** — an obstruction certificate for `TranscriptMalformed` is presented next to a different malformed input | `parse_transcript` always computes `wire_digest := digest_bytes_v1("pcfw.exec_transcript_wire.v1", <raw bytes>)`; the certificate's `transcript_evidence = MalformedTranscript {reason ; wire_digest}` binds the exact bytes that failed to parse (`VERDICT_SEMANTICS.md` §3.1, §9) | re-checkable by recomputing `wire_digest` over the presented bytes |
| T30 | **Context-bundle / stage-1 inconsistency** — an offline package (or a tampered live one) pairs `ctx_not_needed` with a campaign whose stage 1 completes with `Pending` candidates, hoping `replay` proceeds without a resolved context or emits a misleading O1/O2/O3 finding | `replay` is total over an arbitrary `context_bundle` (`VERDICT_SEMANTICS.md` §6.6); this pairing is not a `capture` output and is reported as its own case — `context = ContextBundleInconsistent`, `clo = InconsistentContextBundle`, every pending stage-2 slot `` `NotRun ``, **no finding fabricated** (`ctx_reason` is not widened, so `CtxUnavailable` / `PreflightFail` cannot carry it). Offline reconstruction derives the bundle via `load_context` and never selects `CtxNotNeeded` for such a campaign. `(T2)` unaffected — no `` `ValidWitness `` can arise | `OBSTRUCTED` / `clo = InconsistentContextBundle`, obligation `reconstruct_or_supply_context_bundle` |

## 2. Minimum mitigations (summary)

- Policy-digest binding; model, preprocessing, **inference-spec**, representation,
  and predicate digests.
- Independent model re-execution: context checks O1–O3 once (preflight_O1_O2 + eval_O3)
  (failure → campaign obstruction; O3 uses the committed probe), per-candidate
  O6→O4→O5 in stage 2 (acquire, then compare for determinism, then range);
  in-kernel target evaluation on raw inputs in stage 1.
- Exact shape/type checking at both bundle and re-execution levels; exact integer
  normalisation; fully specified `rounddiv`; no float in the kernel; no saturation
  in `Q_P`.
- Strict closed schema; strict schema versioning; duplicate-key rejection;
  unknown-critical-field rejection.
- Semantic bounds fixed by policy; operational limits fixed by the verifier; both
  fail closed.
- Parser, schema validator, and canonicalisation layer in the F.3 TCB.
- Candidate and certificate digests; typed tier findings and failure reasons.
- Explicit `expiry` and version fields.
- Three-tier separation: `REJECTED_BUNDLE` (B), `NOT_A_WITNESS` (C),
  `WITNESS_CHECK_OBSTRUCTED` (O), then the campaign verdicts.
- Reproducible builds + differential testing for the execution chain.

## 3. Residual risks (not eliminated in v0)

- **R1 — System-binding TCB (`TRUST_BOUNDARY.md` §F.3):** the model loader, `N_P`
  implementation, inference implementation, hashing, **and the parser / schema
  validator / canonicalisation layer** are tested, not proved. A defect there
  could bind the kernel's verdict to values that do not reflect `A` or the
  authoritative policy.
- **R2 — Specification and authority (`§F.2`):** the policy may not express the
  authority's intended question; the registry predicate may be the wrong question;
  the quantisation resolution may not model a real interface.
- **R3 — Execution chain (`§F.1.1`):** the compiled binary is trusted to implement
  the extracted term via an assurance argument, not a proof.
- **R4 — Parser differential (T12):** mitigated by a strict schema, the F.3
  classification, and the implementation-phase agreement battery — not by proof.
  A future proof-checked raw-byte boundary (`TRUST_BOUNDARY.md` §F.3.2) would
  reduce this.
- **R5 — Extraction fidelity:** Rocq→OCaml extraction is trusted subject to the
  declared extraction assumptions and the itemised realisation-file TCB.

Each residual risk is named in the certificate's assumption section.

## 4. Threats deferred beyond version 0

- Adversarial or authenticated **external target authorities** — reintroduce a
  provenance and authority model.
- **Live sensor** provenance and time-of-measurement attestation.
- **Floating-point execution environments** — NaN/infinity/rounding/associativity
  threats become live and require the dyadic representation and pinned-environment
  mitigations.
- **Zero-knowledge / TEE** attestation of model execution as an alternative to
  independent re-execution.
- **Distance-threshold confusability** witnesses — a distinct witness type with
  its own soundness obligations.
- A **proof-checked raw-byte boundary** (`TRUST_BOUNDARY.md` §F.3.2) that removes
  the parser from the TCB.
