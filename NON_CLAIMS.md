# Non-Claims

**Deliverable:** Phase 0, Unit 0F (with `THREAT_MODEL.md`)
**Status:** Draft for Unit 0G ratification. **Revision 14** — item 14: `(T2)` over
`assess_validated` (`validate_campaign` once per pipeline; pure core re-uses its
result); `faithful_transcript` never discharged, O4 = repeatability only;
`` `NotRun `` theorem scoped `(CAP1)` / `(REP1)`. Item 13 aligned with
`(T1)`/`(A1)`/`(T2)`; item 21 the historical-scope reading of certificate validity.

The project does **not** claim any of the following.

---

## 1. Scope of a witness

1. A validated fibre witness does not establish that the entire model is unsafe.
2. A witness does not establish failure outside the declared domain `D_P`.
3. A witness does not establish anything about inputs, representations, targets, or
   resolutions other than those the policy fixes.

## 2. The meaning of "no witness"

4. Failure to find a witness by heuristic search does not establish
   `FibreConstant(C)` (which, in v0, is by stipulation what "`Φ_P` factors through
   `M̃_C`" means — `CLAIM_AND_DEFINITIONS.md` §4.1).
5. `UNDERDETERMINED` warrants only "no valid witness was established by the
   recorded, non-blocked, non-complete campaign" — nothing about factorisation.
6. Version 0 does not produce `EXACT`. `EXACT` requires a checked
   `valid_completeness_certificate(C, c)` meeting the contract
   `(E1) valid_completeness_certificate(C, c) → FibreConstant(C)`; v0 defines the
   type and the contract but implements no producer.

## 3. Quantisation and observation

7. Quantised equality `Q_P(o_x) = Q_P(o_y)` does not establish equality of the raw
   activation vectors `o_x`, `o_y`.
8. The chosen quantisation `Q_P` is not claimed to be uniquely correct; it is a
   declared operational resolution (`AUDIT_POLICY_AND_EVIDENCE.md` §4).
9. `Q_P` performs no saturation in version 0; no claim depends on clamping
   behaviour, and a clamp-manufactured collision is out of scope.

## 4. The decoder

10. Version 0 asserts **neither** the existence **nor** the non-existence of a
    total decoder `Φ̂ : Vec Z n_obs → bool`. "Factors through" is defined by
    stipulation to mean `FibreConstant(C)` (`CLAIM_AND_DEFINITIONS.md` §4.1); the
    decoder characterisation would require additional finiteness, decidable-image,
    or choice assumptions not adopted here. The original specification §3's
    decoder equation and equivalence are superseded
    (`PHASE_0_SPECIFICATION_AMENDMENTS.md` D6).

## 5. The target predicate

11. The registry predicate `Φ_P` is not claimed to be morally, scientifically, or
    institutionally correct merely because the policy selects it. Its
    appropriateness is a specification-and-authority assumption
    (`TRUST_BOUNDARY.md` §F.2).
12. The method does not discover the model's internal semantics, nor identify a
    unique "effective observation map" for the model.

## 6. Formal scope

13. `(T1)` is a kernel theorem about pure data supplied to the kernel,
    parameterised by the policy `P` alone: it concludes that **no** observation
    function `g` agreeing with the supplied `o_x`, `o_y` at `x`, `y` can be
    fibre-constant-preserving for `Φ_P` on `D_P`. It does **not** mention any
    context, model, or execution. The step to `¬FibreConstant(C)` for the real
    context is `(A1)`, which adds the `ObservationBinding(C, ·, ·)` premises
    `model C (preproc C x) = o_x` and `model C (preproc C y) = o_y`. These are
    **not proved**; they follow conditionally from O6 (a re-execution transcript
    event whose input equals `preproc C x` / `preproc C y` and whose outcome is
    `` `Ok ``) plus the **assumed** F.3 premise `faithful_transcript tr C`
    (`CLAIM_AND_DEFINITIONS.md` §6, `TRUST_BOUNDARY.md` §F.3.1).
14. `(T2)` is a verified-orchestration property, not a kernel theorem. Scoped to
    `validate_campaign` (`VERDICT_SEMANTICS.md` §5–§7, `CLAIM_AND_DEFINITIONS.md`
    §6.3), over the pure total `assess_validated` / `replay` on one `` `Wellformed ``
    transcript, with an explicit `loaded_context` threaded through. `validate_campaign ti` is computed **once** per pipeline and
    `assess_validated` re-uses its result:
    `verdict_of (assess_validated ti V src) = INADMISSIBLE`
    **iff** `V = ` `Valid {campaign = ac ; …}`` **and** some `` `Done `` slot of
    `(replay ac …).stage2` has verdict `` `ValidWitness wd ``. A replayable witness
    under an `` `Invalid `` / `` `FuelObstructed `` campaign, a `` `Malformed ``
    transcript, or a `` `NotRun `` slot warrants nothing — `OBSTRUCTED`. The
    `INADMISSIBLE` warrant is additionally **conditional on the F.3 assumption
    `faithful_transcript tr rc.ctx`** and on `loaded_context` well-formedness (F.3)
    — O6 checks input-correctness and success, O4 checks repeatability only;
    **neither establishes faithfulness**. `(REP1)` holds for every certificate;
    `(CAP1)` (the transcript is an unmodified `capture` output) only when
    `transcript_evidence = LiveCapture`.
15. Formal verification does not establish the truth of unauthenticated real-world
    evidence.
16. The verifier does not certify robustness against every perturbation.
17. The method does not replace calibration, validation, safety engineering, or
    domain expertise.
18. Architectural separation between generator and verifier is not by itself a
    guarantee of independence; the independence claim rests on the trust boundary
    and the binding mechanisms.
19. Rocq→OCaml extraction is trusted subject to declared assumptions; a
    hand-written reimplementation in another language does not inherit `(T1)`.
20. The compiled binary is trusted to implement the extracted term by an assurance
    argument (reproducible build + differential testing), not by proof.

## 7. Certificate validity over time

21. A certificate remains valid as a statement about the exact artifacts, policy,
    preprocessing, inference specification, target-registry version, verifier, and
    kernel it binds by digest. It does **not** extend to any changed artifact,
    policy, or version — a change does not invalidate the historical statement, it
    puts the changed system outside the certificate's scope, and that system
    requires a fresh assessment.

## 8. Topological and manifold claims

22. No claim is made about the topology of activation data, persistent homology,
    or activation manifolds. A distance threshold is not claimed to define a
    mathematical fibre; version 0 uses exact quantised equality precisely to avoid
    that.

## 9. Prior work and licensing

23. No source code, formal-definition text, documentation prose, or
    project-specific build configuration from the author's earlier AGPL-3.0
    projects (PCE, PCSE, PCOA, VeriBound) is incorporated into version 0
    (`PRIOR_WORK.md`, `PHASE_0_REUSE_VERIFICATION.md`). Those projects influenced
    the architecture; they were not copied.
24. PCOA's `AdmissibilityGate` is not reused and its `GatedInadmissible`
    constructor is not renamed into this project; the result types are defined
    from first principles (`VERDICT_SEMANTICS.md`).
25. The Apache-2.0 licensing statement is a project recommendation, not a legal
    opinion (`PROJECT_CHARTER.md` §8).
