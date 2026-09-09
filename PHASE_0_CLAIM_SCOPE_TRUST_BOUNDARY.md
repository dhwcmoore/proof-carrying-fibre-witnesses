> ## AMENDMENT NOTICE — this document is a HISTORICAL BASELINE
>
> This is the **original Phase 0 specification** and the framing input for the
> gate. It is **superseded on specific points** by the frozen Phase 0
> deliverables. Where this document and a named deliverable disagree, the
> deliverable governs.
>
> - `PHASE_0_SPECIFICATION_AMENDMENTS.md` itemises every superseded element
>   (candidate bundle §6.2, verdict list §12, `CANDIDATE_ACCEPTED`, the §10 trust
>   structure, the §16 example verdicts, and more).
> - The governing documents are: `PROJECT_CHARTER.md`, `CLAIM_AND_DEFINITIONS.md`,
>   `TRUST_BOUNDARY.md`, `VERDICT_SEMANTICS.md`, `AUDIT_POLICY_AND_EVIDENCE.md`,
>   `THREAT_MODEL.md`, `NON_CLAIMS.md`, with `PHASE_0_PROPOSED_ANSWERS.md` as the
>   decision record.
>
> The original text is retained unchanged below for provenance.

---

# Proof-Carrying Fibre Witnesses for Learned Observation Regimes

## Phase 0: Claim, Scope, and Trust Boundary

**Status:** Superseded in part — see the amendment notice above and
`PHASE_0_SPECIFICATION_AMENDMENTS.md`  
**Phase type:** Specification and design gate  
**Implementation status:** No implementation is authorised by this document  
**Primary outcome:** A precise statement of what the system will check, what a successful check establishes, and which assumptions remain outside the formal kernel

---

## 1. Phase Objective

Phase 0 establishes the semantic and architectural foundation for a proof-carrying audit system that detects target-relevant observational collapse in learned representations.

The phase must answer five questions before any bundle schema, search heuristic, verifier, or model integration is implemented:

1. **What exactly is the claim being assessed?**
2. **What constitutes a valid witness against that claim?**
3. **Which facts are computed by the verifier, and which facts enter as external assumptions or authenticated evidence?**
4. **Which components and actors are trusted, for what purpose, and with what limitations?**
5. **Which verdicts may the system issue, and what does each verdict warrant?**

Phase 0 is complete only when these questions have unambiguous, reviewable answers. The purpose is to prevent the implementation from quietly replacing the intended claim with an easier but weaker one.

---

## 2. Project Working Title

**Proof-Carrying Fibre Witnesses for Learned Observation Regimes**

The title is provisional. It expresses the intended contribution: an untrusted search process may propose a witness, but an independent assurance process determines whether the submitted evidence establishes target-relevant observational collapse under a declared audit policy.

### 2.1 Terminology constraint

The term **fibre witness** will be used only when the audited operational observation map induces an actual equality relation. If the project instead uses a non-transitive distance threshold, the object will be called an **observational-confusability witness**.

The recommended version 0 design uses a declared quantisation map and exact equality after quantisation. This preserves the literal fibre structure.

---

## 3. Central Problem

Let:

- \(X\) be an input space;
- \(D_P \subseteq X\) be the domain authorised by audit policy \(P\);
- \(M_A : X \to O\) be the representation produced by audited model artifact \(A\) at a declared observable interface;
- \(Q_P : O \to \widetilde O\) be the operational-resolution or quantisation map fixed by policy \(P\);
- \(\widetilde M_{A,P}=Q_P\circ M_A\) be the operational observation map;
- \(\Phi_P : X \to \mathbb B\) be the target predicate fixed by policy \(P\).

The audit asks whether the target predicate factors through the operational observation map on the declared domain:

\[
\exists\widehat\Phi:\widetilde O\to\mathbb B
\quad\text{such that}\quad
\Phi_P|_{D_P}=\widehat\Phi\circ\widetilde M_{A,P}|_{D_P}.
\]

Equivalently, the audit asks whether \(\Phi_P\) is constant on every fibre of \(\widetilde M_{A,P}\) within \(D_P\).

A validated counterexample consists of \(x,y\in D_P\) such that:

\[
x\ne y,
\]

\[
\widetilde M_{A,P}(x)=\widetilde M_{A,P}(y),
\]

and

\[
\Phi_P(x)\ne\Phi_P(y).
\]

Such a pair proves that the target predicate does not factor through the operational observation map on the declared domain.

---

## 4. Version 0 Claim

### 4.1 Positive system claim

For an authorised audit policy \(P\), a committed model artifact \(A\), and a submitted candidate bundle \(B\), the system can independently validate whether \(B\) contains a target-divergent pair that the policy-defined operational observation map identifies.

If the system returns `INADMISSIBLE`, then, subject to explicitly discharged model-binding and target-binding obligations, the audited observation regime fails to preserve a distinction required by the declared target predicate within the declared domain.

### 4.2 Relative character of the claim

Every result is relative to:

- one model artifact and version;
- one preprocessing pipeline;
- one observable representation;
- one input domain;
- one target predicate;
- one operational-resolution map;
- one numerical semantics;
- one model-binding method;
- one target-binding method;
- one audit-policy version.

No result may be reported without identifying these parameters.

### 4.3 Constructive asymmetry

A single validated witness can establish inadmissibility on the declared domain. Failure to find a witness does not establish admissibility unless the search or proof procedure is complete for that domain.

Accordingly:

\[
\text{validated witness}\Longrightarrow\text{relative inadmissibility},
\]

but

\[
\text{no witness found by heuristic search}\not\Longrightarrow\text{exactness}.
\]

This asymmetry is a governing rule of the project.

---

## 5. Version 0 Demonstration Scope

The initial demonstration will be deliberately narrow.

### 5.1 Included

- A fixed-dimensional numerical input space.
- A small deterministic learned model.
- A committed model artifact with a cryptographic digest.
- A committed preprocessing specification.
- One named hidden representation or output tensor.
- A Boolean target predicate.
- An axis-aligned box domain.
- A deterministic quantisation map supplied by the audit policy.
- Exact equality after quantisation.
- An untrusted Python witness generator.
- Independent re-execution of the model for submitted witness inputs.
- Deterministic target evaluation for the initial synthetic demonstration.
- An extracted OCaml checking kernel derived from Rocq definitions.
- A typed assessment result with explicit findings.

### 5.2 Excluded from version 0

- Natural-language target predicates.
- Human expert labels without a separate provenance mechanism.
- Live sensor claims.
- Large language models.
- Medical diagnosis.
- Autonomous control of physical equipment.
- General neural-network verification.
- Global robustness claims.
- Topological claims about activation manifolds.
- Persistent-homology inference.
- Zero-knowledge proof of model execution.
- Trusted-execution-environment attestation.
- Protobuf optimisation.
- Autonomous repair of the observation regime.

These exclusions prevent the first implementation from acquiring unresolved semantic and institutional dependencies before the basic assurance claim has been demonstrated.

---

## 6. Core Objects

### 6.1 Audit policy

The audit policy is the authoritative statement of what must be checked. It is not supplied or altered by the untrusted witness generator.

The policy must identify:

- policy identifier and version;
- policy digest;
- audit instance identifier;
- accepted bundle-schema version;
- model artifact digest;
- model format and runtime version;
- preprocessing digest;
- input schema and dimensions;
- authorised input domain;
- observable representation identifier;
- representation shape and numerical type;
- quantisation or operational-resolution specification;
- target-predicate identifier, version, and digest;
- accepted model-binding method;
- accepted target-binding method;
- numerical semantics;
- resource limits;
- freshness or expiry requirements, if applicable.

The bundle may repeat selected policy fields for readability, but the verifier must compare them against the authoritative policy. A candidate cannot choose its own domain, tolerance, representation, target, or model version.

### 6.2 Candidate witness bundle

The candidate bundle is an untrusted claim presented for checking. At minimum it contains:

- schema version;
- referenced policy digest;
- candidate identifier;
- raw inputs \(x\) and \(y\);
- claimed model observations for \(x\) and \(y\);
- claimed target values for \(x\) and \(y\);
- model-execution evidence;
- target-evaluation evidence;
- provenance records;
- declared assumptions supplied by the generator;
- optional search metadata that is never treated as proof.

The candidate must not contain fields such as `domain_check_passed`, `equivalence_verified`, or `predicate_divergence_verified`. Those are checker results, not evidence.

### 6.3 Checked findings

The verifier computes a structured finding for every proof obligation:

- policy binding valid;
- bundle schema accepted;
- dimensions and types valid;
- inputs distinct;
- \(x\) in the authorised domain;
- \(y\) in the authorised domain;
- model artifact correctly identified;
- preprocessing correctly identified;
- model execution for \(x\) bound to the claimed observation;
- model execution for \(y\) bound to the claimed observation;
- target evaluation for \(x\) bound to the claimed target value;
- target evaluation for \(y\) bound to the claimed target value;
- quantised observations equal;
- target values differ;
- freshness requirements satisfied;
- no prohibited numerical values or malformed encodings encountered.

The final verdict is computed from these findings according to a fixed verdict policy.

### 6.4 Certificate

A certificate is the verifier-produced result, not the generator-produced candidate. It must bind:

- the exact policy;
- the exact candidate bundle;
- the verifier version;
- the checking-kernel version;
- all computed findings;
- the final verdict;
- the assumptions on which the verdict depends;
- the time or audit context, where relevant.

---

## 7. Operational Observation Semantics

### 7.1 Why raw distance is insufficient

A relation of the form

\[
\lVert M_A(x)-M_A(y)\rVert\leq\varepsilon
\]

is generally reflexive and symmetric but not transitive. It therefore does not necessarily induce fibres.

### 7.2 Version 0 decision

Version 0 will define a quantisation map \(Q_P\) in the audit policy and compare observations using exact equality after quantisation:

\[
Q_P(M_A(x))=Q_P(M_A(y)).
\]

The fibres under audit are the fibres of:

\[
\widetilde M_{A,P}=Q_P\circ M_A.
\]

This makes the result exact relative to a declared operational resolution. It does not claim that the unquantised activation vectors are equal.

### 7.3 Quantisation obligations

The policy must state:

- input numerical type;
- activation numerical type;
- rounding direction;
- bin width or scale;
- treatment of negative values;
- saturation behaviour;
- permitted range;
- treatment of signed zero;
- rejection of NaN and infinity;
- tensor traversal order;
- shape requirements.

The quantisation rule must be fixed before candidate evaluation. It cannot be selected after inspecting the candidate pair.

---

## 8. Numerical Semantics

### 8.1 Version 0 representation

The wire format should preserve model values as exact bit patterns or exact decimal encodings with a declared source type. The checking kernel should operate on normalised fixed-point integers or another exact internal representation.

### 8.2 Required constraints

- No unchecked host-language floating-point comparison in the formal kernel.
- No unspecified conversion between float32 and float64.
- No acceptance of NaN or positive or negative infinity.
- No dependence on associative rearrangement of floating-point operations.
- No metric selected by an unconstrained string.
- No silent dimension truncation or broadcasting.
- No integer overflow in normalisation or quantisation.

### 8.3 Future extension

Distance-bounded confusability relations may be added later as a distinct witness type. They must not be described as exact fibres unless an actual quotient or equivalence construction is supplied.

---

## 9. Actors and Responsibilities

### 9.1 Audit authority

The audit authority declares the policy. It determines which distinctions matter and which operational resolution is relevant.

It is responsible for:

- selecting the audited model and representation;
- defining the authorised domain;
- identifying the target predicate;
- approving the quantisation semantics;
- selecting accepted binding methods;
- approving verdict-use conditions.

### 9.2 Candidate generator

The candidate generator searches for possible witnesses. It is untrusted.

It may:

- inspect or query the model as permitted;
- use gradients, optimisation, enumeration, sampling, or other heuristics;
- propose inputs and supporting execution data;
- report search statistics.

It may not:

- determine the final verdict;
- alter the audit policy;
- authorise its own tolerance;
- certify its own model outputs;
- convert failure to find a witness into an exactness claim.

### 9.3 Model execution component

For version 0, the verifier independently re-executes the committed model artifact on the two submitted inputs using the committed preprocessing pipeline and runtime.

The model execution component is responsible for producing the observations that the checker compares with the candidate's claims.

### 9.4 Target authority

The target authority fixes the meaning and evaluation of \(\Phi_P\). In version 0, the target predicate will be deterministic and directly computable from the input.

Later versions may use authenticated labels, expert judgements, calibrated measurements, or institutional records. Each extension will require its own provenance and authority model.

### 9.5 Verifier

The verifier:

- parses and normalises the policy and bundle;
- enforces resource limits;
- binds the bundle to the policy;
- obtains independently bound model observations;
- obtains independently bound target values;
- invokes the extracted semantic checker;
- produces a typed verdict and complete findings.

### 9.6 Relying party

The relying party decides how the certificate may affect deployment, escalation, repair, publication, or governance. The verifier does not itself possess authority to modify or disable the audited system unless a separate control policy grants that authority.

---

## 10. Trust Boundary

### 10.1 Trusted for logical correctness

- Rocq kernel and accepted foundational libraries.
- Formal definitions used by the checking kernel.
- Extraction path, subject to the declared extraction assumptions.
- Extracted semantic checker.
- Audit policy as the authoritative statement of the assessment question.
- Exact numerical and quantisation semantics implemented by the checker.

### 10.2 Trusted for system binding

- Cryptographic digest implementation.
- Model artifact loader.
- Committed preprocessing implementation.
- Selected deterministic model runtime.
- Target evaluator for the version 0 demonstration.
- Mechanism that passes independently obtained values into the semantic checker.

These components are not automatically proved correct by the Rocq kernel. Their role and residual risk must be explicit in the certificate.

### 10.3 Untrusted

- Python search heuristic.
- Search metadata.
- Candidate-supplied pass or fail claims.
- Candidate-supplied model observations until independently bound.
- Candidate-supplied target values until independently bound.
- Candidate-selected assumptions.
- JSON field ordering, whitespace, and presentation.
- Transport channel.
- Any dashboard or user interface displaying the result.

### 10.4 Security-critical but outside the logical kernel

- JSON parser.
- Schema validator.
- Normalisation layer.
- Command-line interface.
- File-system access layer.
- Resource-limit enforcement.

These components must fail closed. Their correctness is tested and reviewed, but they are not to be confused with the proved semantic core.

---

## 11. Two-Level Assurance Claim

The project must distinguish kernel soundness from end-to-end system soundness.

### 11.1 Kernel-level theorem

The Rocq theorem concerns normalised values supplied to the kernel.

Informally:

> If the semantic checker accepts policy \(P\) and normalised candidate \(W\) as a fibre witness, then both inputs are distinct and lie within the declared domain, their policy-defined quantised observations are equal, and their supplied Boolean target values differ.

This theorem does not by itself prove that the supplied observations came from the real model or that the supplied target values came from the authorised target evaluator.

### 11.2 System-level theorem or assurance argument

The end-to-end claim adds binding premises.

Informally:

> If the system binds the checked observations to executions of the committed model artifact under the committed preprocessing pipeline, binds the checked target values to the authorised target evaluator, and the semantic checker accepts, then the audited operational observation map is inadmissible for the declared target predicate on the declared domain.

The end-to-end result is therefore conditional on the soundness of the selected binding mechanisms.

### 11.3 Required proof decomposition

The formal development should separate:

1. domain-membership soundness;
2. quantisation soundness;
3. operational-observation equality;
4. target-divergence soundness;
5. witness-implies-non-factorisation;
6. verdict soundness;
7. system-binding assumptions.

This decomposition prevents external execution assumptions from being hidden inside a theorem about pure data.

---

## 12. Verdict Semantics

Transport and parsing failures must be distinguished from epistemic verdicts.

### 12.1 Protocol results

#### `REJECTED_BUNDLE`

The submitted object could not enter assessment because it was malformed, used an unsupported version, exceeded resource limits, failed policy binding, or violated a mandatory structural constraint.

This is not a verdict about model admissibility.

#### `CANDIDATE_ACCEPTED`

The object is structurally valid and may be assessed. This is an internal workflow state, not an epistemic verdict.

### 12.2 Assessment verdicts

#### `INADMISSIBLE`

Issued only when all witness obligations and all policy-required model and target bindings succeed.

Meaning:

> The declared operational observation map fails to preserve a distinction required by the declared target predicate within the declared domain.

#### `UNDERDETERMINED`

Issued when the available checked evidence does not establish either inadmissibility or exactness. Examples include an incomplete search that finds no witness or a structurally coherent candidate whose evidence remains insufficient under a policy that permits partial assessment.

Meaning:

> The present evidence does not determine whether the factorisation condition holds.

#### `OBSTRUCTED`

Issued when a required assessment cannot be completed because a declared obligation is unavailable, incompatible, contradictory, expired, or defeated. Examples include an unavailable committed model artifact, conflicting target provenance, or a runtime incapable of reproducing the declared representation.

Meaning:

> A specific defect prevents completion or preservation of the requested warrant.

The certificate must identify the obstruction and the repair obligation.

#### `EXACT`

Reserved for a complete proof that the target predicate factors through the operational observation map on the declared domain.

A heuristic search that finds no witness can never produce `EXACT`.

Version 0 is not required to produce `EXACT`. The verdict is reserved so that later exhaustive finite checks, verified abstractions, or complete decision procedures can be incorporated without changing the fundamental assessment vocabulary.

---

## 13. Threat Model

Phase 0 assumes that the candidate generator may be buggy, opportunistic, or malicious.

### 13.1 Threats to be addressed

1. **Fabricated observations:** The candidate reports activations the model never produced.
2. **Fabricated targets:** The candidate reports target values not produced by the authorised predicate.
3. **Policy substitution:** The candidate selects a permissive domain, quantiser, tolerance, or target.
4. **Model substitution:** The candidate is generated against a different artifact or version.
5. **Representation substitution:** The candidate names one layer but supplies values from another.
6. **Preprocessing mismatch:** Search and verification apply different normalisation or feature ordering.
7. **Numerical ambiguity:** NaN, infinity, signed zero, rounding, overflow, or type conversion changes a result.
8. **Shape confusion:** Arrays are truncated, broadcast, reordered, or interpreted using inconsistent dimensions.
9. **Stale evidence:** A valid witness for an earlier model is represented as evidence about a later model.
10. **Replay across policies:** A bundle created for one audit is reused under another.
11. **Parser differential:** Python, OCaml, or another implementation interprets the same wire object differently.
12. **Duplicate-key ambiguity:** A JSON object contains repeated field names interpreted inconsistently.
13. **Resource exhaustion:** A bundle uses excessive dimensions, nesting, or integer sizes.
14. **Target self-certification:** The audited model or generator supplies the alleged ground truth.
15. **Identical-input contradiction:** The same input is paired with conflicting target claims and misreported as a fibre collapse.
16. **Unsupported-field smuggling:** Unrecognised semantics are hidden in extension fields.
17. **Certificate detachment:** A valid certificate is displayed beside a different model, policy, or bundle.

### 13.2 Minimum mitigations

- Policy digest binding.
- Model, runtime, preprocessing, representation, and predicate digests.
- Independent model re-execution in version 0.
- Independent deterministic target evaluation in version 0.
- Exact shape checking.
- Exact numerical normalisation.
- Strict schema versioning.
- Duplicate-key rejection.
- Unknown-critical-field rejection.
- Resource limits fixed by policy.
- Candidate and certificate digests.
- Typed findings and failure reasons.
- Explicit freshness and version fields.
- Separate treatment of malformed bundles and epistemic obstruction.

---

## 14. Non-Claims

The project does not claim that:

1. A witness establishes that the entire model is unsafe.
2. A witness establishes global failure outside the declared domain.
3. Failure to find a witness establishes admissibility.
4. Quantised equality establishes equality of raw activation vectors.
5. The chosen quantisation is uniquely correct.
6. The target predicate is morally, scientifically, or institutionally correct merely because it is declared.
7. Formal verification establishes the truth of unauthenticated real-world evidence.
8. The verifier certifies robustness against every perturbation.
9. The method replaces calibration, validation, safety engineering, or domain expertise.
10. The method discovers the model's complete internal semantics.
11. A hidden-layer representation is the model's unique effective observation map.
12. A distance threshold automatically defines a mathematical fibre.
13. Topological features in activation data automatically constitute obstruction certificates.
14. Architectural separation alone guarantees independence.
15. A hand-written Rust or Python reimplementation automatically inherits the Rocq theorem.
16. A valid past certificate remains valid after the model, policy, preprocessing, target, or runtime changes.

---

## 15. Phase 0 Work Units

### Unit 0A: Project Charter

**Objective:** Fix the problem statement, intended contribution, audience, and version 0 demonstration.

**Tasks:**

- Adopt or revise the working title.
- State the central problem in factorisation and fibre language.
- Select the version 0 demonstration class.
- Record included and excluded scope.
- Identify the relationship to existing Proof-Carrying Exactness, VeriBound, Proof-Carrying Stream Exactness, and Proof-Carrying Observability Audit components.

**Deliverable:** `PROJECT_CHARTER.md`

### Unit 0B: Formal Vocabulary and Claim

**Objective:** Eliminate ambiguity in the words observation, representation, fibre, confusability, target, policy, witness, and certificate.

**Tasks:**

- Define \(X\), \(D_P\), \(M_A\), \(Q_P\), \(\widetilde M_{A,P}\), and \(\Phi_P\).
- State the exact witness condition.
- State the constructive asymmetry between finding and not finding a witness.
- State the kernel-level theorem target.
- State the end-to-end assurance claim and its premises.
- Decide when the term fibre is permitted.

**Deliverable:** `CLAIM_AND_DEFINITIONS.md`

### Unit 0C: Trust and Authority Model

**Objective:** Identify who declares, generates, checks, maintains, and relies upon each object.

**Tasks:**

- Identify the audit authority.
- Mark the search process as untrusted.
- Define the model-execution binding.
- Define the target-evaluation binding.
- Identify the logical trusted computing base.
- Identify security-critical components outside the proved kernel.
- Separate epistemic assessment authority from authority to act.

**Deliverable:** `TRUST_BOUNDARY.md`

### Unit 0D: Verdict Algebra

**Objective:** Define every result and prevent negative search results from becoming false certificates.

**Tasks:**

- Separate protocol rejection from epistemic assessment.
- Define `INADMISSIBLE`, `UNDERDETERMINED`, `OBSTRUCTED`, and `EXACT`.
- Define the exact obligations required for `INADMISSIBLE`.
- Reserve `EXACT` for complete procedures.
- Define repair information required for `OBSTRUCTED`.
- Define machine-readable findings and failure reasons.

**Deliverable:** `VERDICT_SEMANTICS.md`

### Unit 0E: Audit Policy and Evidence Obligations

**Objective:** Ensure that the generator cannot choose the conditions under which its own candidate is accepted.

**Tasks:**

- Define mandatory audit-policy fields.
- Fix the version 0 operational-resolution mechanism.
- Define numerical semantics.
- Define model, preprocessing, runtime, representation, and target commitments.
- Define bundle-to-policy binding.
- Define model-output and target-value provenance obligations.
- Define certificate binding and freshness requirements.

**Deliverable:** `AUDIT_POLICY_AND_EVIDENCE.md`

### Unit 0F: Threat Model and Non-Claims

**Objective:** Record foreseeable ways in which a superficially successful implementation could issue an unwarranted result.

**Tasks:**

- Complete the adversarial threat inventory.
- Define minimum mitigations.
- State residual risks.
- State non-claims.
- Identify which threats are deferred beyond version 0.

**Deliverables:** `THREAT_MODEL.md` and `NON_CLAIMS.md`

### Unit 0G: Phase Review and Freeze

**Objective:** Determine whether implementation may begin.

**Tasks:**

- Conduct terminology review.
- Conduct theorem-statement review.
- Conduct trust-boundary review.
- Conduct adversarial review of the proposed claim.
- Resolve or explicitly defer every blocking question.
- Freeze version 0 policy semantics.
- Record the authorised Phase 1 scope.

**Deliverable:** `PHASE_0_CLOSURE_REPORT.md`

---

## 16. Required Manual Examples Before Phase 1

Phase 0 must specify, on paper, the expected outcome for each of the following cases. These examples will become executable fixtures in later phases.

| Case | Expected result | Reason |
|---|---|---|
| Valid target-divergent operational collision | `INADMISSIBLE` | All witness and binding obligations hold |
| One input outside the domain | Candidate rejected or witness obligation fails | The theorem is domain-relative |
| Quantised observations differ | Not a valid witness | No operational fibre collision |
| Target values agree | Not a valid witness | No target divergence |
| Candidate selects a different quantiser | `REJECTED_BUNDLE` | Policy mismatch |
| Candidate selects a larger tolerance | `REJECTED_BUNDLE` | Generator cannot weaken the audit policy |
| Model digest differs | `REJECTED_BUNDLE` or `OBSTRUCTED` according to processing stage | Audited artifact is not bound |
| Claimed activation differs from re-execution | Candidate rejected | Fabricated or stale model output |
| Target claim differs from authorised evaluation | Candidate rejected | Target binding failed |
| Model artifact unavailable | `OBSTRUCTED` | Required binding cannot be completed |
| Heuristic search returns no candidate | `UNDERDETERMINED` | Search incompleteness prevents `EXACT` |
| Identical inputs with conflicting target claims | Candidate rejected | Target inconsistency, not a fibre witness |
| NaN or infinity occurs | `REJECTED_BUNDLE` or `OBSTRUCTED` according to origin | Numerical semantics prohibit it |
| Tensor shape mismatch | `REJECTED_BUNDLE` | Structural invalidity |
| Unsupported schema version | `REJECTED_BUNDLE` | No authorised interpretation exists |
| Complete finite analysis proves factorisation | `EXACT` | Permitted only when completeness is established |

---

## 17. Phase 0 Decisions Recommended for Adoption

1. **Use a policy-defined quantised observation map for version 0.**
2. **Use exact equality after quantisation rather than an informal notion of closeness.**
3. **Use a Boolean target predicate for version 0.**
4. **Use a fixed-dimensional numerical input domain.**
5. **Use a deterministic synthetic target that the verifier can evaluate independently.**
6. **Use independent model re-execution to bind activations to inputs.**
7. **Use JSON with a strict schema for the first wire format.**
8. **Use exact normalised numerical values inside the semantic checker.**
9. **Use the extracted OCaml checker as the authoritative semantic implementation.**
10. **Treat the Python search process as wholly untrusted.**
11. **Treat Rust as a possible later hardened parser or differential implementation, not as automatically verified.**
12. **Separate bundle rejection from epistemic verdicts.**
13. **Do not require version 0 to produce `EXACT`.**
14. **Do not begin TDA, medical, LLM, or human-intelligence extensions during the initial vertical slice.**

---

## 18. Open Questions to Resolve in Phase 0

### 18.1 Formal questions

- Will factorisation be represented constructively by an explicit decoder or propositionally by fibre constancy?
- Which parts of the version 0 witness theorem should be reusable from existing exactness developments?
- How will the quantisation map be represented in Rocq?
- Does the kernel accept quantised observations, or does it perform verified quantisation itself?
- Which assessment conditions produce `OBSTRUCTED` rather than protocol rejection?

### 18.2 Execution questions

- Which model format will be used for the first deterministic demonstration?
- Which runtime version and deterministic settings will be committed?
- How will the observable layer be identified without ambiguity?
- Will preprocessing execute inside the verifier process or in a separately checked component?
- How will exact activation values be serialised before quantisation?

### 18.3 Policy questions

- Who authors and signs or otherwise commits the policy in the demonstration?
- How will the policy's quantisation resolution be justified?
- Are freshness requirements necessary for the initial offline demonstration?
- Which resource limits belong in the policy and which belong in the verifier configuration?

### 18.4 Certificate questions

- Will the certificate contain the complete witness or only its digest and findings?
- How will a certificate be bound to the verifier and kernel versions?
- Which assumptions must be rendered for a human reader?
- What minimum information is necessary for independent replay?

No question that changes the meaning of `INADMISSIBLE` may be deferred beyond Phase 0.

---

## 19. Phase 0 Exit Criteria

Phase 0 is complete only when all of the following are true:

- [ ] The version 0 claim is stated formally and in plain language.
- [ ] The kernel-level theorem and system-level assurance claim are separated.
- [ ] The version 0 domain, model class, representation, target, and operational resolution are fixed.
- [ ] Every trusted component is identified with a specific role.
- [ ] Every untrusted input is identified.
- [ ] Model-output binding is specified.
- [ ] Target-value binding is specified.
- [ ] The generator cannot select or weaken the governing audit policy.
- [ ] Numerical semantics are deterministic and complete.
- [ ] The word fibre is used only for an actual equality-induced fibre.
- [ ] Protocol rejection and epistemic verdicts are separated.
- [ ] `INADMISSIBLE`, `UNDERDETERMINED`, `OBSTRUCTED`, and `EXACT` have non-overlapping definitions.
- [ ] A negative heuristic search cannot produce `EXACT`.
- [ ] The threat model covers fabricated values, substitution, replay, parser ambiguity, and resource exhaustion.
- [ ] Non-claims are recorded.
- [ ] Expected results for all required manual examples are agreed.
- [ ] No unresolved question changes the meaning of a successful certificate.
- [ ] The precise scope of Phase 1 is authorised in a closure report.

---

## 20. Definition of Done

Phase 0 is done when a sceptical reviewer can answer all of the following without inspecting implementation code:

1. What proposition does an `INADMISSIBLE` certificate establish?
2. Which model, representation, target, domain, and operational resolution does it concern?
3. Why is the candidate generator unable to certify its own claims?
4. How are observations bound to actual model executions?
5. How are target values bound to the authorised predicate?
6. Which part of the result is formally proved?
7. Which part depends on external execution or provenance assumptions?
8. Why does failure to find a witness not establish exactness?
9. What would cause the assessment to be underdetermined or obstructed?
10. What may a relying party legitimately do with the resulting certificate?

If any answer remains implicit, Phase 0 remains open.

---

## 21. Authorised Next Phase After Closure

Once Phase 0 closes, Phase 1 may begin with a narrow objective:

> Define the Rocq semantic objects and prove the kernel-level soundness theorem for policy-bound, quantised Fibre Witnesses over a fixed-dimensional numerical domain.

Phase 1 should not yet integrate Python search, a production model runtime, TDA, Protobuf, or autonomous repair. Its purpose is to establish the small semantic kernel that every later component must obey.

