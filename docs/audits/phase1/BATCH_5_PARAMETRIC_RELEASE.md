# PHASE-1 PARAMETRIC RELEASE BOUNDARY REPORT

Closure Batch 5, 2026-10-01. **Phase 1 OPEN; Phase 2 unauthorised.**
This report records the premise/scope repair and current verification evidence.
The generated release summary records the final release run and its working-tree
manifest digest; this report is not a closure disposition.

## 1. Baseline

Clean starting SHA: `94d6b776af6d12159eeabce3535327b798fdb83c`. The clean-tree check, exact SHA check,
`make check` and `make release` all passed before edits. Baseline logs are
`/tmp/pcfw-batch5-baseline-check.log` and `/tmp/pcfw-batch5-baseline-release.log`.
No commits or pushes are authorised or performed in this batch.

## 2. Exact theorem statements changed

The seven declarations below keep their conclusions and replace only their local
policy antecedent in source. This was checked mechanically against `git show HEAD`.
Section-generalised parameter sequences also change: no `policy_payload_digest_of`,
its universal injectivity premise or `audit_policy_hash_committed` remains in
these seven interfaces. Parameters no longer used by each proof are dropped by
Rocq section discharge. All complete parameter sequences and the statements
are kernel-typechecked by [policy_surface.py](../../../implementation/scripts/policy_surface.py).

### `ManifestMatching.manifest_policy_matches_impl_sound`

```coq
Lemma manifest_policy_matches_impl_sound :
  forall ti,
    policy_binding p_committed ti ->
    parse_manifest (ti_manifest ti) = Some audit_view ->
    manifest_policy_matches_impl (ti_manifest ti) ti = true ->
    ti_policy ti = p_committed.
```

### `ManifestMatching.validate_campaign_concrete_binds_policy`

```coq
Theorem validate_campaign_concrete_binds_policy :
  forall ti ac l0,
    policy_binding p_committed ti ->
    validate_campaign ops ti = ValidCampaign ac l0 ->
    ti_policy ti = p_committed.
```

### `ManifestMatching.validate_campaign_concrete_binds`

```coq
Theorem validate_campaign_concrete_binds :
  forall ti ac l0,
    policy_binding p_committed ti ->
    validate_campaign ops ti = ValidCampaign ac l0 ->
    ti_policy ti = p_committed /\
    commits_impl (authenticated_commitment ac) committed_descriptor.
```

### `ManifestMatching.assess_validated_live_concrete`

```coq
Theorem assess_validated_live_concrete :
  forall ti ac l0 tr cb,
    policy_binding p_committed ti ->
    validate_campaign ops ti = ValidCampaign ac l0 ->
    assess_validated ops ti (ValidCampaign ac l0) (LiveTranscript tr cb)
    = decide ops
        (replay ops ac cb (ti_config ti) (ti_policy_document ti)
           p_committed l0 tr)
        ac ti tr (LiveCapture (op_transcript_digest ops tr))
        (AuthenticatedCommitment
           (commitment_digest (authenticated_commitment ac))).
```

### `ManifestMatching.assess_validated_offline_concrete`

```coq
Theorem assess_validated_offline_concrete :
  forall ti ac l0 tr wd cb,
    policy_binding p_committed ti ->
    validate_campaign ops ti = ValidCampaign ac l0 ->
    assess_validated ops ti (ValidCampaign ac l0)
      (OfflineParse (WellformedParse tr wd) cb)
    = decide ops
        (replay ops ac cb (ti_config ti) (ti_policy_document ti)
           p_committed l0 tr)
        ac ti tr (OfflineTranscript (op_transcript_digest ops tr) wd)
        (AuthenticatedCommitment
           (commitment_digest (authenticated_commitment ac))).
```

### `ManifestPipeline.validate_campaign_pipeline`

```coq
Theorem validate_campaign_pipeline :
  forall ti ac l0,
    ManifestMatching.policy_binding p_committed ti ->
    validate_campaign (pipeline_ops base) ti = ValidCampaign ac l0 ->
    manifest_authenticated_by_impl sha256_hex ed25519_verify ed25519_pubkey_valid (ti_config ti)
      (authenticated_commitment ac) (authenticated_manifest ac)
    /\ ti_policy ti = p_committed
    /\ pipeline_commits (ti_config ti) (authenticated_commitment ac)
         committed_descriptor.
```

### `ManifestPipeline.validate_campaign_audit_agrees`

```coq
Theorem validate_campaign_audit_agrees :
  forall ti ac l0,
    ManifestMatching.policy_binding p_committed ti ->
    validate_campaign (pipeline_ops base) ti = ValidCampaign ac l0 ->
    exists v,
      parse_manifest_impl (ti_manifest ti) = Some v /\
      cm_audit_instance_id v = committed_audit_instance_id.
```

The additional existing declaration `manifest_matching_core_hyps_consistent`
now removes its universal injectivity conjunct and includes the local binding
conjunct. Its current full statement is:

```coq
Lemma manifest_matching_core_hyps_consistent :
  (forall a b, String.eqb a b = true -> a = b) /\
  mm_mab mm_commitment mm_manifest /\
  mm_pm mm_manifest = Some mm_view /\
  cm_policy_hash mm_view = mm_ppd mm_p_committed /\
  mm_pco mm_p_committed = mm_D0 /\
  policy_digest_load_validated mm_ppd mm_ti /\
  policy_binding mm_p_committed mm_ti.
```

The unused injectivity helper `mm_ppd_injective` is removed. Three declarations
are added: `manifest_policy_matches_impl_digest_agrees`,
`validate_campaign_concrete_digest_agrees`, and
`digest_agreement_does_not_bind_policy`. The transparent `policy_binding`
definition is not a global axiom.

## 3. Old versus new policy premises

Previously, the seven results inherited the universal premise
`forall p q, policy_payload_digest_of p = policy_payload_digest_of q -> p = q`,
used with per-input `policy_digest_load_validated` and a committed policy-hash
agreement. Now their policy antecedent is:

```coq
Definition policy_binding (p_committed : policy) (ti : trusted_inputs) : Prop :=
  ti_policy ti = p_committed.
```

This is the smallest local identity premise. The policy-only theorem restates
supplied binding; successful validation does not establish it. The gate checks
this definition by reduction, so strengthening the named contract also fails.
`policy_digest_load_validated` remains available as separate digest truthfulness,
but it is no longer a policy-identity premise in these interfaces.

## 4. Proof changes

The root matcher and policy-only proofs use `exact Hbinding`. The full binding
proof uses that equality plus its existing context/authentication proof. The
live/offline proofs rewrite the existing assessment equations with the equality.
The pipeline and audit-id proofs use the equality directly and retain their
existing authentication, context-commitment and audit projection reasoning.
No computational matcher, pipeline builder or replay definition changes.

## 5. No digest-to-policy identity inference

No universal policy digest injectivity remains in project-owned formal source.
Digest comparison truth still means equality of digest strings, not injectivity
of a hash function. The formal independence example uses an abstract constant
hash to satisfy digest truthfulness and manifest matching while binding to a
different token is false. It neither constructs nor claims a SHA-256 collision.

## 6. Manifest and hash evidence retained

Manifest policy/context matchers and all authentication/record/ledger code are
unchanged. Existing canonical byte equality, recomputed tagged digests, signed
manifest validation and policy/context/hash mismatch rejection remain exercised.
Two new results expose parsed manifest hash equality with `ti_policy_digest`
without inferring policy identity. All twelve regenerated extracted `.ml`/`.mli`
files match baseline SHA-256 values byte for byte.

## 7. Revised release boundary

[RELEASE_CRITERIA.md](../../../RELEASE_CRITERIA.md) requires kernel closure,
`coqchk`, complete fail-closed inspection, exact-integer extraction, existing byte
checks/harnesses/differential tests and explicit premise accounting. Results are
relative to supplied semantic `Policy`/`AuditContext` and existing contracts.
Concrete semantic policy loading, target registration, arbitrary policy interpretation
and concrete quantisation are outside this parametric release. Phase 1 remains OPEN.

## 8. Trust taxonomy

[TRUST.md](../../../TRUST.md) distinguishes:

- **KERNEL-CHECKED:** conditional Gallina results, without unexpected global axioms.
- **EXECUTABLE-CHECKED:** existing manifest/record/byte/bigint and finite test evidence.
- **POLICY-REALISATION PREMISE:** supplied functions/context realise the intended policy.
- **TRANSCRIPT-FAITHFULNESS PREMISE:** unresolved/external observation and capture realisation.
- **IMPLEMENTATION TRUST:** extraction, compilers, runtime, I/O, handwritten wrappers and crypto.

Kernel closure is not premise discharge. The latter two premise categories are separate.

## 9. Nonclaims

[NONCLAIMS.md](../../../NONCLAIMS.md) explicitly excludes arbitrary policy
implementation/byte correctness, the learned model/training process as a whole,
truth of external observations, SHA-256 injectivity, collision resistance from
determinism, general correspondence from finite tests, certification and production
security. PCFW verifies claim conditions relative to a specified learned observation
regime; it does not verify the learned system in its entirety.

## 10. Public API boundary

`FibreWitnessKernel.Policy` contains supplied `domainb`, `quantise`, `target`.
`AuditContext` contains `context_policy`, `preproc`, `model`. Kernel, Stage-1/Stage-2
and `PipelineWiring.wired_ops` retain those semantic parameters. The lowercase
`Orchestration.policy` is a distinct opaque string token. Local `policy_binding`
equates tokens and does not establish the token/functional-policy association.
`ExtractPhase1Integration` exports `pipeline_ops`, validation/assessment and
evidence operations with supplied metadata callbacks/base; it does not install
`wired_ops` or load a functional context. Logical premises are erased in raw OCaml
APIs. Correct caller associations and callback contracts remain necessary.
See [implementation/README.md](../../../implementation/README.md).

## 11. Historical specification status

Banners in the charter, definitions and audit specification classify
`SyntheticTargetV0`, `rounddiv`, positive-width concrete quantisation,
no-clamping/no-saturation concrete quantisation and a closed target registry as
historical design specifications, not implemented release features. Existing
manifest-matching and byte-binding reports preserve old statements/evidence under
explicit supersession banners. No historical design body is deleted.
The larger relocation of existing root reports is deferred: it needs a separate
mechanical cross-reference/source-manifest cleanup rather than mixing archival
moves with the theorem review. This new report lives under `docs/audits/phase1`.

## 12. Files changed

- `implementation/rocq/ManifestMatching.v`, `ManifestPipeline.v`: premise/proof repair,
  separate digest results and abstract independence example.
- `implementation/scripts/policy_surface.py`, `test_gates.py`, `release.py`,
  `implementation/Makefile`: exact-interface gate, negative tests and generated evidence.
- `README.md`, `TRUST.md`, `NONCLAIMS.md`, `RELEASE_CRITERIA.md`,
  `implementation/README.md`, `PHASE_1_STATUS.md`, `IMPLEMENTATION_STATUS.md`:
  current parametric claim/API/acceptance account.
- `PROJECT_CHARTER.md`, `CLAIM_AND_DEFINITIONS.md`, `AUDIT_POLICY_AND_EVIDENCE.md`,
  `PHASE_1_MANIFEST_MATCHING.md`, `PHASE_1_BYTE_BINDING.md`: historical-status banners.
- This report and `MANIFEST.sha256`: review evidence and separately refreshed source inventory.

No extraction mapping, OCaml implementation, kernel core, faithful-transcript or
capture/replay implementation is changed. `git diff` is limited to Batch 5.

## 13. Tests and fail-closed evidence

Targeted Rocq compilation and the seven-interface audit pass. All 20 gate
regression tests pass. New negative fixtures compile a theorem with an additional
renamed universal injectivity premise, or a strengthened binding definition;
the interface gate rejects each. A restored local-equality fixture passes.
A missing theorem, exit-zero Error/Anomaly, missing/duplicated marker and nonzero
process result are also rejected. Removing the policy success evidence from the
release log fails release evidence validation. Failed release summaries preserve
PARAMETRIC/NOT_IN_PHASE1_SCOPE and never retain a stale passing status.
Existing real-Coq axiom, forbidden-token, build failure, manifest corruption,
integer/mirror and differential/byte gate regressions remain green.
Manifest wrong-policy-hash, verifier-digest and context-digest rejections pass.

## 14. `make check`

PASS, recorded in `/tmp/pcfw-batch5-final-check.log`. All substantive modules pass
`coqchk`; every release declaration is inspected with zero unexpected global
axioms, and the forbidden-token gate passes. All OCaml harnesses, bigint structural
checks, differential comparisons and byte-vector checks pass. The binding-definition
refinement was additionally tested directly and by the complete gate suite.

## 15. `make release`

PASS. A clean Batch-5 release run completed every required check and verified
all source-manifest entries before and after building. The final run is recorded
in `implementation/release-audit/summary.json` and `check.log`; the source report
and manifest ordering are finalised before its repeat verification. Success still
means **OPEN / NOT YET CLOSED**. The source manifest is refreshed separately;
the release procedure only verifies it.

## 16. Mechanical counts and generated evidence

The current source inventory and verified standalone check discover:

| Evidence | Count |
|---|---:|
| Substantive modules | 20 |
| Compiled modules | 26 |
| Extraction units | 6 |
| Inspected release declarations | 313 |
| Legacy assumption requests (retained subset) | 152 |
| Section-premise declarations | 95 |
| Policy interfaces | 7 |
| OCaml harnesses | 13 |
| Differential cases | 59 |
| Actual-Gallina / exact-Z-reference cases | 38 / 21 |
| Byte-boundary cases | 61 |
| Independent byte vectors | 3 |
| Manifest entries | 122 |

The audit count changes from 311 to 313 by removing one obsolete injectivity
helper and adding the two digest-only results and the independence example.
Five obsolete section-premise declarations are removed (100 to 95). Counts here
are generated from inventory/test evidence, not obtained by editing old totals.
Recorded tool versions: `The Coq Proof Assistant, version 8.18.0; compiled with OCaml 4.14.1`; OCaml `4.14.1`; `Python 3.12.3`.

The final summary additionally records tool versions, manifest entry count and
hash, base SHA, dirty working-tree status, all required check results,
`policy_mode: PARAMETRIC`, `concrete_semantic_policy_loader: NOT_IN_PHASE1_SCOPE`,
`faithful_transcript_status: UNRESOLVED` and OPEN release status.

## 17. Remaining blockers and residuals

**BLOCKING:** final parametric closure audit and acceptance of the public
premises/API boundary, bounded executable coverage, retained implementation trust
and reproducibility/CI arrangements or their explicitly accepted residual scope.
This batch issues no closure disposition.

**SHOULD FIX:** a separate history-report relocation and reference cleanup;
additional nonempty composed-pipeline coverage within the existing semantic API.
No concrete policy should be invented just to supply that coverage.

**DOCUMENTED RESIDUAL:** external policy/context realisation; unresolved transcript
faithfulness; extraction/compiler/runtime/crypto/I/O trust; unproved bounded ASCII
wrappers and parser/loader/`to_cv` contracts; bigint/domain refinements; finite-case
rather than general executable correspondence; absent full Unicode/config loading.
Final review must explicitly account for these, not silently treat them as proved.

**Is absence of a concrete semantic policy loader still a Phase-1 blocker? No.**
It is outside the adopted parametric scope. Closing Phase 1 still requires the
final claim/premise/trust/process review and explicit closure decision. Phase 2,
publication, tagging, commits and pushes are not authorised by this batch.
