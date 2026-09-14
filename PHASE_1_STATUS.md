# Phase 1 status ledger

Date: 2026-09-06
Authoritative acceptance criteria: the **"Open Phase 1 work"** list in
`PHASE_0_CLOSURE_REPORT.md`. `PROJECT_CHARTER.md` §7 defines the v0 *claim*
scope (included / excluded); it does not defer any implementation obligation to
a later phase, and there is no phase defined below Phase 2. **No obligation
below has been moved.** Phase 1 is **OPEN**; Phase 2 is not authorised.

This ledger is author-prepared status. Every "done" row is source-reviewed by
the designated reviewer and machine-checked on the implementation machine
(`coqc` / `ocamlc` 8.18.0 / 4.14.1); the reviewer's environment lacks the
toolchain, so the reviewer's concurrence is by source inspection only.

## Closure-report obligation 1 -- the five Admitted orchestration theorems

> Prove `T2_sound`, `T2_complete`, `stage1_over_is_terminal`,
> `exact_unreachable_v0`, `validation_fuel_obstructed_unreachable_when_sufficient`.

**DONE.** `PHASE_1_ORCHESTRATION_PROOFS.md`. All five `Qed`, axiom-free
(`make assumptions`). Reviewer-concurred, promoted. Caveat recorded there:
`T2_sound` / `T2_complete` are witness-selection control-flow theorems, not
execution faithfulness.

## Closure-report obligation 2 -- `primitive_ops` and its contracts

> Implement `primitive_ops` and establish its required contracts, including
> `stage2_witness_index_contract`, and the correspondence to the semantic kernel
> and specified execution / boundary behaviour.

**PARTIAL.**

> **Promotion (2026-09-13).** The `op_completeness_wellformed` unit (revision 1
> held; revision 2 held -- blocker 1 concurred closed, blocker 2 persisted in
> an unsatisfiable global premise; **revision 3 reviewer-concurred by source
> inspection and promoted** -- reviewed ZIP sha256
> `b4298a2c4f0bdecd7d601a71830bd2e1ecbf1d8cba567f85168f9ade7df3cae3`) makes the
> LAST `validate_campaign` guard concrete: `wellformed_scheme` (non-empty
> only) + `wellformed_body` (the ASCII-wire canonical subset, reviewer-
> concurred as v0's scope) over an independent `completeness_status_wf`
> relation, plus `record_completeness_load_validated` -- a per-input
> `Definition`, not a blanket `Hypothesis` (revision 2's global form was
> inconsistent: two `trusted_inputs` can share `ti_record` while differing in
> `ti_completeness`) -- binding the checked value to `ti.rec.completeness`
> itself. See `PHASE_1_COMPLETENESS_WELLFORMED.md`.
>
> **Promotion (2026-09-10).** The `op_record_crosscheck` unit (r14 held; r15
> partial; r16 held; **r17 reviewer-concurred by source inspection and
> promoted** -- reviewed ZIP sha256
> `476c32c3bbdade74323481ec8b7cba87ac77d1e9e375074d6465f5418de10de1`) applies a
> spec-conformance **data-representation repair to `Orchestration.v`**
> (`finding` `+offending`; `parsed_candidate` `+candidate_id`; `stage1_result`
> `+candidate_id`/`+semantic_digest` -- VERDICT_SEMANTICS §2/§4.1 already ahead)
> plus an F.3 `candidate_id_of` in `Stage1Wrapper`/`PipelineWiring` and an
> `offending` arg on `ContextResolution.pass_finding`. All promoted r5–r13
> theorems are **re-proved**; the only statement change is
> `Stage1Wrapper.wrapper_reject_not_pending`, additive. (The earlier
> reviewer-concurred r5–r13 promotion was against the r13 bytes; the r17
> disposition covers the modified `Orchestration.v` / `Stage1Wrapper.v` /
> `PipelineWiring.v` / `ContextResolution.v`.) The bounded consistency erratum
> `PHASE_1_ADVISORY_FINDING_IDS_ERRATUM.md` (advisory `record_findings`
> identifier domain) is **reviewer-concurred** and applied to `VERDICT_SEMANTICS.md`
> §2/§6.5, `AUDIT_POLICY_AND_EVIDENCE.md` §2.2.5, `THREAT_MODEL.md` T26 (the
> historical Phase 0 closure package is unchanged). The cumulative
> **r5–r13 validation block** --
> `op_parse_commitment` / `op_signer_authorised` / `op_signature_valid`
> (`ManifestAuthentication`), `op_manifest_policy_matches` /
> `op_manifest_context_matches` (`ManifestMatching`), `op_ledger_mismatch`
> (`ManifestLedger`), `op_manifest_audit_matches` (`ManifestAudit`),
> `op_record_identity_mismatch` (`CampaignRecord`), and their
> `ManifestPipeline` integration -- is **reviewer-concurred by source inspection
> and promoted** (reviewer disposition on r13; the reviewed r13 bytes,
> ZIP sha256 `7691bc1d05d1fb85648da9126372476589acd9971b2decc997c37dd424335419`).
> Still **not** a Phase 1 closure. The rows below are unchanged in substance.

| `primitive_ops` member | status |
|---|---|
| `op_stage2_check` | concrete (`Stage2.stage2_check` + `Stage2Adapter.adapter_stage2_check`); `stage2_witness_index_contract` **discharged** (`adapter_satisfies_index_contract`); `S2Valid` -> `CheckedWitness` **proved** (`adapter_valid_supplies_checked_witness`); `ObservationBinding` proved conditional on transcript faithfulness (`adapter_valid_observation_binding`); reporting-conformance proved **under** `adapter_candidate_wf` + `transcript_stage2_wf` (`adapter_reporting_conformance`) |
| `op_stage1_check` | concrete semantic core (`Stage1.stage1_semantic_check`) + F.3 wrapper (`Stage1Wrapper.op_stage1_wrapper`); the pending-output soundness contract `op_stage1_sound` **discharged** for any wrapper-backed op (`wrapper_op_stage1_sound`); B4<B5<C1 precedence proved |
| pending-invariant propagation | `run_stage1` / `replay` carry the invariant (`Stage1Invariant`); adapter C-recheck proved redundant for reachable pending submissions (`adapter_c_recheck_redundant`) |
| `op_preflight`, `op_eval_o3` | concrete, **descriptor- and spec-bound**: `preflight_check` parses `loaded_descriptor lc` into a structured `descriptor` and checks the loaded byte-digests against its fields (`preflight_ok_binds`; changing the descriptor changes acceptance). `preflight_ok_artifact_bound`: `PreflightOk` + `parse = Some committed_descriptor` ⇒ `byte_digest_consistent lc committed_descriptor` ∧ `commits committed_authcommitment committed_descriptor` ∧ `realises_C lc` (the last now a *consequence* of digest-consistency, not opaque). `eval_o3_check` derives the probe from `loaded_inference_bytes lc` via `probe_of_spec` (O2 checked those bytes' digest); `eval_o3_ok_binds` exposes that. **Still F.3-external**: `parse_descriptor` / `probe_of_spec` correctness; `commits …` (manifest auth chain); the loaded descriptor being the committed one; digest-fn truthfulness. **Wired** (`PipelineWiring.wired_ops`): `op_stage1_check` / `op_preflight` / `op_eval_o3` / `op_stage2_check` all closed over the same committed `C`; `wiring_resolution_consistent` proves the wired preflight/O3 succeeding ⇒ `resolve = Some (C, rc)` and both checkers are the `C`-closed ones; `wired_ops_op_stage1_sound` + `wired_ops_stage2_index_contract` discharge the two `primitive_ops` obligations for `wired_ops`; `wired_run_stage1_pending_invariant` (about the `run_stage1` pending list `replay` threads unchanged) + `wired_c_recheck_redundant` carry it forward. Reviewer kept the dimension-agnostic `resolved_context` -- structural single-context not needed, and no separate `replay`-level `rc`-threading theorem needed. **replay path supplies `p_committed` to `op_eval_o3`**: proved concretely for the wired manifest matchers -- `ManifestMatching.assess_validated_{live,offline}_concrete` show `assess_validated`'s `replay` call runs with `p = p_committed` given `policy_digest_load_validated ti` + `validate_campaign` success, no opaque contract. **descriptor ↔ manifest-commitment binding**: `ManifestMatching.validate_campaign_concrete_binds` gives `commits_impl (authenticated_commitment ac) committed_descriptor` under the same. **Still open (explicit)**: the inherited validation-tier `base` members (audit/record/completeness/crosscheck/transcript-digest); `committed_context_wf`; digest / `lower_parse` / `parse_literal` truthfulness; **probe derivation from `loaded_inference_bytes` + checkpoint shape/type**; a meaning for `realises`. (`parse_manifest` and `manifest_authenticated_by` are now **concrete** -- see the `op_parse_commitment` row.) |
| `op_manifest_policy_matches`, `op_manifest_context_matches` | **concrete** (`ManifestMatching.manifest_policy_matches_impl` / `manifest_context_matches_impl` over a parsed `campaign_manifest_view`); `ValidationBinding`'s two opaque contracts **replaced** by capstone `validate_campaign_concrete_binds` + `assess_validated_{live,offline}_concrete` (the same replay-policy statements, no opaque contract). `parse_manifest` is now **concrete** (`ManifestAuthentication.parse_manifest_impl`) and wired in by `ManifestPipeline` (see the `op_parse_commitment` row); `manifest_authenticated_by` is now `manifest_authenticated_by_impl` (concrete, modulo the F.3 `sha256_hex` / `ed25519_verify` / `ed25519_pubkey_valid`). Residuals: the audit's **fixed** `audit_manifest`/`audit_view` with `audit_manifest_parses` / `audit_policy_hash_committed`; `validated_{commitment,manifest}_is_audit` connecting a successful validation to those objects (retrieval integrity); `policy_payload_digest_injective`; per-input `policy_digest_load_validated ti` (§2.3). `commits` given concrete `commits_impl`. `validate_campaign_concrete_binds_policy` is the policy-only capstone (no context-side dependency); the replay corollaries go through it. `manifest_matching_core_hyps_consistent` proves the **seven core non-`ops`** facts mutually consistent (not the `ops` hypotheses or a validation instance -- a consistency result, not full satisfiability). See `PHASE_1_MANIFEST_MATCHING.md` |
| `op_parse_commitment`, `op_signer_authorised`, `op_signature_valid` | **concrete, standalone AND integrated** (`ManifestAuthentication`: `parse_commitment_impl`; `signer_authorised_impl`; `signature_valid_impl` -- recompute `campaign_manifest_digest`, trust-anchor key lookup, Ed25519 over `utf8(mc.digest)`). `parse_manifest` / `manifest_authenticated_by` concrete: `parse_manifest_impl` is a **schema-conforming** decoder (UTF-8 gate; §2.2.2 escape decoding + raw-control rejection; 64-lowercase-hex digest fields; trailing-comma rejection) with a **round-trip theorem** `parse_manifest_impl_roundtrip` under `manifest_roundtrip_wf` (64-lowercase-hex digest fields; identifier bytes all ASCII 0x20..0x7E except `"` and `\`; canonical key order supplied by `render_manifest`, not by `manifest_roundtrip_wf`), plus `vm_compute` vectors (schema-valid round-trip; short-digest frozen vector rejected). **Integration** (`ManifestPipeline`): `pipeline_ops` = auth impls + `manifest_{policy,context}_matches_impl … parse_manifest_impl` over the shared `CanonicalV1.campaign_manifest_view`; `validate_campaign_pipeline`: one `validate_campaign` success ⇒ `manifest_authenticated_by_impl (ti_config ti) …` **and** `ti_policy ti = p_committed` **and** `pipeline_commits (ti_config ti) (authenticated_commitment ac) committed_descriptor` (manifest→descriptor in the shared `context_descriptor` type), no opaque `parse_manifest`. `parse_manifest_impl_wf` proves any accepted manifest is `CanonicalV1.manifest_wellformed`; the decoder covers the **canonical ASCII-wire subset** (keys ascending, ASCII ids -- explicit input requirement). **F.3**: `sha256_hex`, `ed25519_verify`, `ed25519_pubkey_valid` (now run by `signature_valid_impl` on the validation path) -- harness links real SHA-256 + a pure-OCaml RFC-8032 Ed25519 verify **and sign**, checks the frozen digest, RFC 8032 TEST 1, invalid-point / non-canonical-identity / low-order-key rejection **through `signature_valid_impl`**, and a **real signed-digest end-to-end** `signature_valid_impl` positive; retrieval integrity stays explicit. Data-rep repaired in `Orchestration.v` (spec §2.4.1/§2.5 already ahead); `validate_campaign` ordering + fuel unchanged. See `PHASE_1_MANIFEST_AUTHENTICATION.md` |
| `op_ledger_mismatch` | **concrete, standalone AND integrated** (`ManifestLedger.ledger_mismatch_impl digest_eqb parse_manifest_impl`, wired into `ManifestPipeline.pipeline_ops`). `ld_mismatch` walks the parsed `cm_submission_digests` against `map submission_digest ti_submissions` and returns the **least** differing index or the first length-divergence index; `None` iff equal element-wise/ordered/multiplicity-kept. Proved: `ld_mismatch_none_iff`, `ld_mismatch_some_spec` (prefix agreement + genuine divergence at the index), `ledger_mismatch_impl_none_iff` (the `None` equivalence), `ledger_mismatch_impl_some_spec`, `ValidationBinding.validate_campaign_valid_ledger`, `ManifestPipeline.validate_campaign_ledger_agrees` (a **separate** theorem; `validate_campaign_pipeline` keeps its three conclusions). Residual: the decoder passed in (concrete) + retrieval integrity for the manifest and submission list. Harness covers reorder / add / remove / duplicate. See `PHASE_1_MANIFEST_LEDGER.md` |
| `op_manifest_audit_matches` | **concrete, standalone AND integrated** (`ManifestAudit.manifest_audit_matches_impl parse_manifest_impl policy_audit_instance_id_of`, wired into `ManifestPipeline.pipeline_ops`). Decodes with `parse_manifest_impl` and compares `cm_audit_instance_id` with `policy_audit_instance_id_of (ti_policy ti)` by **exact string equality** (`false` on decode failure or any difference incl. case). Proved: `manifest_audit_matches_impl_true_iff` (**full `true` equivalence**, not one-way), `manifest_audit_matches_impl_false_iff`, `ValidationBinding.validate_campaign_valid_audit`, `ManifestPipeline.validate_campaign_audit_agrees` (a **separate** theorem; `validate_campaign_pipeline` keeps its three conclusions) binding the decoded id to a fixed `committed_audit_instance_id` via `committed_policy_audit_id : policy_audit_instance_id_of p_committed = committed_audit_instance_id` + the policy binding. Residual: `policy_audit_instance_id_of` correctness stays an F.3 fact tied to §2.3 load validation **until the policy representation / parser is concrete**. Harness: matching / differing / case-different id + non-decoding manifest. See `PHASE_1_MANIFEST_AUDIT.md` |
| `op_record_identity_mismatch` | **concrete, standalone AND integrated** (`CampaignRecord.record_identity_mismatch_impl parse_record_impl parse_manifest_impl`, wired into `ManifestPipeline.pipeline_ops`). New structured `campaign_record_view` (5 step-8 identity fields) + strict decoder `parse_record_impl` for a **FULL campaign record over the canonical ASCII-wire subset** (8 keys byte-ascending; `completeness` / `recorded_results` / `resource_budget` syntactically skipped by `skip_value`, which enforces canonical integer syntax `0 | -?[1-9][0-9]*` and strictly-ascending duplicate-free keys in every skipped object; raw non-ASCII UTF-8 rejected) -- the wire-level `campaign_record` wrapper is unchanged. Compares, in the **frozen order** `campaign_id`, `audit_instance_id`, `policy_hash`, `context_digests` (all vs the decoded manifest) then `manifest_digest` (vs `commitment_digest mc`); returns `Some "<field>"` at the first inequality, `None` iff both decoders succeed and all five agree. Distinct deterministic decoder-failure sentinels `"!record_undecodable"` / `"!manifest_undecodable"` (`record_sentinels_distinct`). Proved: `record_identity_mismatch_impl_none_iff` (complete `None` equivalence), `_some_<field>` ×5 (preceding fields agree, named field differs), the two `_undecodable_iff`, `ValidationBinding.validate_campaign_valid_record` (standalone), `ManifestPipeline.validate_campaign_record_agrees` (**separate** theorem; `validate_campaign_pipeline` keeps its three conclusions). Bounded to the five identity fields -- the full typed record representation and semantic decoder is `RecordCrosscheck` (`op_record_crosscheck`, r17, promoted). Harness: each field, earliest-of-many, case-only, both decoder failures, complete match, and a **normative full record** end-to-end (payload `completeness`, tagged `recorded_results` entries, populated `resource_budget`; identity-only form rejected; leading-zero / `-0` / duplicate-key / descending-key `resource_budget` rejected). See `PHASE_1_CAMPAIGN_RECORD.md` |
| `op_completeness_wellformed` | **concrete, standalone AND integrated -- reviewer-concurred by source inspection and promoted** (`CompletenessWellformed.op_completeness_wellformed_impl`, wired into `ManifestPipeline.pipeline_ops`, step 9 -- the LAST `validate_campaign` guard; revision 1 HELD; revision 2 HELD (blocker 1 concurred closed, blocker 2 persisted in an unsatisfiable global form); **revision 3 reviewer-concurred**, ZIP sha256 `b4298a2c…f08df8`). A pure structural check on the already-typed `completeness_status` -- no wire decode, unrelated to `Orchestration.valid_completeness_certificate_v0` (the semantic EXACT-branch check, untouched, still dead code in v0). `CompletenessUnknown` / `CompletenessIncomplete` unconditionally well-formed; `CompletenessComplete c` requires `wellformed_scheme (completeness_scheme c)` (**non-empty only**, reviewer-concurred) and `wellformed_body (completeness_body c)` (exactly one value of the **ASCII-wire canonical subset** `CampaignRecord.skip_value` recognises, wholly consumed, reviewer-concurred as v0's scope). An **independent** specification-level relation `CompletenessWellformed.completeness_status_wf` (NOT phrased via this unit's own Booleans) is added; **`op_completeness_wellformed_impl_true_iff`** is now stated against it (the Boolean-only form survives as `_true_iff_bool`), with **`_false_iff`** (`~ completeness_status_wf`) and `_false_spec` (concrete) alongside. `ValidationBinding.validate_campaign_valid_completeness` (standalone, general `ops`); `ManifestPipeline.validate_campaign_completeness_agrees` + `_bool` + `_structured`. **`record_completeness_of` / `record_completeness_load_validated`** bind the checked value to `ti.rec.completeness` itself (revision 1 checked only the separate `ti_completeness` field with no proven connection to the record). Revision 2 stated the binding premise as a blanket `forall ti, ...` Section `Hypothesis` -- UNSATISFIABLE, since two `trusted_inputs` can share `ti_record` while differing in `ti_completeness`; revision 3 makes it a `Definition ... (ti : trusted_inputs) : Prop`, a predicate on ONE input exactly like `ManifestMatching.policy_digest_load_validated`, taken as an explicit premise by **`validate_campaign_completeness_bound_to_record`** + `_structured` (a concrete completeness decoder is the preferred, still-future-work resolution). Residual: the ASCII-wire-subset scope of `wellformed_body` (reviewer-concurred, not yet folded into a governing document) and the F.3 record-binding premise, both explicit and flagged. Harness: `Unknown`/`Incomplete` accepted; well-formed `Complete` certificates accepted; quote/backslash/high-byte/DEL schemes accepted; every remaining failure class rejected; a **Blocker-2 demonstration** -- two records differing only in `completeness` decode to the identical typed view. See `PHASE_1_COMPLETENESS_WELLFORMED.md` |
| `op_record_crosscheck` | **concrete, standalone AND integrated -- reviewer-concurred by source inspection and promoted** (r14 held; r15 partial; r16 held; **r17**, ZIP sha256 `476c32c3…de10de1`). `RecordCrosscheck.record_crosscheck_impl parse_record_full_impl`, wired into `ManifestPipeline.pipeline_ops`; r13 identity representation UNCHANGED. **Data-rep repair to frozen `Orchestration.v`** (VERDICT_SEMANTICS §2/§4.1 already ahead -- no `Orchestration.v` governing-doc change): `finding` `+ finding_offending`; `parsed_candidate` `+ pc_candidate_id`; `stage1_result` `+ s1_candidate_id`/`s1_semantic_digest` (`Some` for every parsed candidate). `Stage1Wrapper` gains an F.3 `candidate_id_of` (correctness = F.3.2 parser residual); `PipelineWiring.wired_stage1` threads it; `ContextResolution.pass_finding` gains the `offending` arg. Promoted r5–r13 theorems re-proved (only `wrapper_reject_not_pending` restated, additively) -- the r17 disposition covers these modified files. **Fully typed `submission_check_result`** (`scr_outcome_view` -- 4 cases, **no `not_run`** -- + `scr_findings : list finding`): `parse_scr_outcome` (unknown reason rejected), `parse_finding` captures `offending` as raw canonical text and enforces the frozen closed stage `check_id` set. **`derive_expected s1 s2` is FILTERED**: a stage-1 `NotRun` slot and a `S1Pending` submission whose stage-2 slot is `NotRun` produce **no** `submission_check_result` (AUDIT_POLICY §2.2.5: mandatory `submission_digest`, no `not_run`); `derive_one_index` / `derive_expected_indices` prove it is an order- and index-preserving projection of the stage-1 slot list. Every derived result has a **mandatory** `exp_digest : digest`. **`scr_agrees : scr_view -> expected_scr -> Prop`** (full field equality) with the two-sided **`scr_matches_expected_true_iff`** (`scr_matches_expected r e = true` iff `scr_agrees r e`). **`crosscheck_impl_nil_iff`** (top level, T26): `crosscheck_impl rf s1 s2 = []` iff `Forall2 scr_agrees (rf_recorded rf) (derive_expected s1 s2)` -- equal length + index order forced; `crosscheck_impl_nil_iff_bool` is the Boolean corollary. `parse_record_full_impl_projects` is the **forward projection only**. `crosscheck_budget_impl` advisory. **Advisory identifier domain**: `record_crosscheck_impl_ids` proves every emitted finding's `check_id` is in the closed 3-element family `{budget_advisory, campaign_record_mismatch, campaign_record_undecodable}`, disjoint from the stage set -- authorised by `PHASE_1_ADVISORY_FINDING_IDS_ERRATUM.md` (reviewer-concurred 2026-09-10, applied to `VERDICT_SEMANTICS.md` §2/§6.5, `AUDIT_POLICY_AND_EVIDENCE.md` §2.2.5, `THREAT_MODEL.md` T26). **Verdict invariance proved** (unchanged): replacing `op_record_crosscheck` by any function leaves the campaign verdict unchanged. Residual: `offending` compared as raw canonical text; `policy_hash`/`schema_version` of `parsed_candidate` not surfaced (B-tier-checked); F.3 decoders passed in. Harness: typed decode incl. offending + check_id rejection; a mutation of every field (incl. isolated `submission_digest` / index); `NotRun` filtering; mutation + `NotRun`-alignment **through `parse_record_full_impl`**; advisory-id closure. See `PHASE_1_RECORD_CROSSCHECK.md` |
| `op_transcript_digest` | **OPEN** |
| artifact-bound `AuditContext` fields | **OPEN** -- `preproc` / `model` / `quantise` / `domainb` / `target` are abstract, not yet bound to the committed model artifact + inference spec. The `resolved_context` type staying **dimension-agnostic** (a string field, not a dependent `AuditContext`) is the reviewer's **decision**, not a gap: single-context is `PipelineWiring.wiring_resolution_consistent` / `ContextResolution.stage1_stage2_use_resolved_context` (theorems). |
| `transcript_stage2_wf` from `parse_transcript` / `capture` | **OPEN** -- assumed as a hypothesis by `adapter_reporting_conformance` |
| digest correctness (`submission_digest` = `digest_bytes_v1` of wire; `semantic_digest_of` = `digest_v1`) | **OPEN** -- wrapper preserves supplied digests; does not prove they represent the bytes |

## Closure-report obligation 3 -- extracted-OCaml build against arbitrary precision

> Complete extracted-OCaml compilation, linking and execution with the required
> arbitrary-precision library.

**OPEN.** Every extraction so far is `Z` / `nat` -> OCaml `int`, explicitly a
test harness with no overflow-safety guarantee (see each `Extract*.v` header).
The exact-integer verifier -- `Z` -> an arbitrary-precision type, compiled,
linked and executed -- is not done. (The verifying environment's `zarith` ships
no `.cmi` files; this remains an environment gap plus unfinished work.)

## Closure-report obligation 4 -- implementation acceptance checks

> Complete the previously specified implementation acceptance checks, including
> capture / replay correspondence, canonical encoding, parser / boundary checks
> and the cross-language agreement battery.

**PARTIAL.**

| check | status |
|---|---|
| parser / boundary (stage 1) | **stage-1 wrapper ordering and binding complete** -- B4 -> B5 -> C1 precedence, dimension well-formedness, `S1Rejected` vs `S1Pending`, and the digest / candidate / index binding, all **proved** (`Stage1`, `Stage1Wrapper`). **Concrete parser conformance remains open**: `lower_parse` (B1a/B6/B1b/B1c/B2/B3) and `parse_literal` (B5 `integer_type` ranges) are external Section parameters, unproven |
| boundary conditions (stage 2) | `adapter_candidate_wf` / `transcript_stage2_wf` formalised; `adapter_candidate_wf` discharged from stage 1 -- **proved** |
| capture / replay correspondence | **OPEN** -- `capture` is not modelled; `replay`'s dependence on `op_stage2_check` is localised (`replay_op_stage2_local`) but no `capture` <-> `replay` theorem |
| canonical encoding | **PARTIAL** -- `CanonicalV1.render_manifest` (`canonicalise_v1 ∘ to_cv` for the campaign-manifest schema, `render_manifest_frozen_vector` = the §2.2.5 payload byte-for-byte) and `digest_v1` / `campaign_manifest_digest` are concrete; the general `canonical_value` tree + the remaining `to_cv` rows are open |
| cross-language agreement battery | **OPEN** -- OCaml `orchestration.ml` mirror compiles but no Rocq <-> OCaml equivalence; the `Stage*` extractions have OCaml harness tests but no cross-language correspondence proof |

## O1/O2/O3 functions + shared-`C` wiring -- reviewer source review PASSED

`ContextResolution.v` + `PipelineWiring.v` (`PHASE_1_CONTEXT_RESOLUTION.md`),
`Qed`, axiom-free. The reviewer concurred that **the bounded shared-`C`
construction and its invariant / index / redundancy results pass source
inspection**, with the explicit qualification that this **does not establish
full artifact-bound context resolution**.

Established: O1/O2/O3 as concrete functions with parameter-level bindings
(`preflight_ok_binds`, `preflight_ok_artifact_bound`, `preflight_fail_reason`,
`eval_o3_ok_binds`); both stage checkers fixed to one committed `C`
(`PipelineWiring.wired_ops`); `wiring_resolution_consistent`; the two
`primitive_ops` obligations for `wired_ops`; the pending-list invariant and
C-recheck redundancy for `wired_ops`.

**Artifact binding, this revision:** the descriptor is now structured and O1/O2
check the loaded byte-digests against the **descriptor parsed from
`loaded_descriptor lc`**; `preflight_ok_artifact_bound` chains that to the
authenticated commitment via the explicit `commits` relation and to `C` via
`byte_digest_consistent … committed_descriptor -> realises_C` (`realises_C` is
now a *consequence* of digest-consistency, not opaque). The O3 probe is derived
from `loaded_inference_bytes lc` (digest-checked by O2) via `probe_of_spec`.

**Campaign-validation binding (`ValidationBinding.v`, `PHASE_1_VALIDATION_BINDING.md`):**
the contracts are **scoped to one `ops`** (`Variable ops` fixed before the
`Hypothesis` lines, each `forall ti …` not `forall ops …`) -- the earlier
`forall ops` form was unsatisfiable. `validate_campaign_valid_guards` is proved
for any `ops` first. `validate_campaign ops ti = ValidCampaign ac l0` ⇒ (modulo
two explicit F.3 contracts `policy_match_sound` / `context_match_sound` on that
`ops`'s manifest-matching primitives) `ti_policy ti = p_committed` and
`commits (authenticated_commitment ac) committed_descriptor`
(`validate_campaign_binds`). The dependency is **split and `Check`-verified**:
`validate_campaign_binds_policy` and both
`assess_validated_{live,offline}_uses_committed_policy` proofs use
`policy_match_sound` **only** (their proof terms mention no `context_match_sound`,
`commits`, or `committed_descriptor`); `validate_campaign_binds_descriptor` uses
`context_match_sound`. For a validated campaign `assess_validated`'s `replay`
call runs with `p = p_committed`, so `op_eval_o3` is invoked with `p_committed`
-- **the "replay path supplies `p_committed`" obligation is discharged modulo
`policy_match_sound` only**; the descriptor↔commitment link is a consequence
modulo `context_match_sound`.

**Still F.3-external:**
- ~~`policy_match_sound` / `context_match_sound` themselves~~ -- for the concrete
  matchers (`ManifestMatching.v`, next section) the abstract contracts are **not
  instantiated**; they are **replaced/bypassed** -- the capstone
  `validate_campaign_concrete_binds` and the concrete replay corollaries prove
  the same conclusions directly, modulo the narrower residuals listed there;
- `parse_descriptor` / `probe_of_spec` wire-decoding correctness
  (`parse_manifest` is now the concrete `ManifestAuthentication.parse_manifest_impl`);
- the *loaded* descriptor being the committed one
  (`parse_descriptor (loaded_descriptor lc) = Some committed_descriptor`
  -- `load_context` / retrieval store);
- digest-function truthfulness; the kernel-`Policy` ↔ policy-string link;
  a definition for `realises_C`;
- `transcript_stage2_wf` (transcript parser / capture);
- the remaining validation-tier `primitive_ops` (`op_transcript_digest`)
  -- `op_parse_commitment` / `op_signer_authorised` / `op_signature_valid` are
  now concrete (`ManifestAuthentication`); the F.3 residuals there are
  `sha256_hex` / `ed25519_verify` / `ed25519_pubkey_valid` and retrieval
  integrity. `op_ledger_mismatch` is concrete (`ManifestLedger`), residual =
  the decoder passed in + retrieval integrity. `op_manifest_audit_matches` is
  concrete (`ManifestAudit`), residual = `policy_audit_instance_id_of`
  correctness (tied to §2.3 load validation until the policy parser is concrete).
  `op_record_identity_mismatch` is concrete (`CampaignRecord`, five step-8
  identity fields), residual = the two decoders passed in + retrieval integrity;
  `op_record_crosscheck` is concrete (`RecordCrosscheck`), advisory-only
  (verdict-invariance proved).

Reviewer decision on the earlier flag: **keep the dimension-agnostic
`resolved_context`**; no dependent `AuditContext` field, no separate
`replay`-level `rc`-threading theorem.

## Concrete manifest matchers -- `ManifestMatching.v` (`PHASE_1_MANIFEST_MATCHING.md`)

`Qed`, axiom-free. `manifest_policy_matches_impl` / `manifest_context_matches_impl`
over a parsed `campaign_manifest_view`. Revised same day after three reviewer
defects (`PHASE_1_MANIFEST_MATCHING.md` documents each): (1) digest truthfulness
is now `policy_digest_load_validated ti` on ONE input, not the inconsistent
`forall ti` form; (2) the audit's commitment / manifest / view are FIXED section
objects with four hypotheses about them only, and `validated_{commitment,manifest}_is_audit`
connect a successful validation to them (was an unscoped `forall mc M`); (3) the
`discharges_*` lemmas (contract-shaped modulo extra premises) are removed in
favour of `assess_validated_{live,offline}_concrete` -- the SAME statements as
`ValidationBinding.assess_validated_*_uses_committed_policy`, proved from
`validate_campaign_concrete_binds_policy` (the policy-only capstone) with no
opaque contract and no context-side dependency. Full capstone
`validate_campaign_concrete_binds`: `policy_digest_load_validated ti` +
`validate_campaign` success + these matchers ⇒ `ti_policy ti = p_committed` ∧
`commits_impl (authenticated_commitment ac) committed_descriptor`. `commits`
given concrete `commits_impl`. `manifest_matching_core_hyps_consistent` proves
the **seven core non-`ops`** facts mutually consistent -- it does not exhibit an
`ops`, the four `ops`-hypotheses, or a `validate_campaign` instance, so it is a
consistency result, not full non-vacuous satisfiability. `test_manifest_matching`
exercises the extracted matchers.

`make check` exits 0: `coqchk` covers 19 modules;
across `make check`, **133** `Print Assumptions` "Closed under the global
context"; seven `make test` harnesses PASS. The validation-tier layer: `ManifestAuthentication` (2.4.1 auth), `ManifestLedger` (`op_ledger_mismatch`), `ManifestAudit` (`op_manifest_audit_matches`), `CampaignRecord` (`op_record_identity_mismatch`), `RecordCrosscheck` (`op_record_crosscheck` -- concrete + `crosscheck_impl_nil_iff` over `Forall2 scr_agrees` + filtered `derive_expected` + advisory-id closure + verdict-invariant; reviewer-concurred + promoted, r17), `CompletenessWellformed` (`op_completeness_wellformed` -- concrete + positive/negative structural characterisations + per-input record-binding premise; reviewer-concurred + promoted, r3) -- see the per-unit docs; coqchk covers 19 modules.

## Next

The remaining validation-tier `primitive_ops` (`op_transcript_digest`);
`parse_descriptor` / `probe_of_spec` as concrete canonical decoders; a
maintained Ed25519; `transcript_stage2_wf` from a modelled `parse_transcript` /
`capture`; the arbitrary-precision extraction; capture/replay correspondence;
canonical encoding; cross-language battery.

**Phase 1 closure is not appropriate now** and is not proposed.
