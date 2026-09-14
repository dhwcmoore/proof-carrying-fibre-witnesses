# Phase 0 executable skeleton

The normative prose in this archive is preserved byte-for-byte from Revision 14.
The new `implementation/` directory is a Phase 1 entry skeleton. It exists to
replace further hand-review of orchestration pseudocode with type-checking and
evaluation.

The Rocq source defines concrete algebraic data types and real, structurally
recursive total functions for:

- `validate_campaign`;
- `replay`;
- `decide`;
- `assess_validated`.

Primitive parsing, cryptography, hashing, stage checks and certificate assembly
are represented by the typed `primitive_ops` interface. This makes their trust
boundary explicit without pretending that Phase 0 prose implements them.

The proof statements are present and deliberately use `Admitted`. They are proof
obligations, not claims of completion. The OCaml source is an independently
written executable structural mirror for early tests. The authoritative Phase 1
OCaml is to be regenerated from `rocq/ExtractOrchestration.v` after the admitted
proofs and primitive implementations are discharged.

No Phase 0 closure report is issued by this archive.

## Build verification addendum

This skeleton was subsequently built with `coqc`/`coqchk` 8.18.0 and `ocamlc`
4.14.1. As delivered it did **not** compile: four source defects (a Coq scope
shadowing bug, two `List`/`String` naming collisions, and two OCaml record
field-label collisions) plus one `Makefile` include-path omission. All five are
fixed in this tree; see `implementation/README.md` § Build for the exact
locations and reasoning. After the fixes: `rocq/Orchestration.v` and
`rocq/ExtractOrchestration.v` compile clean; `coqchk` passes; `Print Assumptions`
on each of the six named theorems shows exactly that theorem and nothing else,
confirming no unintended axioms; the hand-written OCaml skeleton compiles clean.
Linking the Coq-*extracted* OCaml against `zarith` was not verified — the
verifying environment's `zarith` install ships no `.cmi` interface files.
(Update, 2026-09-13: this has since been verified in the build environment
used for `PHASE_1_ARBITRARY_PRECISION_EXTRACTION.md` — that environment's
`zarith` install, the one the Makefile's own `OCAML_LIB`/`ZARITH` variables
already resolve to, does ship complete `.cmi` files, and both `ExtractOrchestration.v`
and `ExtractFibreWitnessKernel.v` now compile, link and execute against it.
This is an observation about that specific environment, not a general claim;
see that document for what remains unconverted.)

## REP1 repair + context-bundle addendum

A later review found `REP1_not_run_has_no_witness` **false as stated** (it
quantified over an arbitrary `list stage2_slot`), which made its `Admitted`
render `PCFW.Orchestration` inconsistent as an imported theory. Five bounded
repairs were applied to `implementation/` as pre-closure-candidate work — no
change to the frozen Revision 14 normative set:

1. `REP1_not_run_has_no_witness` restated over `stage2_slots_wf` slot lists and
   proved (`Qed`); `replay_stage2_wf` discharges that predicate for every
   `replay` output; `REP1_replay_not_run_has_no_witness` is the corollary.
2. `run_stage1` now assigns each pending index (`with_pending_index i`);
   `run_stage1_pending_nodup` proves distinctness.
3. `stage2_witness_index_contract` added as a `primitive_ops` obligation for
   `op_stage2_check` (Phase 1 must discharge).
4. `Stage1Complete ∧ pending ≠ [] ∧ cb = CtxNotNeeded` reported via new nullary
   `campaign_obstruction` `InconsistentContextBundle` + new nullary
   `context_state` `ContextBundleInconsistent` — OBSTRUCTED, all pending stage-2
   slots `NotRun`, **no finding of any kind**, obligation
   `reconstruct_or_supply_context_bundle`. `ctx_reason` is left unchanged (it is
   shared by `CtxUnavailable`/`PreflightFail`/O3), so those cannot carry the new
   case — `CtxUnavailable InconsistentContextBundle` is a type error. Distinct
   from terminal stage-1 fuel exhaustion (`Stage1Stopped` branch, unchanged).
   Proposed frozen constructor-set / encoding amendment:
   `implementation/CONTEXT_BUNDLE_AMENDMENT.md`.
5. OCaml mirror updated to match; `make assumptions` and `make test` added.

## Phase 0 closed at Revision 15; Phase 1 orchestration proofs discharged

Phase 0 was closed by the designated reviewer at Revision 15 (see
`PHASE_0_CLOSURE_REPORT.md`). Phase 1 then discharged the five orchestration
proof obligations that Phase 0 had left `Admitted` — see
`PHASE_1_ORCHESTRATION_PROOFS.md`.

`make check` now exits 0 with **no `Admitted` / `admit` / `Axiom` / `Parameter`
/ `Hypothesis` in `rocq/Orchestration.v`**. `coqchk` passes both modules.
`make assumptions` reports all eight targets — `REP1_not_run_has_no_witness`,
`REP1_replay_not_run_has_no_witness`, `replay_stage2_wf`, `T2_sound`,
`T2_complete`, `stage1_over_is_terminal`, `exact_unreachable_v0`,
`validation_fuel_obstructed_unreachable_when_sufficient` — as
`Closed under the global context`. `make test` (`ocaml/test_context_bundle.ml`)
prints `PASS`. Kernel `T1` / `A1` unchanged, still
`Closed under the global context`.

`T2_sound` / `T2_complete` are the witness-selection control-flow theorems as
stated (they relate `assess_validated`'s `INADMISSIBLE` verdict to membership in
`valid_witnesses (replay_stage2 (replay …))`); they are **not** a proof of
execution faithfulness. `REP1` still carries `stage2_witness_index_contract` as
an explicit premise for a concrete `op_stage2_check` to discharge in Phase 1.

### Phase 1 unit: concrete stage-2 checker + kernel connection

`implementation/rocq/Stage2.v` + `Stage2Adapter.v` (both `Qed`, axiom-free) --
see `PHASE_1_STAGE2_KERNEL_CONNECTION.md`. `stage2_check` implements the frozen
**O6a -> O6b -> O6c -> O6d -> O4 -> O5 -> C4** order over the kernel carriers
(inputs carried on every outcome so O6b precedes O6c; O6d is the per-candidate
fuel bound); `stage2_valid_checked_witness` turns a `S2Valid` result (plus the
stage-1 C1/C2/C3/C5 facts) into `FibreWitnessKernel.CheckedWitness`;
`stage2_valid_observation_binding` gives `ObservationBinding` conditionally on
the F.3 transcript-faithfulness assumption. `adapter_satisfies_index_contract`
discharges the `stage2_witness_index_contract` premise that the repaired `REP1`
carries. Boundary contracts are formalised (`adapter_candidate_wf`,
`transcript_stage2_wf`, `event_dims_ok`) and proved to exclude the adapter's
parsing-failure branches (`adapter_candidate_wf_parses`, `slot_at_wf_none_iff`,
`stage2_check_missing_char`); `adapter_reporting_conformance` scopes the
truthful-reporting claim to them. Establishing those conditions from the
concrete `stage1_check` / `parse_transcript` / `capture` is an outstanding
integration obligation. `ExtractStage2.v` + `ocaml/test_stage2.ml` (`make test`) exercise the
extracted checker/adapter on valid / not-a-witness / every obstruction /
O6b<O6c order / O6d fuel boundary / malformed candidate+event lengths -- **the
`Z -> int` extraction is a test harness only, not the exact-integer verifier**.

`verifier_config` gains `max_fuel_per_candidate : nat` (the frozen
`per_candidate_limits` field from AUDIT_POLICY 2.2.5, previously unmodelled);
additive, the five orchestration proofs and OCaml mirror rebuilt clean.

Reviewer concurred with promotion of this bounded, conditional unit after
verifying archive integrity and source (two reporting corrections applied:
`lookup_unique = None` is "no unique event -- absent or duplicated"; the
boundary predicates condition the conformance theorem, they are not
runtime-enforced). Now promoted into `implementation/`. Compilation evidence is
from the implementation machine; the reviewer's concurrence is by source
inspection.

### Phase 1 unit: concrete stage-1 semantic checker

`implementation/rocq/Stage1.v` (`Qed`, axiom-free) -- see
`PHASE_1_STAGE1_CONNECTION.md`. `stage1_semantic_check` does B4 + C1/C2/C3/C5 in
the frozen order. `stage1_pending_identity`: the returned `ps` is exactly
`mkPendingSubmission idx sd cd c []` (candidate, index and both supplied digests
preserved). `stage1_pending_candidate_wf` discharges the adapter's
`adapter_candidate_wf` hypothesis; `stage1_pending_evidence` supplies
`pending_candidate ps = c` plus `Stage2.Stage1Evidence C x y` for the vectors of
that same `ps`. `stage1_reject_char` (a `match` on the returned reason, no
exclusivity question) and `stage1_dim_reject` establish the C1<C2<C3<C5 and
B4<C1 precedence. `ocaml/test_stage1.ml` (`make test`) exercises them. Reviewer passed source
review of this unit (2 doc corrections applied); promoted.

### Phase 1 unit: evidence preservation through orchestration

`implementation/rocq/Stage1Invariant.v` (`Qed`, axiom-free) -- see
`PHASE_1_ORCHESTRATION_INVARIANT.md`. `pending_invariant C ps` (a `Prop` over
the existing `pending_submission`, erased at extraction) is established by
`stage1_pending_invariant`, propagated to every pending submission `run_stage1`
produces by `run_stage1_all_pending_invariant` under the F.3-pending
*pending-output soundness contract* `op_stage1_sound` (`op_stage1_check`'s every
`S1Pending` verdict satisfies `pending_invariant` -- not a comparison with
`stage1_semantic_check`). `replay_op_stage2_local` proves `replay`'s output
depends on `op_stage2_check` only through its behaviour on invariant-satisfying
pending submissions (swap `op_stage2_check` for one that agrees on them, other
14 `primitive_ops` fields fixed, `replay` unchanged). `adapter_c_recheck_redundant`
shows the adapter's C-recheck falls through under the invariant. No executable
change. Reviewer concurred with promotion (source review, two review rounds:
`replay_pending_invariant` -> `replay_op_stage2_local`; `op_stage1_sound`
reworded). Promoted.

### Phase 1 unit: F.3 stage-1 parser wrapper; `op_stage1_sound` discharged

`implementation/rocq/Stage1Wrapper.v` (`Qed`, axiom-free) -- see
`PHASE_1_STAGE1_WRAPPER.md`. `op_stage1_wrapper` wire-parses a raw
`candidate_submission` (`lower_parse` for B1a/B6/B1b/B1c/B2/B3, then **B4 before
B5**), then runs `stage1_semantic_check C` on success. `wire_parse_B4_before_B5`
proves the dimension check dominates the literal check; `wrapper_reject_not_pending`
(rejection, never `S1Pending`); `wrapper_pending_binds` (all five
`pending_submission` fields bound to the raw submission / parsed candidate);
`wrapper_fields` (index / raw digest / `[]` preserved); **`wrapper_op_stage1_sound`**
discharges `Stage1Invariant.op_stage1_sound` for any wrapper-backed
`op_stage1_check`. `ocaml/test_stage1_wrapper.ml` (`make test`) exercises B4<B5,
B5<C1, and the binding. Across `make check`, **32** `Print Assumptions` commands
print "Closed under the global context" -- 30 from `make assumptions`, plus the
2 kernel ones from the `rocq` target; `coqchk` covers seven modules incl.
`PCFW.Stage1Wrapper`. Still F.3-external: digest truthfulness, `lower_parse` /
`parse_literal` correctness. Reviewer passed source review of this unit (one
reporting correction applied). Promoted.

### Phase 1 unit: O1/O2/O3 bound to descriptor + inference spec; shared-`C` wiring

`implementation/rocq/ContextResolution.v` + `PipelineWiring.v` (`Qed`,
axiom-free) -- see `PHASE_1_CONTEXT_RESOLUTION.md`. `preflight_check` parses
`loaded_descriptor lc` into a structured `descriptor` and checks the loaded
byte-digests against its fields (`preflight_ok_binds` -- changing the descriptor
changes acceptance); `preflight_ok_artifact_bound` chains a `PreflightOk` on the
committed descriptor to the authenticated commitment (explicit `commits`
relation) and to `C` (`realises_C`, now a *consequence* of digest-consistency).
`eval_o3_check` derives the probe from `loaded_inference_bytes lc` (digest-checked
by O2) via `probe_of_spec`; `eval_o3_ok_binds` exposes that. `PipelineWiring.wired_ops`
closes `op_stage1_check` / `op_preflight` / `op_eval_o3` / `op_stage2_check` over
one committed `C`; `wiring_resolution_consistent`, `wired_ops_op_stage1_sound`,
`wired_ops_stage2_index_contract`, `wired_run_stage1_pending_invariant`,
`wired_c_recheck_redundant`. **Still F.3-external**: `parse_descriptor` /
`probe_of_spec` correctness; the `commits` manifest-auth-chain hypothesis; the
loaded descriptor being the committed one; digest-fn truthfulness.
`ocaml/test_context_resolution.ml` (`make test`).

### Phase 1 unit: `validate_campaign` bound to committed policy + descriptor

`implementation/rocq/ValidationBinding.v` (`Qed`, axiom-free) -- see
`PHASE_1_VALIDATION_BINDING.md`. The F.3 contracts are **scoped to one `ops`**
(`Variable ops` fixed first; each `forall ti …`, not `forall ops …`);
`validate_campaign_valid_guards` is proved for any `ops` beforehand.
`validate_campaign_binds`: `validate_campaign ops ti = ValidCampaign ac l0` ⇒
(modulo `policy_match_sound` / `context_match_sound` on that `ops`) `ti_policy ti
= p_committed` and `commits (authenticated_commitment ac) committed_descriptor`.
The dependency is split and `Check`-verified: `validate_campaign_binds_policy`
and both `assess_validated_{live,offline}_uses_committed_policy` proofs use
`policy_match_sound` **only** -- discharging the "replay path supplies
`p_committed`" obligation modulo `policy_match_sound` alone;
`validate_campaign_binds_descriptor` uses `context_match_sound`.

### Phase 1 unit: concrete manifest matchers; `ValidationBinding` contracts replaced

`implementation/rocq/ManifestMatching.v` (`Qed`, axiom-free) -- see
`PHASE_1_MANIFEST_MATCHING.md`. `manifest_policy_matches_impl` /
`manifest_context_matches_impl` are concrete boolean checks over a parsed
`campaign_manifest_view` (`digest_eqb` on `cm_policy_hash` vs `ti_policy_digest`;
`descriptor_eqb` on `cm_context_digests` vs the policy's embedded context
digests). Revised same day after three reviewer defects: digest truthfulness is
`policy_digest_load_validated ti` on ONE input (not the inconsistent `forall ti`);
the audit's commitment / manifest / view are FIXED section objects with
`validated_{commitment,manifest}_is_audit` connecting a successful validation to
them; the `discharges_*` lemmas replaced by `assess_validated_{live,offline}_concrete`
-- the SAME statements as `ValidationBinding.assess_validated_*_uses_committed_policy`,
proved from `validate_campaign_concrete_binds_policy` (the **policy-only** capstone,
no context-side dependency) with no opaque contract. Full capstone
`validate_campaign_concrete_binds`: `policy_digest_load_validated ti` +
`validate_campaign` success + these matchers ⇒ `ti_policy ti = p_committed` ∧
`commits_impl (authenticated_commitment ac) committed_descriptor`. `commits`
given a concrete `commits_impl`. `manifest_matching_core_hyps_consistent` proves
the **seven core non-`ops`** facts mutually consistent -- not the `ops`
hypotheses or a `validate_campaign` instance, so a consistency result, not full
satisfiability.
`manifest_matching_core_hyps_consistent`: see `PHASE_1_MANIFEST_MATCHING.md`.

### Phase 1 unit: concrete authenticated-manifest validation (AUDIT_POLICY 2.4.1)

`implementation/rocq/CanonicalV1.v` + `ManifestAuthentication.v` +
`ManifestPipeline.v` (all `Qed`, axiom-free) -- see
`PHASE_1_MANIFEST_AUTHENTICATION.md`. Makes `op_parse_commitment` /
`op_signer_authorised` / `op_signature_valid` concrete (`parse_commitment_impl`
-- 64/128 lowercase-hex + hex-decode; `signer_authorised_impl`;
`signature_valid_impl` -- recompute `campaign_manifest_digest` =
`SHA256_hex(tag ++ 0x1F ++ canonicalise_v1(to_cv M))`, trust-anchor key lookup,
`ed25519_verify k mc.signature (utf8 mc.digest)`). `parse_manifest_impl` is a
**schema-conforming** decoder (UTF-8 gate; §2.2.2 escape decoding + raw-control
rejection; 64-lowercase-hex digest fields; trailing-comma rejection) with a
**round-trip theorem** `parse_manifest_impl_roundtrip` under
`manifest_roundtrip_wf` (64-lowercase-hex digest fields; identifier bytes all
ASCII 0x20..0x7E except `"` and `\`; canonical key order supplied by
`render_manifest`, not by `manifest_roundtrip_wf`), plus `vm_compute` vectors
(schema-valid round-trip; the §2.2.5 short-digest frozen vector **rejected**). The manifest type is unified:
`CanonicalV1.campaign_manifest_view` is the shared validation type, also consumed
by `ManifestMatching`. `ManifestPipeline.validate_campaign_pipeline`: `pipeline_ops`
= auth impls + `manifest_{policy,context}_matches_impl … parse_manifest_impl`;
one `validate_campaign` success ⇒ `manifest_authenticated_by_impl … (ti_config ti)
…` **and** `ti_policy ti = p_committed` **and** `pipeline_commits (ti_config ti)
(authenticated_commitment ac) committed_descriptor` (manifest→descriptor, in the
shared `context_descriptor` type consumed by O1/O2/O3), with no opaque
`parse_manifest`. `parse_manifest_impl_wf` proves any accepted manifest is
`CanonicalV1.manifest_wellformed`; the decoder covers the canonical ASCII-wire
subset (explicit input requirement).
`render_manifest_frozen_vector` is a `vm_compute` check against the AUDIT_POLICY
2.2.5 payload string.
**Data representation repaired in the frozen `Orchestration.v`** to match the
spec (§2.4.1 wire type, §2.5 `trust_anchor`): `manifest_commitment` gains
`commitment_signature`; the wire becomes `{cw_digest;cw_signer;cw_signature}`;
`verifier_config` gains `config_trust_anchor`; `op_signer_authorised` /
`op_signature_valid` gain a `verifier_config` argument;
`validate_campaign` threads `ti_config ti`. First-failure ordering and per-phase
fuel charging unchanged; `validation_fuel_obstructed_unreachable_when_sufficient`
and `validate_campaign_valid_guards` re-proved. No governing-document change.
**F.3**: `sha256_hex` / `ed25519_verify` / `ed25519_pubkey_valid` are named
components -- NOT proved; `ed25519_pubkey_valid` is now run by `signature_valid_impl`
on the validation path. `ocaml/test_manifest_authentication.ml` links a real
SHA-256 (`sha` library) and a pure-OCaml RFC 8032 Ed25519 verify **and sign**,
and checks: the frozen digest; RFC 8032 TEST 1; invalid-point /
non-canonical-identity (`x=0 ∧ x_0=1`) / low-order trust-anchor-key rejection
**through `signature_valid_impl`**; and a **real signed-digest end-to-end**
`signature_valid_impl` positive (sign `utf8(campaign_manifest_digest)`, then
verify). RFC 8032 §6 (its illustrative code is not for production) applies -- a
maintained Ed25519 would replace this F.3 test component in a production build.
Retrieval integrity stays an explicit F.3 premise.

**`op_ledger_mismatch` concrete** (`ManifestLedger.v`, `Qed`, axiom-free --
`PHASE_1_MANIFEST_LEDGER.md`): `ld_mismatch` compares the parsed
`cm_submission_digests` element-wise against `map submission_digest
ti_submissions` and returns the least differing index or the first
length-divergence index; `ledger_mismatch_impl_none_iff` is the `None`
equivalence. Wired into `ManifestPipeline.pipeline_ops`;
`validate_campaign_ledger_agrees` is a separate theorem (the three-conclusion
`validate_campaign_pipeline` is unchanged). Harness covers reorder / add /
remove / duplicate.

**`op_manifest_audit_matches` concrete** (`ManifestAudit.v`, `Qed`, axiom-free --
`PHASE_1_MANIFEST_AUDIT.md`): VERDICT_SEMANTICS step 5 --
`manifest_audit_matches_impl` decodes with `parse_manifest_impl` and compares
`cm_audit_instance_id` with `policy_audit_instance_id_of (ti_policy ti)` by exact
string equality (`false` on decode failure or any difference incl. case).
`manifest_audit_matches_impl_true_iff` is the full `true` equivalence (not one-way).
Wired into `pipeline_ops`; `validate_campaign_audit_agrees` a separate theorem
binding the decoded id to a fixed `committed_audit_instance_id`
(`committed_policy_audit_id : policy_audit_instance_id_of p_committed =
committed_audit_instance_id` + the policy binding); `validate_campaign_pipeline`
unchanged. Residual: `policy_audit_instance_id_of` correctness stays F.3, tied to
§2.3 load validation until the policy parser is concrete. Harness: matching /
differing / case-different id + non-decoding manifest.

**`op_record_identity_mismatch` concrete** (`CampaignRecord.v`, `Qed`, axiom-free --
`PHASE_1_CAMPAIGN_RECORD.md`): VERDICT_SEMANTICS step 8 -- a structured
`campaign_record_view` (five identity fields) + strict decoder `parse_record_impl`
for a **FULL campaign record over the canonical ASCII-wire subset** (8 keys
byte-ascending; `completeness` / `recorded_results` / `resource_budget` skipped by
`skip_value`, which enforces canonical integer syntax and strictly-ascending
duplicate-free keys in every skipped object; raw non-ASCII UTF-8 rejected; the
wire-level `campaign_record` wrapper unchanged). `record_identity_mismatch_impl`
compares, in the frozen order `campaign_id`, `audit_instance_id`, `policy_hash`,
`context_digests` (vs the decoded manifest) then `manifest_digest` (vs
`commitment_digest mc`); `Some "<field>"` at the first inequality, `None` iff both
decoders succeed and all five agree (`record_identity_mismatch_impl_none_iff`).
Distinct decoder-failure sentinels `"!record_undecodable"` / `"!manifest_undecodable"`.
Per-field `_some_<field>` lemmas (preceding fields agree, named field differs).
Standalone `validate_campaign_valid_record`; wired into `pipeline_ops`; separate
`validate_campaign_record_agrees`; `validate_campaign_pipeline` unchanged. Bounded to
the five identity fields.  `op_record_crosscheck` is now concrete
(`RecordCrosscheck.v` -- **reviewer-concurred by source inspection and promoted**
(r14 held, r15 partial, r16 held, **r17** -- ZIP sha256 `476c32c3…de10de1`): a data-rep repair to frozen
`Orchestration.v` (`finding` `+offending`; `parsed_candidate` `+candidate_id`;
`stage1_result` `+candidate_id`/`+semantic_digest` -- spec-conformant), a fully
typed `submission_check_result` (`scr_outcome_view` has **no `not_run`** case),
a propositional `scr_agrees` relation with the two-sided
`scr_matches_expected_true_iff`, and the top-level **`crosscheck_impl_nil_iff`** --
`crosscheck_impl rf s1 s2 = []` iff `Forall2 scr_agrees (rf_recorded rf)
(derive_expected s1 s2)` (T26; equal length + index order forced).
`derive_expected` is **filtered**: a stage-1 `NotRun` slot and a pending +
stage-2-`NotRun` slot produce no `submission_check_result` (AUDIT_POLICY §2.2.5),
proved an order/index-preserving projection (`derive_expected_indices`); every
derived result has a mandatory digest. Advisory `record_findings` identifiers
are a closed 3-element family disjoint from the stage `check_id` set
(`record_crosscheck_impl_ids`), authorised by
`PHASE_1_ADVISORY_FINDING_IDS_ERRATUM.md` (reviewer-concurred 2026-09-10, applied
to `VERDICT_SEMANTICS.md` §2/§6.5, `AUDIT_POLICY_AND_EVIDENCE.md` §2.2.5,
`THREAT_MODEL.md` T26). Plus the unchanged **verdict-invariance theorem**;
`PHASE_1_RECORD_CROSSCHECK.md`. `parse_record_full_impl_projects` is the forward
projection ONLY. The r17 disposition covers the modified `Orchestration.v` /
`Stage1Wrapper.v` / `PipelineWiring.v` / `ContextResolution.v`.

**Promotion (2026-09-10).** The cumulative **r5–r13 validation block**
(`ManifestAuthentication` / `ManifestMatching` / `ManifestLedger` / `ManifestAudit`
/ `CampaignRecord` + the `ManifestPipeline` integration) is **reviewer-concurred
by source inspection and promoted** (reviewer disposition on r13; reviewed r13
bytes, ZIP sha256 `7691bc1d05d1fb85648da9126372476589acd9971b2decc997c37dd424335419`).
Not a Phase 1 closure.

**`op_completeness_wellformed` (2026-09-13, reviewer-concurred by source
inspection and promoted; revision 1 HELD; revision 2 HELD -- blocker 1
concurred closed, blocker 2 persisted in an unsatisfiable global form;
**revision 3 reviewer-concurred**, ZIP sha256
`b4298a2c4f0bdecd7d601a71830bd2e1ecbf1d8cba567f85168f9ade7df3cae3`).**
`implementation/rocq/CompletenessWellformed.v` (new, `Qed`, axiom-free) makes
`op_completeness_wellformed` concrete: VERDICT_SEMANTICS §5 step 9 (the LAST
`validate_campaign` guard) -- a pure structural well-formedness check on the
already-typed `completeness_status` (no wire decode). Revision 1 was HELD on
two grounds: (1) it reused `ManifestAuthentication.printable_ascii_id` -- a
round-trip-THEOREM predicate, never a decoder acceptance gate -- for
`wellformed_scheme`, wrongly rejecting legitimate decoded strings (a quote, a
backslash, a raw high byte); FIXED in revision 2, reviewer-concurred:
`wellformed_scheme` now requires only non-emptiness, and `wellformed_body`'s
scope to the ASCII-wire canonical subset (via `CampaignRecord.skip_value`) is
stated honestly, reviewer-concurred as v0's scope (the alternative, a full
UTF-8-tolerant canonical-value recognizer, is a separate, larger decoder
unit); an INDEPENDENT specification-level relation `CompletenessWellformed.
completeness_status_wf` is added, with `op_completeness_wellformed_impl_true_iff`
stated against it (the Boolean-only form kept as `_true_iff_bool`). (2) the
checked value (`ti_completeness ti`) had no proven connection to
`ti.rec.completeness`, the value the governing step actually reads. Revision
2's fix re-introduced this as an UNSATISFIABLE global Section `Hypothesis`
(`forall ti, record_completeness_of (ti_record ti) = ti_completeness ti` --
two `trusted_inputs` can share `ti_record` while differing in
`ti_completeness`, forcing e.g. `CompletenessUnknown = CompletenessIncomplete`;
the same defect class as the earlier `ManifestMatching.
ti_policy_digest_truthful` inconsistency). FIXED in revision 3:
`record_completeness_load_validated` is now a `Definition ... (ti :
trusted_inputs) : Prop`, a predicate on ONE input exactly like
`ManifestMatching.policy_digest_load_validated`, and
`validate_campaign_completeness_bound_to_record` / `_structured` take it as an
explicit per-input premise (a concrete completeness decoder remains preferred
future work). `ValidationBinding.validate_campaign_valid_completeness`
(standalone) + `ManifestPipeline.validate_campaign_completeness_agrees` /
`_bool` / `_structured` / `_bound_to_record` / `_bound_to_record_structured`
(separate theorems, `validate_campaign_pipeline` keeps its three conclusions).
Entirely UNRELATED to `Orchestration.valid_completeness_certificate_v0` (the
semantic EXACT-branch check, untouched, still dead code in v0);
`op_transcript_digest` untouched at the time and
was still OPEN. See `PHASE_1_COMPLETENESS_WELLFORMED.md`. **Reviewer-concurred
and promoted; not a Phase 1 closure.**

**`op_transcript_digest` (2026-09-14, reviewer-concurred by source inspection
and promoted; revision 3 -- ZIP sha256
`8b6e3b01533c1f8cfa864a05a36383e2e814ff7b78e7ef42515b24818e5b60ad`).** The
final `primitive_ops` member. `implementation/rocq/TranscriptDigest.v` (new,
`Qed`, axiom-free) -- an interface-and-evidence-binding unit, NOT a
cryptographic implementation: `op_transcript_digest` REMAINS a primitive
hook; its normative target `digest_v1("pcfw.exec_transcript.v1", to_cv(tr))`
is an abstract Section `Variable transcript_digest_v1` (F.3). Proves ordinary
Gallina determinism (`op_transcript_digest_deterministic`) -- explicitly NOT
collision resistance; different transcripts are NOT required to produce
different digests. `set_transcript_digest` replaces only this field
(`set_transcript_digest_field` + `_preserves_others`, all 14 other fields).
Non-interference: `validate_campaign_indep_of_transcript_digest`,
`replay_indep_of_transcript_digest` (the FULL `replay_result`, strictly
stronger than `RecordCrosscheck.set_crosscheck`'s field-wise independence --
this field affects nothing inside `replay`, not even `record_findings`), and
`verdict_indep_of_transcript_digest` (via `decide_verdict_indep_of_tev`:
`decide` never inspects `_ops`/`_tr`/`tev`/`cev`) -- the digest hook records
which transcript was assessed but cannot manufacture or suppress a witness.
Evidence binding: `outcome_transcript_evidence` / `typed_digest_of`
projections with `live_evidence_uses_typed_transcript_digest` /
`offline_evidence_uses_both_digests` / `live_offline_typed_digest_agree`
(same typed digest for live vs. well-formed-offline, independent of the
offline wire digest); conditional on the PER-INPUT `transcript_digest_agrees
ops tr` premise (never a blanket `forall tr` Hypothesis -- the defect class
this project has now held twice), `live_evidence_digest_agrees` /
`offline_evidence_digest_agrees`. Malformed-offline separation:
`malformed_evidence_uses_only_wire_digest`, `malformed_no_typed_digest`,
`malformed_assess_indep_of_transcript_digest` (the WHOLE `assess_validated`
result is `ops`-independent on this branch). `ManifestPipeline.
pipeline_ops_transcript_digest` (pass-through, unchanged) +
`pipeline_transcript_digest_agrees`. Harness: `ExtractTranscriptDigest.v`, a
DEDICATED extraction (`extracted_transcript_digest.ml`) kept separate from
`extracted_stage2.ml` -- adding `assess_validated` there directly perturbed
that file's `Orchestration.policy` / `FibreWitnessKernel.Policy` OCaml type
naming and broke the six existing harnesses; reverted, and this unit's
extraction is fully isolated instead. `ocaml/test_transcript_digest.ml` uses a
deterministic MOCK digest (explicitly not SHA-256) over a submission-free
campaign. See `PHASE_1_TRANSCRIPT_DIGEST.md`. **Reviewer-concurred and
promoted; not a Phase 1 closure.**

Across `make check`, **152** `Print Assumptions` "Closed under the global
context"; `coqchk` covers 20 modules; ten `make test` harnesses PASS (eight
validation-tier + two arbitrary-precision, `PHASE_1_ARBITRARY_PRECISION_EXTRACTION.md`).
Packaging: `make clean` before archiving (source only -- no `*.vo`,
`extracted_*.ml`, or compiled executables); the `Makefile` locates crypto
libraries via `opam var lib` with a `?=` override.

See `PHASE_1_STATUS.md` for the full ledger of the four `PHASE_0_CLOSURE_REPORT.md`
Phase 1 obligations against current state: obligation 1 done; obligations 2, 3,
and 4 partial (obligation 3, arbitrary-precision extraction, is partial as of
`PHASE_1_ARBITRARY_PRECISION_EXTRACTION.md` -- first unit, `ExtractOrchestration.v`
+ `ExtractFibreWitnessKernel.v`, reviewer-concurred and promoted, revision 2;
second unit, `ExtractStage2.v` + its five harnesses, also reviewer-concurred
and promoted, revision 2; `ExtractManifestAuthentication.v`/`ExtractTranscriptDigest.v`
still native-int either way -- not complete). **Phase 1 is open;
no obligation has been deferred to a later phase; Phase 1 closure is not
proposed.**

Phase 1 remains open for: the concrete `AuditContext` fields (`preproc` / `model`
/ `quantise` / `domainb` / `target`) bound to the committed model artifact and
inference spec -- the orchestration `resolved_context` type stays
**dimension-agnostic** by the reviewer's decision (`AuditContext` itself is
indexed by `n_in` / `n_pre` / `n_obs`; the point is that `resolved_context`
carries no such index, and single-context is instead
`PipelineWiring.wiring_resolution_consistent` /
`ContextResolution.stage1_stage2_use_resolved_context`, a theorem, not a
dependent `resolved_context` field); physical capture/replay correspondence;
the general `canonical_value` / remaining `to_cv` encoders (campaign-manifest
rendering + `digest_v1` are concrete); parser/boundary acceptance; converting
`ExtractManifestAuthentication.v` and `ExtractTranscriptDigest.v` to
arbitrary precision (the central `Orchestration`/`FibreWitnessKernel`
extractions and `ExtractStage2.v` + its five harnesses are all now
compiled/linked/executed against one, both reviewer-concurred and promoted
-- `PHASE_1_ARBITRARY_PRECISION_EXTRACTION.md`); the cross-language
agreement battery. `Stage1Evidence` propagation is **done** as an
invariant (`Stage1Invariant.pending_invariant`, carried through `run_stage1` /
`replay`), not runtime-enforced re-checking. `transcript_faithful_for` stays a
stated F.3 assumption by design.

