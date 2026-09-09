# Phase 1 -- concrete `op_manifest_audit_matches` (VERDICT_SEMANTICS 5 step 5)

Date: 2026-09-08
Baseline: `PHASE_1_MANIFEST_LEDGER.md` (r7). One new module,
`implementation/rocq/ManifestAudit.v`, `Qed` and axiom-free; small additions to
`ValidationBinding.v` and `ManifestPipeline.v`.

The validation step being made concrete:

> step 5 -- `ti.M.audit_instance_id = <committed policy payload>.audit_instance_id`
> -> else `ManifestAuditInstanceMismatch`.

## 1. The checker

`ManifestAudit.v`, `Section Audit` over the decoder and the policy projection:

```
Variable parse : manifest -> option campaign_manifest_view.
Variable policy_audit_instance_id_of : policy -> string.

Definition manifest_audit_matches_impl (M : manifest) (ti : trusted_inputs) : bool :=
  match parse M with
  | None    => false
  | Some cm => String.eqb (cm_audit_instance_id cm)
                          (policy_audit_instance_id_of (ti_policy ti))
  end.
```

Exact string equality (`String.eqb`), no normalisation -- a case difference is a
mismatch. A decode failure is `false`. The pipeline passes
`ManifestAuthentication.parse_manifest_impl` as `parse`.

`policy_audit_instance_id_of` is an abstract projection of the policy string. Its
**correctness** -- that it returns the `audit_instance_id` the load-validated
policy actually commits to -- stays an F.3 fact tied to §2.3 policy load
validation **until the policy representation and its parser become concrete** (a
later unit). This module proves only the comparison logic.

## 2. Proved (`Qed`, `Print Assumptions` = "Closed under the global context")

- **`manifest_audit_matches_impl_true_iff`** (full `true` equivalence, not one-way
  soundness): `manifest_audit_matches_impl M ti = true` **iff**
  `exists cm, parse M = Some cm /\ cm_audit_instance_id cm = policy_audit_instance_id_of (ti_policy ti)`.
- **`manifest_audit_matches_impl_false_iff`**: `= false` iff `parse M = None` or
  the decoded id differs.
- **`ValidationBinding.validate_campaign_valid_audit`** : any `ops`,
  `validate_campaign ops ti = ValidCampaign ac l0` implies
  `op_manifest_audit_matches ops (ti_manifest ti) ti = true`
  (standalone, so the existing `validate_campaign_valid_guards` destructures are
  undisturbed).

## 3. Wiring into `pipeline_ops`

`ManifestPipeline.pipeline_ops` now sets its `op_manifest_audit_matches` field to
`ManifestAudit.manifest_audit_matches_impl parse_manifest_impl
policy_audit_instance_id_of` (was the abstract op from `base`). New section
variables `policy_audit_instance_id_of : policy -> string`,
`committed_audit_instance_id : string`, and one hypothesis:

```
committed_policy_audit_id : policy_audit_instance_id_of p_committed
                          = committed_audit_instance_id
```

`pipeline_ops_audit_match` is the `reflexivity` projection.

`validate_campaign_pipeline` is **unchanged** -- still exactly three conclusions.
The audit fact is a **separate theorem**:

```
validate_campaign_audit_agrees :
  policy_digest_load_validated policy_payload_digest_of ti ->
  validate_campaign (pipeline_ops … base) ti = ValidCampaign ac l0 ->
  exists v, parse_manifest_impl (ti_manifest ti) = Some v
         /\ cm_audit_instance_id v = committed_audit_instance_id
```

Proof: `validate_campaign_valid_audit` + `pipeline_ops_audit_match` +
`manifest_audit_matches_impl_true_iff` give
`cm_audit_instance_id v = policy_audit_instance_id_of (ti_policy ti)`;
`ManifestMatching.validate_campaign_concrete_binds_policy` (needs
`policy_digest_load_validated`) gives `ti_policy ti = p_committed`;
`committed_policy_audit_id` closes it.

## 4. Harness -- `ocaml/test_manifest_authentication.ml`

`manifest_audit_matches_impl` is extracted (`ExtractManifestAuthentication.v`).
New assertions over a rendered schema-valid manifest
(`cm_audit_instance_id = "ai-0001"`) and a minimal `trusted_inputs`:

- **matching identity** (`policy_audit_instance_id_of` yields `"ai-0001"`) -> `true`;
- **differing identity** (`"ai-9999"`) -> `false`;
- **case difference** (`"AI-0001"`) -> `false` (exact, case-sensitive);
- **non-decoding manifest** (`"{}"`) -> `false`;
- the id is genuinely read from `policy_audit_instance_id_of (ti_policy ti)`:
  with the projection = identity, `ti_policy = "ai-0001"` -> `true`,
  `ti_policy = "ai-0002"` -> `false`.

## Effect on the status ledger

`op_manifest_audit_matches`: **was OPEN, now concrete standalone AND integrated**
(`pipeline_ops`). Residual: `policy_audit_instance_id_of` correctness (F.3, tied
to §2.3 load validation until the policy parser is concrete) and, downstream,
retrieval integrity.

Still OPEN: `op_completeness_wellformed`, `op_record_crosscheck` (needs
`recorded_results` represented), `op_transcript_digest`.  (`op_record_identity_mismatch`
is now concrete -- `CampaignRecord`, `PHASE_1_CAMPAIGN_RECORD.md`.)

`make check` exits 0: `coqchk` covers **17** modules (adds `PCFW.ManifestAudit`);
across `make check`, **101** `Print Assumptions` "Closed under the global context";
**seven** `make test` harnesses PASS.

Phase 1 remains **open**; Phase 2 is not authorised; this is an author-reported
unit for review, not a promotion or Phase 1 closure.
