# Phase 1 -- structured campaign-record view + decoder, and concrete `op_record_identity_mismatch` (VERDICT_SEMANTICS 5 step 8)

Date: 2026-09-08
Baseline: `PHASE_1_MANIFEST_AUDIT.md` (r9). One new module,
`implementation/rocq/CampaignRecord.v`, `Qed` and axiom-free; small additions to
`ValidationBinding.v` and `ManifestPipeline.v`.

The validation step being made concrete:

> step 8 -- `ti.rec.{campaign_id, audit_instance_id, policy_hash, context_digests,
> manifest_digest}` agree -> else `RecordIdentityMismatch{field}`.

## 1. Structured view + decoder

The wire-level `Orchestration.campaign_record` (`{ record_token : string }`) is
**unchanged**.  `CampaignRecord.v` adds -- in the established `manifest` /
`campaign_manifest_view` pattern -- a structured view and a strict decoder:

```
Record campaign_record_view := mkCampaignRecordView {
  crv_campaign_id       : string;
  crv_audit_instance_id : string;
  crv_policy_hash       : digest;
  crv_context_digests   : context_descriptor;
  crv_manifest_digest   : digest }.

render_campaign_record : campaign_record_view -> string
parse_record_impl      : campaign_record -> option campaign_record_view
```

**`campaign_record_view` is the five-field identity projection.**
`parse_record_impl` nonetheless decodes a **FULL campaign record over the
canonical ASCII-wire subset** -- the eight keys in byte-ascending order

```
audit_instance_id, campaign_id, completeness, context_digests,
manifest_digest, policy_hash, recorded_results, resource_budget
```

-- extracting the five identity fields.  `completeness`, `recorded_results` and
`resource_budget` are **syntactically consumed** by `skip_value` (string /
integer / boolean / null / array / object, fuel-bounded), **not** interpreted.
Cross-checking `recorded_results` / `resource_budget` is a later
`op_record_crosscheck` unit; that needs a **full typed record representation and
semantic decoder** for those fields, not just `skip_value` -- **this unit does
not by itself unlock `op_record_crosscheck`**.

**`skip_value` enforces the canonical form**, it does not merely tolerate JSON:
integers are exactly `0 | -?[1-9][0-9]*` (no leading zero, no `-0`); every
skipped object's keys are **strictly byte-ascending and duplicate-free**;
strings go through `ManifestAuthentication.parse_json_string`.

**ASCII-wire restriction (explicit, as for the manifest decoder).**  The whole
input is gated on `CanonicalV1.valid_utf8`, and every string -- identifiers,
digests, and every string inside a skipped value -- is read by
`parse_json_string`, which accepts raw bytes only in ASCII `0x20..0x7F` (plus the
escape-decodable controls via `\uXXXX`).  A record carrying a raw non-ASCII
(`>= 0x80`) UTF-8 string is **rejected**; a UTF-8-tolerant campaign-record
decoder is future work.

`parse_record_impl` uses `ManifestAuthentication.starts_with` /
`parse_json_string` / `parse_digest_field` (no whitespace, digest fields exactly
64 lowercase hex); `context_digests` decodes with the same sub-object grammar as
the manifest.  `render_campaign_record` emits a full eight-key record with
`"completeness":"unknown"` (the no-payload `Unknown` form), `[]`, `{}`.

`vm_compute` vectors: `parse_record_impl_schema_valid_vector` (render/parse
round-trip); **`parse_record_impl_full_record_vector`** -- a **schema-valid** full
record (per AUDIT_POLICY 2.2.5: `"completeness":{"k":"complete","v":{"body":…,"scheme":…}}`;
`recorded_results` with a `{"k":"accepted","v":"valid_witness"}` entry and a
`{"k":"accepted","v":{"k":"not_a_witness","v":"inputs_equal"}}` entry whose
finding is `{"check_id":"C1","outcome":"fail","reason":"inputs_equal"}`; a
populated `resource_budget`) decodes to the identity view;
`parse_record_impl_accepts_canonical_budget`;
`parse_record_impl_rejects_empty_object`;
**`parse_record_impl_rejects_identity_only`** (the five-field mini-form is
**rejected**); and the canonicality rejections
**`parse_record_impl_rejects_leading_zero`** / **`_rejects_neg_zero`** /
**`_rejects_dup_key`** / **`_rejects_descending_keys`** on the `resource_budget`
slot.  The OCaml harness mirrors all of these.

## 2. The comparison

`record_identity_mismatch_impl parse_rec parse_man r mc M` decodes `r` and `M`,
then compares in the **frozen order**

| # | field | compared against |
|---|---|---|
| 1 | `campaign_id`       | `cm_campaign_id` of the decoded manifest |
| 2 | `audit_instance_id` | `cm_audit_instance_id` |
| 3 | `policy_hash`        | `cm_policy_hash` |
| 4 | `context_digests`   | `cm_context_digests` (field-wise) |
| 5 | `manifest_digest`   | `commitment_digest mc` |

returning `Some "<field name>"` at the **first** inequality, else `None`.

**Deterministic decoder-failure sentinels**, distinct from every field name and
from each other (both begin with `!`, which no field name contains):

- record fails to decode -> `Some "!record_undecodable"`
  (`sentinel_record_undecodable`);
- record decodes, manifest fails -> `Some "!manifest_undecodable"`
  (`sentinel_manifest_undecodable`).

`record_sentinels_distinct` proves the two sentinels differ from each other and
from all five field names.

## 3. Proved (`Qed`, `Print Assumptions` = "Closed under the global context")

- **`record_identity_mismatch_impl_none_iff`** -- `= None` **iff** both decoders
  succeed **and** all five equalities hold (complete equivalence, both
  directions).
- **`record_identity_mismatch_impl_some_<field>`** for each of the five fields --
  `= Some "<field>"` implies all *preceding* fields agree **and** the named field
  genuinely differs.
- **`record_identity_mismatch_impl_record_undecodable_iff`** -- `= Some
  sentinel_record_undecodable` iff `parse_rec r = None`.
- **`record_identity_mismatch_impl_manifest_undecodable_iff`** -- `= Some
  sentinel_manifest_undecodable` iff the record decodes and the manifest does not.
- **`cd_eqb_true` / `cd_eqb_refl` / `cd_eqb_eq`** -- the `context_descriptor`
  decider is sound and complete.
- **`ValidationBinding.validate_campaign_valid_record`** -- any `ops`,
  `validate_campaign ops ti = ValidCampaign ac l0` implies `exists mc,
  op_parse_commitment ops (ti_commitment_wire ti) = CommitmentParsed mc /\
  op_record_identity_mismatch ops (ti_record ti) mc (ti_manifest ti) ti = None`.
  Standalone -- `validate_campaign_valid_guards` is **unchanged**.

## 4. Wiring into `pipeline_ops`

`ManifestPipeline.pipeline_ops` sets its `op_record_identity_mismatch` field to
`fun r mc M _ => CampaignRecord.record_identity_mismatch_impl parse_record_impl
parse_manifest_impl r mc M` (was the abstract op from `base`).
`pipeline_ops_record` is the `reflexivity` projection.

`validate_campaign_pipeline` is **unchanged** -- still exactly three conclusions.
The record fact is a **separate theorem**:

```
validate_campaign_record_agrees :
  validate_campaign (pipeline_ops … base) ti = ValidCampaign ac l0 ->
  exists rv cm,
    parse_record_impl (ti_record ti) = Some rv /\
    parse_manifest_impl (ti_manifest ti) = Some cm /\
    crv_campaign_id rv       = cm_campaign_id cm /\
    crv_audit_instance_id rv = cm_audit_instance_id cm /\
    crv_policy_hash rv       = cm_policy_hash cm /\
    crv_context_digests rv   = cm_context_digests cm /\
    crv_manifest_digest rv   = commitment_digest (authenticated_commitment ac)
```

(from `validate_campaign_valid_record` + `pipeline_ops_record` +
`record_identity_mismatch_impl_none_iff`, with `mc` connected to
`authenticated_commitment ac` via `validate_campaign_valid_guards`).

## 5. Harness -- `ocaml/test_manifest_authentication.ml`

`render_campaign_record`, `parse_record_impl`, `record_identity_mismatch_impl` are
extracted.  New assertions over a record view matching the schema-valid manifest
and `good_digest`:

- complete matching case -> `None`; a **normative full record** (payload
  `completeness`, `recorded_results` with two `{"k":"accepted","v":…}` entries,
  populated `resource_budget`) decodes and matches; the five-field identity-only
  form is rejected; non-canonical `resource_budget` bytes (leading-zero / `-0` /
  duplicate key / descending keys) are rejected;
- each of the five identity fields, individually mismatched -> `Some "<that
  field>"`;
- multiple mismatches -> the earliest field in the frozen order
  (`campaign_id` before `policy_hash`; `policy_hash` before `manifest_digest`);
- case-only identifier differences (`"AI-0001"`, `"CMP-1"`) -> mismatch on that
  field;
- record decode failure -> `Some "!record_undecodable"`; manifest decode failure
  -> `Some "!manifest_undecodable"`; both fail -> the record sentinel;
- neither sentinel is a field name;
- `render_campaign_record` round-trips through `parse_record_impl`.

## Effect on the status ledger

`op_record_identity_mismatch`: **was OPEN (blocked on `campaign_record`
representation), now concrete standalone AND integrated** (`pipeline_ops`),
bounded to the five step-8 identity fields.  Residual: the two decoders passed in
(both concrete) and, downstream, retrieval integrity.

Still OPEN: `op_completeness_wellformed`, `op_transcript_digest`.
(`op_record_crosscheck` was made concrete in the follow-on `RecordCrosscheck`
unit -- `PHASE_1_RECORD_CROSSCHECK.md`.)

`make check` exits 0: `coqchk` covers **18** modules (adds `PCFW.CampaignRecord`);
across `make check`, **121** `Print Assumptions` "Closed under the global context";
**seven** `make test` harnesses PASS.

Phase 1 remains **open**; Phase 2 is not authorised. **Reviewer-concurred by source inspection and promoted** as part of the cumulative r5–r13 validation block (reviewer disposition on r13; the reviewed r13 bytes, ZIP sha256 `7691bc1d05d1fb85648da9126372476589acd9971b2decc997c37dd424335419`). Not a Phase 1 closure.
