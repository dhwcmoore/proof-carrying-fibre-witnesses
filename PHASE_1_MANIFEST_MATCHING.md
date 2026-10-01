# Phase 1 -- concrete manifest-matching primitives; the two `ValidationBinding` contracts replaced

> Historical evidence: this report preserves the pre-Batch-5 interfaces and
> acceptance boundary. Batch 5 replaces their universal policy digest injectivity
> with explicit local `policy_binding` and adopts a parametric release.
> The earlier injectivity/semantic-loader blocker below is superseded; absence
> of a concrete semantic loader is **NOT IN PHASE-1 SCOPE**. See
> [TRUST.md](TRUST.md) and [RELEASE_CRITERIA.md](RELEASE_CRITERIA.md).

Date: 2026-09-07 (revised same day after reviewer defects; further revised
2026-09-08 by the authentication unit)
Baseline: `PHASE_1_VALIDATION_BINDING.md`. One new module,
`implementation/rocq/ManifestMatching.v`, `Qed` and axiom-free.

> **Superseded in part by `PHASE_1_MANIFEST_AUTHENTICATION.md`.** That unit
> unified the manifest view type (`ManifestMatching` now uses the shared
> `CanonicalV1.campaign_manifest_view` / `CanonicalV1.context_descriptor`, not a
> local 4-field record), made `parse_manifest` concrete
> (`ManifestAuthentication.parse_manifest_impl`), made `manifest_authenticated_by`
> concrete (`manifest_authenticated_by_impl`, modulo the F.3 `sha256_hex` /
> `ed25519_verify` / `ed25519_pubkey_valid`), and wired both into an integrated
> capstone
> (`ManifestPipeline.validate_campaign_pipeline`). The "uninterpreted predicate"
> and "open `op_parse_commitment` / `op_signer_authorised` / `op_signature_valid`"
> statements below are historical -- see the authentication doc for current
> status. Current build: `coqchk` 20 modules, **152** `Print Assumptions`
> "Closed under the global context", eight `make test` harnesses (the later
> additions are the authentication, `op_ledger_mismatch`,
> `op_manifest_audit_matches`, `op_record_identity_mismatch`,
> `op_completeness_wellformed`, and `op_transcript_digest` units --
> `PHASE_1_MANIFEST_AUTHENTICATION.md`, `PHASE_1_MANIFEST_LEDGER.md`,
> `PHASE_1_MANIFEST_AUDIT.md`, `PHASE_1_CAMPAIGN_RECORD.md`,
> `PHASE_1_COMPLETENESS_WELLFORMED.md`, `PHASE_1_TRANSCRIPT_DIGEST.md`).

`ValidationBinding.v` proved the validation-to-replay connection *modulo* two
opaque contracts on the manifest-matching primitives (`policy_match_sound`,
`context_match_sound`). This unit replaces them with concrete boolean matchers
plus proofs, reduced to narrower residuals.

## Reviewer defects in the first cut, and the repairs

1. **`ti_policy_digest_truthful : forall ti, ti_policy_digest ti =
   policy_payload_digest_of (ti_policy ti)` was inconsistent** -- two `trusted_inputs`
   records may share a policy but carry different digest strings, so the universal
   form forces those strings equal.
   **Repair:** `policy_digest_load_validated ti`, a predicate on **one** input,
   supplied as an explicit premise (the AUDIT_POLICY §2.3 load-validation
   postcondition for that input).

2. **`authenticated_manifest_policy_hash : forall mc M cm, …` was unscoped** -- it
   forced every authenticated, parsed manifest to carry this section's committed
   policy digest.
   **Repair:** the audit's published objects are now **fixed** section variables
   -- `audit_commitment`, `audit_manifest`, `audit_view` -- and the hypotheses
   speak only about them:
   - `audit_authenticated : manifest_authenticated_by audit_commitment audit_manifest`
   - `audit_manifest_parses : parse_manifest audit_manifest = Some audit_view`
   - `audit_policy_hash_committed : cm_policy_hash audit_view = policy_payload_digest_of p_committed`
   - `committed_policy_context : policy_context_of p_committed = committed_descriptor`

   and a **successful validation is connected to those fixed objects**:
   - `validated_commitment_is_audit : validate_campaign ops ti = ValidCampaign ac l0 -> authenticated_commitment ac = audit_commitment`
   - `validated_manifest_is_audit : … -> ti_manifest ti = audit_manifest`

   (the F.3 retrieval-integrity + Ed25519-unforgeability residual, stated once,
   about the selected commitment). `manifest_authenticated_by` remains an
   uninterpreted predicate -- its Ed25519 / `digest_v1` meaning is documented,
   not implemented.

3. **The `discharges_*` lemmas were "contract-shaped modulo extra premises"** and
   did not instantiate `ValidationBinding`'s contracts, whose live/offline
   replay-policy consumers were unchanged.
   **Repair:** removed; replaced by `assess_validated_{live,offline}_concrete` --
   the **same statements** as `ValidationBinding.assess_validated_*_uses_committed_policy`,
   proved here from the corrected capstone with no opaque contract (plus the
   per-input `policy_digest_load_validated` premise, which validation does not
   supply -- §2.3 load validation is assumed done on trusted inputs).

## The matchers

Over a parsed `campaign_manifest_view` (`{cm_audit_instance_id; cm_policy_hash :
digest; cm_context_digests : descriptor; cm_submission_digests}`) decoded by the
F.3 `parse_manifest`:

```
manifest_policy_matches_impl  M ti :=
  match parse_manifest M with Some cm => digest_eqb (cm_policy_hash cm) (ti_policy_digest ti) | None => false end
manifest_context_matches_impl M ti :=
  match parse_manifest M with Some cm => descriptor_eqb (cm_context_digests cm) (policy_context_of (ti_policy ti)) | None => false end
```

`descriptor_eqb` is built from `digest_eqb` and proved injective
(`descriptor_eqb_true`); `digest_eqb_true` is the only equality-decider
hypothesis. `commits` gets a concrete definition `commits_impl mc d := ∃ M cm,
manifest_authenticated_by mc M ∧ parse_manifest M = Some cm ∧ cm_context_digests
cm = d`.

## Proved (`Qed`, `Print Assumptions` = "Closed under the global context")

- **`manifest_policy_matches_impl_sound`** : `policy_digest_load_validated ti`,
  `parse_manifest (ti_manifest ti) = Some audit_view`, and the policy matcher
  returning `true` imply `ti_policy ti = p_committed`.
- **`manifest_context_matches_impl_sound`** : `ti_policy ti = p_committed`, the
  same parse fact, and the context matcher returning `true` imply
  `commits_impl audit_commitment committed_descriptor`.
- **`validate_campaign_concrete_binds_policy`** (policy-only capstone) : for the
  `ops` whose policy matcher is `manifest_policy_matches_impl`,
  `policy_digest_load_validated ti` and `validate_campaign ops ti = ValidCampaign
  ac l0` imply `ti_policy ti = p_committed`. Proved from the **policy matcher
  alone**; after section discharge its premises do **not** include
  `ops_context_match`, `validated_commitment_is_audit`, `audit_authenticated`,
  `committed_policy_context`, `policy_context_of`, or `committed_descriptor`
  (`Check` / `Print Assumptions` confirm).
- **`validate_campaign_concrete_binds`** (full capstone) : the same premises
  (plus the context-side hypotheses) imply `ti_policy ti = p_committed` **and**
  `commits_impl (authenticated_commitment ac) committed_descriptor` -- with **no**
  opaque `policy_match_sound` / `context_match_sound`. First conjunct is
  `validate_campaign_concrete_binds_policy`; second uses the context lemma.
- **`assess_validated_live_concrete`** / **`assess_validated_offline_concrete`** :
  the `ValidationBinding.assess_validated_*_uses_committed_policy` statements,
  proved from `validate_campaign_concrete_binds_policy` -- so they carry **only**
  `policy_digest_load_validated` beyond the policy-side hypotheses, no
  context-side dependency.
- **`manifest_matching_core_hyps_consistent`** : concrete witnesses (`String.eqb`,
  identity `policy_payload_digest_of`, a fixed `campaign_manifest_view`, a fully
  built `trusted_inputs`) satisfy the **seven core non-`ops` facts** together --
  `digest_eqb_true`, `policy_payload_digest_injective`, `audit_authenticated`,
  `audit_manifest_parses`, `audit_policy_hash_committed`, `committed_policy_context`,
  and `policy_digest_load_validated` for that input. So those hypotheses are **not
  mutually contradictory** (defect 1: the old `forall ti` truthfulness is gone).
  It does **not** formally exhibit an `ops`, the four `ops`-hypotheses, or a
  successful `validate_campaign` -- it is a consistency result, **not** full
  non-vacuous satisfiability of the capstone's premises.

## Residual F.3 facts

| hypothesis | meaning | discharge route |
|---|---|---|
| `parse_manifest` | campaign-manifest wire decoder | concrete canonical decoder (parallel to `parse_descriptor`) |
| `manifest_authenticated_by` | the §2.4.1 `authenticate_manifest` predicate | Ed25519 verifier + `digest_v1` implementation |
| `audit_authenticated`, `audit_manifest_parses`, `audit_policy_hash_committed`, `committed_policy_context` | the audit's published commitment authenticates its manifest, which decodes to a view whose policy hash is the committed policy's digest and whose context digests the committed policy also embeds (§2.4 steps 3, 6) | the commitment procedure; auditable from the signed tags |
| `validated_commitment_is_audit`, `validated_manifest_is_audit` | a successful validation is a validation *of this audit* | retrieval integrity + Ed25519 unforgeability |
| `policy_payload_digest_injective` | `digest_v1` collision-freedom on policy payloads | the crypto idealisation |
| `policy_digest_load_validated ti` | supplied per validated input | the §2.3 load-validation postcondition |

## Effect on the status ledger

Closure-report obligation 2, row `op_manifest_*_matches`: **was OPEN, now
concrete**, with `ValidationBinding`'s two contracts replaced by the capstone and
the two `assess_validated_*_concrete` corollaries (no opaque contract), modulo the
table above. Since this unit, `op_parse_commitment` / `op_signer_authorised` /
`op_signature_valid` (`ManifestAuthentication`), `op_ledger_mismatch`
(`ManifestLedger`), `op_manifest_audit_matches` (`ManifestAudit`) and
`op_record_identity_mismatch` (`CampaignRecord`) have all been made concrete.
`op_record_crosscheck` is concrete (`RecordCrosscheck`, verdict-invariant,
reviewer-concurred + promoted r17); `op_completeness_wellformed` is concrete
(`CompletenessWellformed`, reviewer-concurred + promoted r3 --
`PHASE_1_COMPLETENESS_WELLFORMED.md`); `op_transcript_digest` has a
contract-bound primitive treatment (the hook stays primitive; its normative
digest realisation stays F.3, so it is NOT concrete) (`TranscriptDigest`,
reviewer-concurred + promoted r3 -- `PHASE_1_TRANSCRIPT_DIGEST.md`).

`make check` exits 0: `coqchk` covers `PCFW.ManifestMatching` (eleven modules);
across `make check`, **53** `Print Assumptions` "Closed under the global
context"; **six** `make test` harnesses PASS.

Phase 1 remains **open**; Phase 2 is not authorised. **Reviewer-concurred by source inspection and promoted** as part of the cumulative r5–r13 validation block (reviewer disposition on r13; the reviewed r13 bytes, ZIP sha256 `7691bc1d05d1fb85648da9126372476589acd9971b2decc997c37dd424335419`). Not a Phase 1 closure.
