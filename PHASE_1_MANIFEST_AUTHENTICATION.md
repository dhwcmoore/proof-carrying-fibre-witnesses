# Phase 1 -- concrete authenticated-manifest validation (AUDIT_POLICY 2.4.1)

Date: 2026-09-08 (revised twice after reviewer defects)
Baseline: `PHASE_1_MANIFEST_MATCHING.md` (r4). Bounded first slice of the
remaining validation operations: `op_parse_commitment`, `op_signer_authorised`,
`op_signature_valid` made concrete; `parse_manifest` and
`manifest_authenticated_by` made concrete implementations; the shared manifest
type unified and `parse_manifest_impl` wired into the matching capstone.

Modules (all `Qed`, axiom-free): `CanonicalV1.v`, `ManifestAuthentication.v`,
`ManifestPipeline.v`. `ManifestMatching.v` and `ContextResolution.v` retargeted onto the shared descriptor type.

## 1. Data-representation repair (frozen `Orchestration.v`)

Governing spec already specifies these (§2.4.1 wire type, §2.5 `trust_anchor`,
§2.2.5 `to_cv`); the code now matches:

| type | change |
|---|---|
| `manifest_commitment` | `+ commitment_signature : bytes` (64 decoded signature bytes) |
| `manifest_commitment_wire` | `{ commitment_wire_bytes }` -> `{ cw_digest; cw_signer; cw_signature }` |
| `verifier_config` | `+ config_trust_anchor : trust_anchor`; new `trust_anchor`, `ta_key_of`, `signer_in` |
| `primitive_ops` | `op_signer_authorised` / `op_signature_valid` gained a `verifier_config` argument |
| `signature_valid_impl` | now also runs an F.3 `ed25519_pubkey_valid : bytes -> bool` on the looked-up key (rejects the identity / cofactor-torsion keys the bare group equation accepts for S = 0) -- so trust-anchor key validation is **on the validation path**, not only in the harness |
| `validate_campaign` | threads `ti_config ti` -- the trust anchor used is the one in the config under validation |

Ordering and per-phase fuel charging unchanged;
`validation_fuel_obstructed_unreachable_when_sufficient`,
`ValidationBinding.validate_campaign_valid_guards` (now also exposes
`op_signer_authorised … = true`) re-proved. No governing-document change.

## 2. Shared manifest type (defect 1)

`CanonicalV1.campaign_manifest_view` (5 fields incl. `cm_campaign_id`) and
`CanonicalV1.context_descriptor` are now **the** validation types.
`ManifestMatching.v` uses them (`Notation`, its old local record removed).
`parse_manifest_impl` produces `CanonicalV1.campaign_manifest_view` -- the same
type the matching capstone consumes.

**`ManifestPipeline.v`** builds `pipeline_ops` = the authentication ops **plus**
`manifest_policy_matches_impl digest_eqb parse_manifest_impl` and
`manifest_context_matches_impl digest_eqb parse_manifest_impl policy_context_of`,
and proves the **integrated capstone**:

```
validate_campaign_pipeline :
  policy_digest_load_validated policy_payload_digest_of ti ->
  validate_campaign (pipeline_ops … base) ti = ValidCampaign ac l0 ->
    manifest_authenticated_by_impl … (ti_config ti) (authenticated_commitment ac)
                                       (authenticated_manifest ac)
  /\ ti_policy ti = p_committed
  /\ pipeline_commits (ti_config ti) (authenticated_commitment ac) committed_descriptor
```

One `validate_campaign` success yields **three** facts: the §2.4.1
authentication fact, `ti_policy ti = p_committed`, and
`pipeline_commits (ti_config ti) (authenticated_commitment ac)
committed_descriptor` -- the authenticated manifest committing to the descriptor
**in the shared `context_descriptor` type that O1/O2/O3 consume**
(`ContextResolution.descriptor` is now a `Notation` for
`CanonicalV1.context_descriptor`, so the manifest, matching, O1/O2/O3 and
`ValidationBinding` paths all use one type). No opaque `parse_manifest`, no
opaque manifest-match contract.

## 3. `CanonicalV1.v` -- digest input + schema predicates

- `esc_str` / `json_string` : §2.2.2 escaping.
- `render_manifest` : `canonicalise_v1(to_cv(campaign_manifest))` for the fixed
  schema. `render_manifest_frozen_vector` (`vm_compute`) = the §2.2.5 payload
  string byte-for-byte.
- `digest_v1` / `campaign_manifest_digest` (over the F.3 `sha256_hex`).
- `is_hex64`; `valid_utf8` (RFC 3629 structural + overlong / surrogate / range
  guards); `manifest_wellformed`; `schema_valid_manifest` (full-length hex
  digests) with `schema_valid_manifest_wf`.

## 4. `ManifestAuthentication.v` -- schema-conforming decoder + 2.4.1 (defect 2)

`parse_manifest_impl` is a schema-conforming decoder for the canonical wire
form. **Explicit input requirement**: keys in byte-ascending order, no
whitespace, and identifier values restricted to ASCII (0x20..0x7F plus the
escape-decodable controls); non-ASCII UTF-8 identifiers and non-canonical key
order are **rejected** (future work). Within that it:

- gates the whole input on `valid_utf8`;
- **decodes** the §2.2.2 escapes: `\"` `\\` `\b` `\t` `\n` `\f` `\r`, and
  `\u00xx` **only** for a control code point with no named escape
  (U+0000..U+0007, U+000B, U+000E..U+001F); a `\u00xx` for a named-escape value
  or for a code point >= U+0020 is **rejected**, as is a raw control byte
  (< 0x20), a raw non-ASCII byte, and a lone / unknown backslash;
- requires every digest-typed field to be **exactly 64 lowercase hex**;
- **rejects a trailing comma** in the submission-digest array;
- rejects a duplicate key / unknown field (template mismatch).

### Proved (`Qed`, `Print Assumptions` = "Closed under the global context")

- **`parse_manifest_impl_wf`**: any accepted manifest satisfies
  `CanonicalV1.manifest_wellformed` -- all digest fields 64-lowercase-hex, both
  ids valid UTF-8. (via `parse_digest_field_wf`, `parse_str_body_all_ascii`,
  `parse_dig_array_wf`.)
- **`parse_manifest_impl_roundtrip`**: for every `m` with `manifest_roundtrip_wf
  m`, `parse_manifest_impl (mkManifest (render_manifest m)) = Some m`.
  `manifest_roundtrip_wf` requires 64-lowercase-hex digest fields and identifiers
  whose bytes are all ASCII 0x20..0x7E except `"` and `\`; canonical key order is
  supplied by `render_manifest`, **not** expressed by `manifest_roundtrip_wf`.
- `parse_manifest_impl_schema_valid_vector` / `_rejects_short_digests`
  (`vm_compute`): the schema-valid vector round-trips; the §2.2.5 short-digest
  frozen vector is **rejected**.
- `esc_decode_quote` / `esc_decode_u0000` / `esc_decode_u001f` and
  `esc_reject_u0061` / `esc_reject_u0008` / `esc_reject_u00ff` /
  `esc_reject_raw_ctrl` / `esc_reject_raw_nonascii` (`vm_compute`): the escape
  decoder accepts exactly the canonical `\u00xx` forms and rejects the rest.
- `parse_commitment_impl_sound` / `_reject_not_parsed`.
- `signature_valid_impl_sound`: `= true` gives digest agreement +
  `ta_key_of … = Some k` + `ed25519_pubkey_valid k = true` +
  `ed25519_verify k mc.signature mc.digest = true` (message = `utf8(mc.digest)`).
- `auth_from_ops`; `validate_campaign_authenticates` /
  `validate_campaign_authenticates_ops`.

## 5. Trust boundary (F.3) -- SHA-256 and Ed25519

`sha256_hex`, `ed25519_verify` and `ed25519_pubkey_valid` are section variables
-> explicit theorem premises; **not** proved in Coq (SHA-256 collision-resistance,
Ed25519 soundness, and canonical / non-small-order public-key decoding are F.3
per Phase 0). The claim is: the authentication composition and
validation control flow are formalised, and the SHA-256 / Ed25519 F.3 components
are tested against normative vectors.

Retrieval integrity (that the retrieved object is the intended audit's) is **not**
established by authentication and stays an explicit premise
(`ManifestPipeline.validated_manifest_is_audit`,
`ManifestMatching.validated_*_is_audit`).

## 6. Harness -- `ocaml/test_manifest_authentication.ml` (defect 3)

Links real SHA-256 (`sha` library) + `zarith`; a pure-OCaml RFC 8032 Ed25519
**verify and sign**. 37 assertions:

- frozen digest `0714f76c…`; byte-exact canonical render.
- **Ed25519 RFC 8032 TEST 1** verifies; one-bit-flip rejected.
- **invalid-point / degenerate rejections**: `y >= p`; the non-canonical
  identity encoding with the sign bit set (RFC 8032 §5.1.3, `x = 0 ∧ x_0 = 1`);
  a low-order (cofactor-torsion) public key rejected by `valid_pubkey_hex`
  (trust-anchor key validation: 64 lowercase hex → canonical, non-small-order
  point).
- `parse_commitment_impl` rejects wrong digest length / uppercase / non-hex /
  wrong signature length / non-hex signature.
- `parse_manifest_impl`: round-trips a **schema-valid** manifest; **rejects** the
  short-digest frozen vector, `{}`, a truncated object, a **trailing comma**, a
  **raw control byte**, **invalid UTF-8**; round-trips a value carrying `"` and
  `\` (escape decode).
- **REAL end-to-end positive**: sign `utf8(campaign_manifest_digest schema_valid)`
  with the pure-OCaml Ed25519 sign; `signature_valid_impl sha256_hex
  ed25519_verify ed25519_pubkey_valid c_real mc sv_bytes = true`.
- **low-order key on the validation path**: a config whose trust-anchor key is
  the identity point makes `signature_valid_impl` return `false` (it now runs
  `ed25519_pubkey_valid k` -- see below).
- `signature_valid_impl`: signature over `digest ++ "\n"` rejected; over the
  decoded digest bytes rejected; digest mismatch → false with **no verify call**;
  on a match the verifier is called with **exactly the digest string**; missing
  key → false; signer authorised / unauthorised.

`validate_campaign`'s `SignerNotAuthorised`-before-`SignatureInvalid` ordering
and fuel accounting are unchanged Coq control flow
(`validation_fuel_obstructed_unreachable_when_sufficient`).

RFC 8032 §6 notes its illustrative code is not for production; the pure-OCaml
verifier here is an **F.3 test component** checked against vectors, not a
verified primitive -- a maintained Ed25519 library would replace it in a
production build.

## 7. Packaging

`make check` regenerates all extracted OCaml and compiled harnesses; the archive
ships **source only** -- `make clean` before packaging, then the archive tree is
swept for `*.vo` / `*.aux` / `*.glob` / `*.cm[iox]` / `*.o`, `extracted_*.ml`
(both the archive root's stale `.lia.cache` and any compiled `ocaml/test_*`
executable), so no build product or embedded dependency code is shipped. The
`Makefile` locates the crypto libraries via `$(shell opam var lib …)` with `?=`
variables (`OCAML_LIB` / `ZARITH` / `SHALIB`), and a `$HOME/.opam/default/lib`
fallback only when `opam` is absent -- overridable from the command line.

## Effect on the status ledger

`op_parse_commitment` / `op_signer_authorised` / `op_signature_valid`:
**concrete standalone AND integrated** (`pipeline_ops`), F.3 residuals
`sha256_hex` / `ed25519_verify` / `ed25519_pubkey_valid` + retrieval integrity. `parse_manifest` /
`manifest_authenticated_by`: concrete implementations, wired into the matching
capstone. `op_ledger_mismatch` is now concrete too (`ManifestLedger`, six
results -- see `PHASE_1_MANIFEST_LEDGER.md`); `op_manifest_audit_matches` is
concrete (`ManifestAudit`, full `true` equivalence -- `PHASE_1_MANIFEST_AUDIT.md`);
`op_record_identity_mismatch` is concrete (`CampaignRecord`, structured
`campaign_record_view` + canonical full-record decoder, five step-8 identity fields --
`PHASE_1_CAMPAIGN_RECORD.md`).
Still OPEN: `op_completeness_wellformed`, `op_record_crosscheck` (needs
`recorded_results` represented), `op_transcript_digest`; a maintained Ed25519;
the retrieval-integrity premise; a key-order-tolerant manifest decoder.

`make check` exits 0: `coqchk` covers 17 modules (adds `PCFW.CanonicalV1`,
`PCFW.ManifestAuthentication`, `PCFW.ManifestPipeline`, `PCFW.ManifestLedger`,
`PCFW.ManifestAudit`, `PCFW.CampaignRecord`); across `make check`, **101** `Print
Assumptions` "Closed under the global context" (the last 30 are the
`op_ledger_mismatch`, `op_manifest_audit_matches` and `op_record_identity_mismatch`
units -- `PHASE_1_MANIFEST_LEDGER.md`, `PHASE_1_MANIFEST_AUDIT.md`,
`PHASE_1_CAMPAIGN_RECORD.md`); **seven** `make test` harnesses PASS.
`parse_manifest_impl_wf` proves every accepted manifest is
`CanonicalV1.manifest_wellformed`.

Phase 1 remains **open**; Phase 2 is not authorised. **Reviewer-concurred by source inspection and promoted** as part of the cumulative r5–r13 validation block (reviewer disposition on r13; the reviewed r13 bytes, ZIP sha256 `7691bc1d05d1fb85648da9126372476589acd9971b2decc997c37dd424335419`). Not a Phase 1 closure.
