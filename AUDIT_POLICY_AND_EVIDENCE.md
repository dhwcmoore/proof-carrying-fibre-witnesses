# Audit Policy and Evidence Obligations

**Deliverable:** Phase 0, Unit 0E
**Status:** Draft for Unit 0G ratification. **Revision 15** — §2.2 gains encodings
for the new `campaign_obstruction` `"inconsistent_context_bundle"` and
`context_state` `"context_bundle_inconsistent"` (both nullary, the standard
constructor rule; `ctx_reason` unchanged). See
`phase0_closure_package_r1/CONTEXT_BUNDLE_AMENDMENT.md`. Revision 14 —
`assessment_outcome`
carries a `certificate` in every non-`Underdetermined` constructor. An explicit
immutable `loaded_context` (one F.3 `load_context`) is threaded through capture /
replay, so `preflight_O1_O2` / `eval_O3` / `resolved_context` are constructible.
Stage-1 fuel `` `Over `` is a terminal return. `transcript_source` keeps
entry-point provenance; `transcript_evidence` = `LiveCapture` (`(CAP1)`) vs
`OfflineTranscript` (`(REP1)` only). One `validate_campaign` per pipeline;
charge-before-work; `` `FuelObstructed `` dead.
**Normative.**

---

## 1. Principle

The generator cannot choose the conditions under which its own candidate is
accepted. Every quantity that affects the meaning of the verdict is fixed by the
policy before any candidate is evaluated and is bound by digest. Policy
well-formedness is the audit authority's responsibility (§2.3).

## 2. Policy document, payload, and identity

### 2.1 Structure

    policy_payload   : the unsigned content (all fields in §2.5). Contains NO digest field.
    policy_digest    := digest_v1( "pcfw.policy_payload.v1", to_cv(policy_payload) )
    policy_document  := { payload : policy_payload ; policy_digest : digest }

The digest is over the **payload only**, so there is no circularity. A candidate's
`policy_hash` is checked (tier B3) against
`digest_v1("pcfw.policy_payload.v1", to_cv(policy_payload))`.

The formal `Policy` `P` and the wire `policy_document` are carried by an
`AuditRequest`. `validate_campaign` (`VERDICT_SEMANTICS.md` §5) runs **once** per
pipeline — `parse_commitment` + Ed25519 auth + manifest/ledger/record binding,
frozen first-failure precedence, **charging each `fuel_schedule` phase before its
work**, no model call. Context resolution begins with one F.3 `load_context` fetch
producing an immutable `loaded_context` (model/preproc/inference-spec bytes + the
pure `ctx`), threaded as data. Its result and the transcript feed the pure core
`assess_validated`, which **never re-validates** and returns a `certificate` for
every verdict (`CLAIM_AND_DEFINITIONS.md` §3.2). Two entry points build the
`transcript_source`: **live** (`validate_campaign` → gated capture →
`assess_validated (` `LiveTranscript …``)`, §2.4 step 7) and **offline replay**
(`validate_campaign` → `parse_transcript` of the retained wire bytes → reconstruct
`context_bundle` → `assess_validated (` `OfflineParse …``)`, §9). Every verdict
object is a pure total function of `(trusted_inputs, validation_result,
transcript_source)`.

### 2.2 Canonicalisation and hashing — normative

#### 2.2.1 `canonical_value`

A tree of exactly these node kinds: `object` (unordered `string → canonical_value`
members), `array` (ordered), `string` (Unicode scalar values), `integer`
(arbitrary precision), `boolean`, `null`. **No other kind** (no float, no date,
no binary blob).

#### 2.2.2 `canonicalise_v1 : canonical_value → bytes`

UTF-8 output, no whitespace:

- `object` → `{` then members in ascending key order, `,`-separated, each
  `canonicalise_v1(key):canonicalise_v1(value)` with one `:`, then `}`. Key order
  = byte-wise ascending comparison of the keys' UTF-8 (= code-point order).
- `array` → `[` elements in given order (significant), `,`-separated, `]`.
- `string` → `"` then the characters with **exactly** these escapes: `"`→`\"`,
  `\`→`\\`, U+0008→`\b`, U+0009→`\t`, U+000A→`\n`, U+000C→`\f`, U+000D→`\r`, and
  every remaining code point in U+0000–U+001F→`\u00xx` (lowercase hex). Every
  other character (incl. all non-ASCII) is raw UTF-8 — **no** `\uXXXX` for code
  points ≥ U+0020, **no** `\/`. Then `"`.
- `integer` → decimal ASCII matching `0 | -?[1-9][0-9]*`.
- `boolean` → `true` / `false`; `null` → `null`.

#### 2.2.3 Parsing rules (a violation of 1–4 for a policy document is a load failure, §2.3)

1. valid UTF-8;
2. no `object` has two members with equal (unescaped) keys;
3. an absent field is **omitted**, never `null` (`null` only where a field's
   schema lists it — v0: `expiry`);
4. an `integer` literal matches `0 | -?[1-9][0-9]*` (no `+`, no leading zeros, no
   `-0`).

#### 2.2.4 Two domain-separated hash families

    digest_v1(tag, v : canonical_value)  :=  SHA256_hex( utf8(tag) ‖ 0x1F ‖ canonicalise_v1(v) )
    digest_bytes_v1(tag, b : bytes)      :=  SHA256_hex( utf8(tag) ‖ 0x1F ‖ b )

`0x1F` is one UNIT SEPARATOR byte. A raw `0x1F` byte never occurs in
`canonicalise_v1` output — a U+001F code point inside a string is escaped as the
six ASCII characters `\u001f` (per §2.2.2) — so the delimiter is unambiguous.
`SHA256_hex` is SHA-256, lowercase hex. **Every digest in the system is one of
these two forms, with a type-specific tag.**

| Object | Family | Tag |
|---|---|---|
| policy payload | `digest_v1` | `pcfw.policy_payload.v1` |
| parsed candidate (semantic) | `digest_v1` | `pcfw.candidate.v1` |
| submission-check result (advisory) | `digest_v1` | `pcfw.submission_check_result.v1` |
| campaign record | `digest_v1` | `pcfw.campaign_record.v1` |
| campaign manifest | `digest_v1` | `pcfw.campaign_manifest.v1` |
| assessment certificate | `digest_v1` | `pcfw.certificate.v1` |
| verifier configuration | `digest_v1` | `pcfw.verifier_config.v1` |
| execution transcript (canonical, typed) | `digest_v1` | `pcfw.exec_transcript.v1` |
| execution transcript (raw wire bytes) | `digest_bytes_v1` | `pcfw.exec_transcript_wire.v1` |
| generic canonical value (test only) | `digest_v1` | `pcfw.canonical_value.v1` |
| raw candidate submission (wire bytes) | `digest_bytes_v1` | `pcfw.candidate_submission.v1` |
| model artifact | `digest_bytes_v1` | `pcfw.model_artifact.v1` |
| inference specification (its canonical file bytes) | `digest_bytes_v1` | `pcfw.inference_spec.v1` |
| preprocessing specification | `digest_bytes_v1` | `pcfw.preprocessing_spec.v1` |
| export toolchain descriptor | `digest_bytes_v1` | `pcfw.export_toolchain.v1` |
| generator descriptor | `digest_bytes_v1` | `pcfw.generator.v1` |
| campaign configuration descriptor | `digest_bytes_v1` | `pcfw.campaign_config.v1` |
| extracted kernel binary | `digest_bytes_v1` | `pcfw.kernel_binary.v1` |
| verifier binary | `digest_bytes_v1` | `pcfw.verifier_binary.v1` |

So `model_artifact_digest := digest_bytes_v1("pcfw.model_artifact.v1", <file bytes>)`;
`submission_digest := digest_bytes_v1("pcfw.candidate_submission.v1", <wire bytes>)`;
`semantic_candidate_digest := digest_v1("pcfw.candidate.v1", to_cv(parsed_candidate))`;
`campaign_manifest_digest := digest_v1("pcfw.campaign_manifest.v1", to_cv(manifest))`.

#### 2.2.5 `to_cv` — complete mappings

**Primitives.** `Z`→`integer`; `bool`→`boolean`; `string`→`string`;
`Vec Z n`→`array` of `integer` in index order; `digest` (hex string)→`string`;
`option None`→the key is **omitted**, `option (Some x)`→`to_cv(x)`;
`list`→`array` in list order.

**Sum-type constructors.** No payload → the `string` of the constructor name in
`lower_snake_case` (`` `VALID_WITNESS ``→`"valid_witness"`,
`XNotInDomain`→`"x_not_in_domain"`). With a payload →
`{"k":"<name>","v":<to_cv(payload)>}`.

**Records** → an `object` keyed by field name in `lower_snake_case`, each value
`to_cv` of the field, omitting excluded fields and `None` options. `nat` → the
`integer` of its value. Every hashed type and every type nested in one:

| type | `to_cv` |
|---|---|
| `policy_payload` | the §2.5 fields, each mapped by the row for its type below; `expiry`→`null` when unset; all other absent fields omitted |
| `input_schema` | `{n_in:<int>, components:[{integer_type:<string>, scale:<int>}…]}` (one entry per component, index order; `integer_type` ∈ the §2.5.1 closed registry) |
| `model_input_schema` | `{n_pre:<int>}` |
| `domain` | `{lo:<array of integer>, hi:<array of integer>}` (index order; equal length `n_in`) |
| `quantisation` | `{widths:<array of integer>}` when per-component, or `{width:<integer>, uniform:true}` when scalar-uniform |
| `quantisation_rounding_mode` / `model_binding_method` / `target_binding_method` / `model_format` / `representation_id` | the `string` of the value (`quantisation_rounding_mode` ∈ `"floor"`/`"ceil"`/`"half_even"`/`"toward_zero"`) |
| `expected_observation_range` | `{lo:<array of integer>, hi:<array of integer>}` (index order, length `n_obs`) |
| `numerical_semantics` | `{representation:"integer_z", prohibited:[<string>…]}` (the §5 list, ascending) |
| `semantic_bounds` | `{n_in:<int>, n_pre:<int>, n_obs:<int>}` |
| `justification` | `{operational_resolution_rationale:<string>, constructed_positive_control:<boolean>}` — a **structured** object, not free text |
| `predicate_id` / `predicate_version_or_digest` / `policy_id` / `policy_version` / `audit_instance_id` / `canonicalisation_version` / `model_format` / `target_binding_method` / `model_binding_method` / `representation_id` | scalar `string` (or `integer` for `policy_version`, `bundle_schema_version`) of the value |
| `expiry` | `null` when unset, else the `string` value |
| `parsed_candidate` | keys `candidate_id`, `policy_hash`, `schema_version`, `x`, `y` **only** — `search_metadata`, `hints` excluded (bound by `submission_digest`) |
| `context_descriptor` | `{model_artifact_digest, inference_spec_digest, preprocessing_digest}` (hex strings) |
| `check_outcome` | `"pass"` / `"fail"` / `"not_evaluated"` |
| `finding` | `{check_id, outcome:<check_outcome>, reason:<constructor name>|omitted, offending:<to_cv>|omitted}`. A stage finding's `check_id` is from the `VERDICT_SEMANTICS.md` §2 stage set. A `finding` in `replay_result.record_findings` instead has `check_id` from the closed advisory family (§2), `offending` always omitted, and `reason` a fixed lower-snake-case **token** (not a constructor name) — see `PHASE_1_ADVISORY_FINDING_IDS_ERRATUM.md` |
| `witness_outcome` / `candidate_outcome` | the constructor rule: no payload → `lower_snake_case` string; with payload → `{"k":"<name>","v":"<reason name>"}` (the payload is always a `b_/c_/o_reason` — a nullary constructor, so `"v"` is its `lower_snake_case` string). `` `VALID_WITNESS `` in an advisory `submission_check_result` carries no payload; the certificate's `witness_data` is bound separately |
| `verifier_config` | `{bundle_limits:{max_wire_bytes:<int>, max_nesting_depth:<int>, max_parser_recursion:<int>, max_transcript_bytes:<int>}, fuel_schedule:{commitment_parse_fuel:<int>, signature_verify_fuel:<int>, manifest_bind_fuel:<int>, record_bind_fuel:<int>, preflight_fuel:<int>, stage1_base_fuel:<int>, stage1_per_byte_fuel:<int>}, per_candidate_limits:{max_fuel_per_candidate:<int>}, campaign_limits:{max_candidates:<int>, max_fuel:<int>}, trust_anchor:{authorised_signers:[<string>… ascending, no repeat], keys:[{signer:<string>, public_key:<string 64-hex>}… by signer ascending, exactly one per authorised signer]}}` |
| `witness_data` | `submission_index`(`integer`), `submission_digest`, `semantic_candidate_digest`, `x`, `y`, `preproc_x`, `preproc_y`, `o_x`, `o_y`, `quantised_o_x`, `quantised_o_y` (all `Vec Z`→`array`), `phi_x`, `phi_y` (`boolean`), `stage2_findings` (array) |
| `exec_outcome` | `"exhausted"` / `{"k":"ok","v":<array of integer>}` / `{"k":"failed","v":<string>}` |
| `call_key` | `{phase:<"context_probe" \| {"k":"stage2","v":<int>}>, role:<"probe"\|"x"\|"y">, repeat:<int>}` |
| `call_request` | `{key:<call_key>, input:<array of integer>}` — what the verifier hands the runner; the wrapper builds the `exec_event` from it |
| `exec_event` | `{key:<call_key>, input:<array of integer>, outcome:<exec_outcome>}` — **no fuel field** |
| `exec_transcript` | `array` of `to_cv(exec_event)` in call order. **Live**: `capture` yields this typed value directly (tagged `LiveCapture`). **Offline**: `parse_transcript : verifier_config → bytes → `Malformed of {reason:<string>, wire_digest:<digest>} \| `Wellformed of {transcript:<exec_transcript>, wire_digest:<digest>}` — atomic; `wire_digest := digest_bytes_v1("pcfw.exec_transcript_wire.v1", <bytes>)` on both branches; `` `Malformed `` if `\|bytes\| > bundle_limits.max_transcript_bytes` or any event is ill-formed |
| `loaded_context` | not serialised as bytes — represented by its `context_descriptor` (which O1/O2 check the `*_bytes` against); `ctx` holds functions (F.3 well-formed) |
| `context_bundle` | `"ctx_not_needed"` / `{"k":"ctx_unavailable","v":<ctx_reason>}` / `{"k":"ctx_loaded","v":<context_descriptor>}` |
| `validation_result` | `{"k":"invalid","v":{reason:<integrity_reason>, fuel:<fuel_ledger>, evidence:<commitment_evidence>}}` / `{"k":"fuel_obstructed","v":{fuel:<fuel_ledger>, evidence:<commitment_evidence>}}` / `{"k":"valid","v":{fuel:<fuel_ledger>}}` (the `authenticated_campaign` payload holds functions — bound by `M`/`mc` digests, not serialised) |
| `transcript_evidence` | `"no_transcript"` / `{"k":"malformed_transcript","v":{reason:<string>, wire_digest:<digest>}}` / `{"k":"live_capture","v":{transcript_digest:<digest string>}}` / `{"k":"offline_transcript","v":{transcript_digest:<digest string>, wire_digest:<digest string>}}` — `transcript_digest = digest_v1("pcfw.exec_transcript.v1", to_cv(tr))` |
| `assessment_outcome` | `{"k":"inadmissible"\|"exact"\|"obstructed","v":<certificate>}` / `{"k":"underdetermined","v":<campaign_report>}` |
| `context_state` | `"no_context_needed"` / `{"k":"context_unresolved","v":{reason:<ctx_reason>, findings:[<finding>…]}}` / `{"k":"context_resolved","v":{context_digests:<context_descriptor>, findings:[<finding>…]}}` / `"context_bundle_inconsistent"` — `resolved_context` is represented by its `context_descriptor` |
| `pending_submission` | `{submission_index:<int>, submission_digest, semantic_candidate_digest, candidate:<parsed_candidate>, stage1_findings:[<finding>…]}` |
| `stage1_slot` / `stage2_slot` | `{submission_index:<int>, result:<"not_run" \| {"k":"done","v":<stage1_result \| stage2_result>}>}` |
| `fuel_ledger` | `{budget:<int>, consumed:<int>}` |
| `integrity_reason` | constructor rule: `{"k":"bad_commitment_encoding","v":<string>}` / `"signer_not_authorised"` / `"signature_invalid"` / `"manifest_policy_mismatch"` / `"manifest_audit_instance_mismatch"` / `"manifest_context_mismatch"` / `{"k":"ledger_mismatch","v":{index:<int>}}` / `{"k":"record_identity_mismatch","v":{field:<string>}}` / `"completeness_malformed"` |
| `campaign_obstruction` | `{"k":"record_integrity","v":<integrity_reason>}` / `"validation_fuel_exhausted"` / `{"k":"transcript_malformed","v":{reason:<string>, wire_digest:<digest>}}` / `{"k":"context_obstruction","v":<ctx_reason>}` / `"campaign_fuel_exhausted"` / `"campaign_candidate_count_exceeded"` / `"inconsistent_context_bundle"` / `{"k":"witness_obstruction","v":{primary_index:<int>, primary_reason:<o_reason>, other_indices:[<int>…]}}` |
| `commitment_evidence` | `{"k":"unparsed_commitment","v":<manifest_commitment_wire>}` / `{"k":"parsed_commitment","v":<digest string>}` / `{"k":"authenticated_commitment","v":<digest string>}` |
| `replay_input` | `{"k":"invalid_fuel","v":<fuel_ledger>}` / `{"k":"replay_done","v":<replay_result>}` — what `build_certificate` receives |
| `campaign_record_summary` | `{campaign_id, audit_instance_id, policy_hash, manifest_digest, completeness:<completeness_status>}` |
| `replay_result` | `{stage1:[<stage1_slot>…], context:<context_state>, stage2:[<stage2_slot>…], fuel:<fuel_ledger>, clo:<campaign_obstruction>|omitted, record_findings:[<finding>…]}` |
| `campaign_report` | `{manifest_digest, policy_digest, context_digests:<context_descriptor>, verifier_config_digest, transcript_evidence:<transcript_evidence>, fuel_ledger, replay:<replay_result>, record:<campaign_record_summary>, assumptions:[<string>…]}` |
| `rejection_report` | `{submission_index:<int>, submission_digest, reason:<b_reason>, findings:[<finding>…]}` |
| `submission_check_result` | every field **except any digest of itself**: `submission_index` (`integer`), `submission_digest`, `candidate_id`|omitted, `semantic_candidate_digest`|omitted, `outcome`, `findings` (array) |
| `resource_budget` | `{max_candidates:<int>|omitted, max_wall_clock_seconds:<int>|omitted, max_memory_bytes:<int>|omitted, max_per_candidate_wall_clock_seconds:<int>|omitted, max_per_candidate_memory_bytes:<int>|omitted}` |
| `termination_reason` | constructor: `"exhausted"` / `"budget_reached"` / `"manual_stop"` / `{"k":"error","v":"<string>"}` |
| `limitation` | `{kind:<string>, detail:<string>}` |
| `completeness_certificate` | `{scheme:<string>, body:<the canonical_value verbatim>}` |
| `completeness_status` | `"unknown"` / `{"k":"incomplete","v":[<limitation>…]}` / `{"k":"complete","v":<completeness_certificate>}` |
| `campaign_failure` | `{submission_index:<int>|omitted, kind:<string>, detail:<string>}` |
| `obstruction` | `{cause:<string>, detail:<string>, repair_obligation:<string>}` |
| `campaign_manifest` | `{audit_instance_id, campaign_id, context_digests, policy_hash, submission_digests:[<string>…] (submission order, multiplicity kept)}` |
| `campaign_record` | every field **except any `digest_v1`/`digest_bytes_v1` of the record itself**; `manifest_digest` **is included** (it binds the record to the parsed `mc`); `recorded_results`→array of `to_cv(submission_check_result)`; `completeness`→`to_cv(completeness_status)` |
| `certificate` | see §2.2.6 |

A record or constructor not listed is **not hashed in v0**; a later version that
hashes it must add its `to_cv` here first.

#### 2.2.6 The `certificate` type

The certificate has **no standalone `verdict` field**: the verdict is a total
function of the body, `verdict(`Inadmissible _) = INADMISSIBLE`,
`verdict(`Exact _) = EXACT`, `verdict(`Obstructed _) = OBSTRUCTED`
(`VERDICT_SEMANTICS.md` §9).

    certificate := {
      policy_digest       : digest ;
      commitment_evidence : commitment_evidence ;   (* UnparsedCommitment (BadCommitmentEncoding) |
                                                       ParsedCommitment mc.digest (SignerNotAuthorised /
                                                       SignatureInvalid) | AuthenticatedCommitment mc.digest *)
      transcript_evidence : transcript_evidence ;   (* NoTranscript (validation obstruction) |
                                                       MalformedTranscript {reason ; wire_digest} |
                                                       LiveCapture {transcript_digest}   ((CAP1) applies) |
                                                       OfflineTranscript {transcript_digest ; wire_digest}   ((REP1) only) *)
      context_digests     : context_descriptor ;    (* = ac.M.context_digests; binds the loaded_context bytes via O1/O2 *)
      verifier_config_digest : digest ;
      fuel_model_digest   : digest ;
      fuel_ledger         : fuel_ledger ;      (* vr.fuel on an obstruction branch; rr.fuel on the replay branch *)
      verifier_digest     : digest ;
      kernel_digest       : digest ;
      rocq_commit         : string ;
      extraction_assumptions : string list ;
      execution_chain_descriptor : string ;
      configured_limits : limit_id list ;
      fired_limits      : limit_id list ;
      assumptions       : string list ;        (* incl. faithful_transcript for `Inadmissible *)
      body              : cert_body ;
    }
    cert_body :=
      | `Inadmissible of { primary : witness_data ; additional_valid_witness_indices : nat list ;
                           all_findings : finding list }
      | `Exact of { completeness : completeness_certificate }   (* not produced in v0 *)
      | `Obstructed of { obstruction : campaign_obstruction ; failed_obligation : string ;
                         context_findings : finding list }

    cert_body_input :=
      | InadmissibleInput of { primary : witness_data ; others : nat list ; all_findings : finding list }
      | ExactInput        of { completeness : completeness_certificate }
      | ObstructedInput   of { obstruction : campaign_obstruction ; failed_obligation : string ;
                               context_findings : finding list }

    build_certificate :
      cert_body_input → trusted_inputs → replay_input → transcript_evidence → commitment_evidence → certificate
      (* replay_input = `InvalidFuel fuel_ledger  on an obstruction branch;  `ReplayDone replay_result  otherwise *)

    assessment_outcome := Inadmissible of certificate | Exact of certificate
                        | Obstructed   of certificate | Underdetermined of campaign_report
      (* every constructor except Underdetermined carries a certificate *)

    witness_data := {
      submission_index : nat ; submission_digest : digest ; semantic_candidate_digest : digest ;
      x : Vec Z n_in ; y : Vec Z n_in ;
      preproc_x : Vec Z n_pre ; preproc_y : Vec Z n_pre ;
      o_x : Vec Z n_obs ; o_y : Vec Z n_obs ;
      quantised_o_x : Vec Z n_obs ; quantised_o_y : Vec Z n_obs ;
      phi_x : bool ; phi_y : bool ;
      stage2_findings : finding list ;
    }

`to_cv(certificate)` and `to_cv` of each nested type follow §2.2.5;
`certificate_digest := digest_v1("pcfw.certificate.v1", to_cv(certificate))`.
`to_cv(verifier_config)` (tag `pcfw.verifier_config.v1`) and `to_cv(exec_transcript)`
(tag `pcfw.exec_transcript.v1`) are defined in the §2.2.5 table; both are closed
and order-deterministic (`verifier_config.trust_anchor.keys` and `authorised_signers`
ordered by signer ascending with no repeat; `exec_transcript` in capture order).

`limit_id` is the **closed** identifier set (§7.2.4); `configured_limits` and
`fired_limits` are `limit_id` lists in ascending order.

#### 2.2.7 Normative digest vectors

Bytes hashed = `utf8(tag) ‖ 0x1F ‖ payload` (canonical bytes for `digest_v1`, raw
bytes for `digest_bytes_v1`).

| tag | payload (ASCII) | digest |
|---|---|---|
| `pcfw.policy_payload.v1` | `{"audit_instance_id":"ai-0001","bundle_schema_version":1,"canonicalisation_version":"canonicalise_v1","expiry":null,"policy_id":"demo","policy_version":1}` | `14e86aab02f815f8f5fefafc5501e29153b6a0d8a413cf11595312e2e3d05eaf` |
| `pcfw.canonical_value.v1` | `{"a":[1,2,3],"b":"x\"y\\z","c":-5,"d":true,"e":null}` — the `b` string is the 5 characters `x`, `"`, `y`, `\`, `z` | `b64f81d5e627b9287fb4aadfd270ebc10083fe65d76b46b82f5ea6e325292d91` |
| `pcfw.candidate.v1` | `{"candidate_id":"c-1","policy_hash":"fb0105...","schema_version":1,"x":[0,0],"y":[0,1]}` | `70faafcead2ee8b26b67dc61aa88c1e8284392668d0ebd2f7e52759e03873fd4` |
| `pcfw.candidate_submission.v1` | the 5 raw bytes `hello` | `9ec2679ac0e8eb8d1e9e506657c6b547412cdde54c796c93d14183a24af37b9d` |
| `pcfw.campaign_manifest.v1` | `{"audit_instance_id":"ai-0001","campaign_id":"cmp-1","context_digests":{"inference_spec_digest":"ii","model_artifact_digest":"mm","preprocessing_digest":"pp"},"policy_hash":"fb0105","submission_digests":["d1","d2"]}` | `0714f76c7269b6e5eaa6e8348a0e84e527db842ffd0552653d49263a452bbe80` |
| `pcfw.submission_check_result.v1` | `{"candidate_id":"c-1","findings":[{"check_id":"C1","outcome":"fail","reason":"inputs_equal"}],"outcome":{"k":"accepted","v":{"k":"not_a_witness","v":"inputs_equal"}},"submission_digest":"9ec2679a","submission_index":0}` | `90f8c82050395ddaf4d3d4a887c97018cbf0d9ea9ab0ed660708c8841d75565a` |
| `pcfw.generator.v1` | the raw bytes `pcfw-search/0.1` | `829ccc0fdce3e6ac0e70dd65d3f5090190db33e666af5e144766d572daefdd2c` |

**These are hash-layer conformance vectors.** Each fixes the
`canonicalise_v1` + `digest_v1` / `digest_bytes_v1` computation for the byte string
shown — it is **not** an assertion that the payload is a schema-valid instance of
its named domain type (`pcfw.policy_payload.v1` here omits mandatory §2.5 fields;
several digest fields are shortened or elided). Schema-valid end-to-end example
bundles are an implementation-phase deliverable (§10). What is normative here is
the transform from the exact bytes in the middle column to the digest in the
right.

### 2.3 Load-time validity (authority-side)

The policy document does not load, and no assessment runs, if: any §2.2.3 parsing
rule is violated; the recomputed `policy_digest` disagrees with
`policy_document.policy_digest`; `canonicalisation_version` is not recognised; any
`w_i ≤ 0`; any `s_k ≤ 0` in the inference specification; the inference spec's
per-layer shapes disagree; the inference spec has no `probe_input` /
`probe_observation` at `representation_id` (§2.5.2) or no `model_call_fuel`
(§2.5.3); `representation_id` names no enumerated checkpoint; any
`input_schema.components[i].integer_type` is not in the §2.5.1 closed registry;
`predicate_id` is not in the closed registry; or `n_pre` disagrees with the
preprocessing spec's output arity. These are authority-side errors — **not**
candidate faults, **not** bundle rejections.

Separately, a **`verifier_config` is rejected at load** (operator-side) if
`trust_anchor.authorised_signers` has a repeat, a listed signer has zero or more
than one key, any `public_key` is not 64 lowercase-hex characters, any
`fuel_schedule` (`commitment_parse_fuel`, `signature_verify_fuel`,
`manifest_bind_fuel`, `record_bind_fuel`, `preflight_fuel`, `stage1_base_fuel`,
`stage1_per_byte_fuel`) / `bundle_limits` (incl. `max_transcript_bytes`) /
`per_candidate_limits` / `campaign_limits` field is absent, **or
`campaign_limits.max_fuel < validation_fuel_ok`** (`= commitment_parse_fuel +
signature_verify_fuel + manifest_bind_fuel + record_bind_fuel`). The last rule
makes `` `FuelObstructed `` from `validate_campaign` provably unreachable
(`VERDICT_SEMANTICS.md` §5). A malformed `manifest_commitment_wire` (bad-length or
non-hex `digest` / `signature`) is **not** a config defect — it is an `MCW` parse
failure inside `validate_campaign` (`BadCommitmentEncoding`, §2.4.1). A malformed
wire **transcript** is likewise not a config defect — `parse_transcript`
(offline only) fails the whole transcript → `OBSTRUCTED` / `TranscriptMalformed
{reason ; wire_digest}` (`VERDICT_SEMANTICS.md` §3.1, §6.7).

### 2.4 Commitment procedure and chronology

**"Commit"** = the bytes are finalised, their `digest_v1` (structured) or
`digest_bytes_v1` (raw) is computed, and that digest is recorded in the project's
immutable record — a **signed** git tag over the digest. A signed commitment
`X` yields `X.digest` and a verifiable `X.signature`. After a policy or artefact
commit the bytes cannot change without a new `policy_version` **and** a new
`audit_instance_id`.

Sequence:

1. **Choose the semantic-policy fields** (`input_schema`, `model_input_schema`,
   `domain`, `quantisation`, `quantisation_rounding_mode`,
   `expected_observation_range`, `predicate_id`/version, `bundle_schema_version`,
   `semantic_bounds`, `numerical_semantics`, `canonicalisation_version`).
2. **Produce and commit the model chain** (all before the search): export the
   integer weights → commit → `model_artifact_digest`; write the canonical
   inference specification → commit → `inference_spec_digest`; write the canonical
   `N_P` specification → commit → `preprocessing_digest`; commit the
   `export_toolchain` descriptor.
3. **Assemble and commit the policy document** (before the search): `policy_payload`
   = step-1 fields **+** step-2 digests **+** `audit_instance_id`, `policy_id`,
   `policy_version`, `model_format`, `representation_id`, `justification`,
   `expiry`. Run §2.3 load validation. Compute
   `policy_digest = digest_v1("pcfw.policy_payload.v1", to_cv(policy_payload))`.
   Commit the `policy_document`.
4. **Open the append-only ledger** — a growing list of `submission_digest`s in
   arrival order (`TRUST_BOUNDARY.md` §F.3).
5. **Run the untrusted search**; each `candidate_submission` (raw bytes) is
   appended to the ledger as it arrives.
6. **Close the campaign.** Build `campaign_manifest M` from the ledger
   (`campaign_id`, `audit_instance_id`, `policy_hash`, `context_digests`,
   `submission_digests` in arrival order). Compute
   `campaign_manifest_digest = digest_v1("pcfw.campaign_manifest.v1", to_cv(M))`,
   sign `utf8(<that digest>)`, and publish the `manifest_commitment_wire MCW`
   (§2.4.1).
7. **Assess (LIVE)** — **(a)** `vr := validate_campaign ti` (**once**; pure —
   `parse_commitment MCW`, Ed25519 auth, manifest/ledger/record binding, frozen
   first-failure precedence, **charging each `fuel_schedule` phase before its
   work**; no model call). On `` `Invalid `` (or the unreachable `` `FuelObstructed ``)
   `assess_validated` emits an obstruction certificate (`vr.fuel`, the matching
   `commitment_evidence`, `transcript_evidence = NoTranscript`) and stops. **(b)**
   On `` `Valid {campaign = ac ; fuel = L0}`` run the **gated capture**
   (`VERDICT_SEMANTICS.md` §6.4): candidate-count check first; for each submission
   *charge `cost_stage1` then run `stage1_check`* (**a stage-1 `charge` `` `Over ``
   is a terminal return** — `clo = CampaignFuelExhausted`, no context, no further
   calls); then `load_context env (context_descriptor ac)` (F.3 fetch, once); then
   *charge `preflight_fuel` then run `preflight_O1_O2(lc)`*; then *charge
   `model_call_fuel` then issue the probe*; then per pending candidate *charge
   `cost_candidate` then issue its four calls*. `capture` yields
   `{ transcript ; issued ; clo ; ctx_bundle }`. **(c)** `assess_validated ti vr
   (` `LiveTranscript { transcript = co.transcript ; ctx_bundle = co.ctx_bundle }``)`
   = `replay ac co.ctx_bundle … L0 co.transcript` then `decide`
   (`transcript_evidence = LiveCapture`). The replay package (`§9`) ships `M`,
   `MCW`, `verifier_config`, the model/preproc/inference-spec bytes, the serialised
   wire transcript, every submission, and the campaign record.

Every quantity that fixes the *meaning* of a verdict is committed before the
search (steps 1–3). The ledger records what the search did (steps 4–6); its
commitment `MCW` is authenticated in step 7(a) **before any model call**, so an
unauthenticated campaign never triggers model execution.

#### 2.4.1 The manifest-commitment scheme (frozen for v0)

**Wire type** (as retrieved) and **validated type** (after parsing):

    manifest_commitment_wire := { digest : string ; signer : string ; signature : string }
    manifest_commitment      := { digest : digest ; signer : string ; signature_bytes : bytes(64) }

    parse_commitment : manifest_commitment_wire
      → [ `BadEncoding of string | `Parsed of manifest_commitment ]

`parse_commitment` succeeds iff `digest` is exactly 64 lowercase-hex characters
and `signature` is exactly 128 lowercase-hex characters; it then sets `digest` to
that hex string and `signature_bytes` to the 64 decoded bytes. A failure carries a
short reason string and becomes `integrity_reason = BadCommitmentEncoding <msg>`
in `validate_campaign` step 1 (`VERDICT_SEMANTICS.md` §5).

    authenticate_manifest(ta : trust_anchor, mc : manifest_commitment, M : manifest) : bool :=
        mc.digest = digest_v1("pcfw.campaign_manifest.v1", to_cv(M))
      ∧ mc.signer ∈ ta.authorised_signers
      ∧ (match key_of ta mc.signer with
         | Some k → ed25519_verify(k, mc.signature_bytes, utf8(mc.digest))
         | None   → false)

`validate_campaign` (`VERDICT_SEMANTICS.md` §5) splits this into ordered
`integrity_reason` steps — `SignerNotAuthorised` before `SignatureInvalid` (which
also covers `key_of = None`, a bad signature, and `mc.digest ≠ digest_v1(…)`).
`charge` is applied **before** each phase: `commitment_parse_fuel` before step 1,
`signature_verify_fuel` before step 3, `manifest_bind_fuel` before step 4,
`record_bind_fuel` before step 7. `validation_fuel(reason)` = the sum of the
phases charged before the failure; `validation_fuel_ok = commitment_parse_fuel +
signature_verify_fuel + manifest_bind_fuel + record_bind_fuel`. **All three**
`validation_result` branches carry a `fuel_ledger` — `{budget =
campaign_limits.max_fuel ; consumed = validation_fuel(...)}` — so the obstruction
certificate records a **truthful** `consumed`. A `charge` returning `` `Over ``
during validation yields `` `FuelObstructed `` (unreachable for a loaded config,
§2.3). `commitment_evidence`: `UnparsedCommitment` for `BadCommitmentEncoding`;
`ParsedCommitment mc.digest` for `SignerNotAuthorised` / `SignatureInvalid`;
`AuthenticatedCommitment mc.digest` for every later integrity failure and every
`` `Valid `` outcome.

- **Signed message:** exactly `utf8(mc.digest)` — the 64 ASCII characters of the
  lowercase-hex SHA-256 string, no trailing newline, no length prefix. Identical
  bytes on the signing side. `VERDICT_SEMANTICS.md` §5 uses this same function
  over the **parsed** `manifest_commitment`.
- **Signature scheme:** **PureEdDSA using Ed25519 (edwards25519), RFC 8032.**
- **Wire encodings (frozen):** `signer` is a UTF-8 string id;
  `trust_anchor.keys[*].public_key` is the 32-byte Ed25519 public key as 64
  lowercase-hex ASCII characters; `signature` is the 64-byte Ed25519 signature as
  128 lowercase-hex ASCII characters. Any wrong length or non-hex character →
  `parse_commitment` returns `` `BadEncoding `` (→ `validate_campaign` step 1 fails
  → `OBSTRUCTED`).
- **Unique-key rule:** `verifier_config` is well-formed only if
  `trust_anchor.authorised_signers` has **no repeat** and every listed signer has
  **exactly one** key (§2.3); `key_of : trust_anchor → string → option
  ed25519_pubkey` is therefore unambiguous.
- **Signer:** the audit authority's release identity (the same key that signs the
  policy-document git tag, §2.4). One signer in v0.
- **Trust anchor:** `ta := verifier_config.trust_anchor`, a trusted input
  (`TRUST_BOUNDARY.md` §F.3), bound into the certificate by
  `verifier_config_digest`. The immutable record that the tag was published is the
  project's signed-tag history.

### 2.5 Mandatory payload fields

| Field | Notes |
|---|---|
| `canonicalisation_version` | e.g. `canonicalise_v1` |
| `policy_id`, `policy_version` | identity |
| `audit_instance_id` | one assessment context |
| `bundle_schema_version` | accepted wire schema (tier B1 equality target) |
| `model_artifact_digest` | `digest_bytes_v1("pcfw.model_artifact.v1", <file>)` |
| `model_format` | integer model format identifier |
| `inference_spec_digest` | `digest_bytes_v1("pcfw.inference_spec.v1", <file>)` — sole source of truth for per-layer `Mat`/`Vec` shapes, `s_k`, `rescale_rounding_mode`, `ReLU` placement, op order, the enumerated observable checkpoints with their `Vec Z n_obs` types, **and the O3 probe** `probe_input : Vec Z n_pre` with its expected `probe_observation : Vec Z n_obs` at `representation_id` (§2.5.2) |
| `export_toolchain_digest` | `digest_bytes_v1("pcfw.export_toolchain.v1", <descriptor>)` (informational) |
| `preprocessing_digest` | `digest_bytes_v1("pcfw.preprocessing_spec.v1", <file>)` — the committed pure `N_P : Vec Z n_in → Vec Z n_pre` |
| `input_schema` | `n_in`, and per component an `integer_type` (§2.5.1 closed registry) and a `scale` for `X_raw` |
| `model_input_schema` | `n_pre` for `X_model` |
| `domain` | axis-aligned box on `Vec Z n_in`: `lo`, `hi` per component |
| `representation_id` | **selector** — one checkpoint enumerated by the inference specification; shape/type come from the spec |
| `quantisation` | bin-width `Vec Z n_obs` (or scalar + uniform flag), each `w_i > 0` (§4) |
| `quantisation_rounding_mode` | `Floor \| Ceil \| HalfEven \| TowardZero` (`CLAIM_AND_DEFINITIONS.md` §7.2) — a `Q_P` parameter, distinct from `rescale_rounding_mode` |
| `expected_observation_range` | validity bounds on the **raw** observation; not a clamp (§4.3) |
| `predicate_id`, `predicate_version_or_digest` | one constructor of the closed in-kernel registry |
| `model_binding_method` | v0: `independent_reexecution` |
| `target_binding_method` | v0: `in_kernel_registry` |
| `numerical_semantics` | §5 |
| `semantic_bounds` | §7.1 |
| `justification` | **structured**: `{operational_resolution_rationale : string, constructed_positive_control : bool}` (§2.2.5, §4.2) |
| `expiry` | `null` for the v0 offline demonstration (§8) |

`rescale_rounding_mode`, the observable-checkpoint shape/type, and the O3 probe
(§2.5.2) are content of the inference specification, bound transitively by
`inference_spec_digest`, not restated here; `representation_id` is a selector only
(§2.3 checks it at load).

### 2.5.1 Closed integer-type registry (for `input_schema.components[].integer_type`)

| `integer_type` | representable range `[lo, hi]` (inclusive) |
|---|---|
| `i8`  | `[-128, 127]` |
| `i16` | `[-32768, 32767]` |
| `i32` | `[-2147483648, 2147483647]` |
| `i64` | `[-9223372036854775808, 9223372036854775807]` |
| `u8`  | `[0, 255]` |
| `u16` | `[0, 65535]` |
| `u32` | `[0, 4294967295]` |

This registry is **closed** in v0. Tier **B5** checks that each candidate integer
literal, after the grammar check, is **representable in its component's declared
`integer_type`** — a wire-format well-formedness test. It is **not** a domain
check: membership in `D_P` is decided entirely by **C2 / C3** against `domain`
(which may be a strict sub-box of the type range). A component whose declared
`integer_type` is not in this table is a load-time authority error (§2.3).

### 2.5.2 The O3 probe

The inference specification binds a canonical `probe_input : Vec Z n_pre` and the
`probe_observation : Vec Z n_obs` it must produce at `representation_id`. During
the capture pass the verifier calls the runner once with key
`{phase = `ContextProbe ; role = `Probe ; repeat = 0}` on `probe_input`, appending
the `exec_event` to `tr`. `eval_O3` (`CLAIM_AND_DEFINITIONS.md` §3.2.3,
`VERDICT_SEMANTICS.md` §6.3) requires that probe event to satisfy
**`e.input = probe_input`** and `e.outcome = ` `Ok probe_observation ``, plus the
structural checkpoint-shape check. Both values are covered by
`inference_spec_digest`. The probe is issued **only after `preflight_O1_O2`
succeeds** (§6, `VERDICT_SEMANTICS.md` §6.4).

### 2.5.3 The forward-pass fuel constant

The inference specification binds `model_call_fuel : nat` — the exact integer
operation count of one forward pass from `X_model` to `representation_id`. Because
the model is a fixed-shape integer MLP (`CLAIM_AND_DEFINITIONS.md` §7.3),
`model_call_fuel` is a function of the layer shapes **only** — never of an input
value — so it is known before any call. It is covered by `inference_spec_digest`;
the certificate's `fuel_model_digest` binds `model_call_fuel` together with
`verifier_config.fuel_schedule` (§7.2). This is what lets the gated capture
`charge` each call's fuel **before** issuing it (§6.4).

## 3. Candidate submission, parsing, and the two digests

### 3.1 Submission vs parsed candidate

    candidate_submission := raw wire bytes                     (* what the generator sends *)

    parse_candidate : verifier_config → policy_document → candidate_submission
                    → [ `REJECTED_BUNDLE of b_reason | `Parsed of parsed_candidate ]

`parse_candidate` is the **tier-B helper** invoked by `stage1_check`
(`VERDICT_SEMANTICS.md` §4.1): on `` `Parsed pc `` the stage continues with
C1/C2/C3/C5 and the overall `stage1_result.verdict` is `` `NotAWitness `` or
`` `Pending pc `` — `stage1_check` itself has no `` `Parsed `` constructor. It
takes `verifier_config` so its bounded parser can enforce B6 during the parse.

    parsed_candidate := {
      schema_version : int ;      (* = policy_payload.bundle_schema_version, else B1 *)
      policy_hash    : digest ;
      candidate_id   : string ;
      x, y           : Vec Z n_in ;
      search_metadata : search_metadata option ;   (* never evidence *)
      hints           : observation_hints option ; (* diagnostic only; separate log *)
    }

`parse_candidate` performs tier B (§6). Tier-B failures — invalid UTF-8, duplicate
keys, malformed structure, unrecognised or mismatched `schema_version`, prohibited
override field, unparseable `x`/`y`, malformed integer literal, `policy_hash`
mismatch, bundle-limit breach — are only expressible on **raw bytes**, hence
`parse_candidate` takes the submission, not a typed record.

### 3.2 Two digests

    submission_digest         := digest_bytes_v1("pcfw.candidate_submission.v1", <the raw wire bytes>)
    semantic_candidate_digest := digest_v1("pcfw.candidate.v1", to_cv(parsed_candidate))

- `submission_digest` binds the **exact bytes**, including `search_metadata` and
  `hints`; it exists for **every** submission, including rejected ones.
- `semantic_candidate_digest` binds only the authoritative parsed fields; it
  exists for **every successfully parsed submission** — `` `Parsed `` — whether
  its stage-1 verdict is `` `NotAWitness `` or `` `Pending `` (`stage1_result`
  and `pending_submission` both carry it).

The `INADMISSIBLE` certificate records **both**; "the exact candidate bundle" in
§8 means the `submission_digest`. Campaign manifests and records key on
`submission_digest`.

### 3.3 Prohibited fields

Tier-B2 rejection: any authoritative model, quantiser, tolerance, domain, or
target override; `domain_check_passed`, `equivalence_verified`,
`predicate_divergence_verified`, or similar. `hints` are excluded from the
semantic checker, from `(T1)`, and from the certificate's proof obligations.

The verifier reads `o_x`, `o_y` from the captured transcript (the agreeing
`` `Ok `` values) and computes `Q_P o_x`, `Q_P o_y`, `Φ_P x`, `Φ_P y` in-kernel;
all six go into `witness_data`.

## 4. Operational-resolution mechanism (version 0)

### 4.1 Definition

`Q_P : Vec Z n_obs → Vec Z n_obs`, component-wise
`q_i = rounddiv(o_i, w_i, quantisation_rounding_mode)`, `w_i > 0`, **no
saturation**. `rounddiv` is fully defined in `CLAIM_AND_DEFINITIONS.md` §7.2.
Proved: totality (at this type), determinism, `n_obs`-preservation.

### 4.2 Fixed before evaluation

`Q_P` and its parameters are committed in step 3 of the §2.4 procedure — after the
model chain and before the search. A deliberately collision-seeded quantiser
carries `justification.constructed_positive_control = true` (a Boolean field of the
structured `justification` object, §2.2.5).

### 4.3 Expected range is a validity check, not a clamp

`expected_observation_range` bounds the **raw** `o_x`, `o_y` before `Q_P`. A value
outside it is a tier-O5 obstruction — never a saturation into a collision.

## 5. Numerical semantics

- Wire form: decimal integers, declared component counts and shapes, declared
  row-major order. The parser (F.3) validates lengths and constructs `Vec`/`Mat`.
- Kernel representation: `Z` (extracted to a `zarith` big integer).
- Two independent rounding roles: `rescale_rounding_mode` (inference spec) for
  `rounddivᵥ(W^{(k)}·z^{(k)}+b^{(k)}, s_k, ·)`; `quantisation_rounding_mode`
  (policy) for `Q_P`.
- Model inference:
  `z^{(k+1)} = ReLU(rounddivᵥ(W^{(k)}·z^{(k)} + b^{(k)}, s_k, rescale_rounding_mode))`,
  `s_k > 0`, `ReLU(t) = max(0,t)`, exact integer matrix–vector product and bias
  add (`CLAIM_AND_DEFINITIONS.md` §7.3).
- Prohibited: host float comparison; float32/float64 conversion; NaN/infinity;
  associative float rearrangement; unconstrained-string metric; silent truncation
  or broadcasting; integer overflow or wrapping.

## 6. Evidence obligations — frozen evaluation order

`check_id` labels and the sequence are `VERDICT_SEMANTICS.md` §2; checks run in
that sequence, first failure's reason wins, unreached checks are
`` `NotEvaluated ``. O1–O3 are context-level (one `context_state`, carrying the
O1–O3 findings); a failure means no `` `Pending `` submission is checked further →
`clo = ContextObstruction …`. O6/O4/O5 are per-candidate, stage 2.

```text
GATED CAPTURE (VERDICT_SEMANTICS.md §6.4) / REPLAY (§6.5) — identical control flow.
Ledger L seeded with vr.fuel (= validation_fuel_ok on `Valid).

  candidate-count:  |subs| > max_candidates  ⇒  stage1 all `NotRun ; clo = CandidateCount ; NO calls.

STAGE 1  — for i in 0..|subs|-1:
  charge L (cost_stage1 (subs!i))   ⇒  `Over ⇒ TERMINAL RETURN: i..end `NotRun ; clo = CampaignFuelExhausted ;
                                                context NEVER reached ; NO further calls.
  stage1_check(vcfg, policy_document, P, i, subs!i):
    B6  wire-byte count ≤ max_wire_bytes (pure, FIRST).          → `Rejected BundleLimitExceeded
    B1a valid UTF-8.  B1b bounded structural parse.  B1c schema_version.  B2 no override.  B3 policy_hash.
    B4  x,y each n_in P integer literals.   B5 grammar + representable in integer_type.
    C1 x≠y.  C2 D_P x.  C3 D_P y.  C5 Φ_P x ≠ Φ_P y.             → `NotAWitness …
    otherwise → `Pending ps.
  pending := [(i,ps) | s1!i = `Pending ps]   (every submission was checked)
  if pending = [] : NO further calls.

LOAD CONTEXT  — load_context env (context_descriptor ac)   (F.3 fetch, once).
  `Unavailable rn ⇒ ContextUnresolved rn ; every pending slot `NotRun ; NO probe, NO candidate calls.
  `Loaded lc ⇒ continue.
  [replay only] the supplied context_bundle stands in for load_context's result:
    CtxUnavailable rn ⇒ as `Unavailable rn above.
    CtxNotNeeded WITH pending ≠ [] ⇒ context = ContextBundleInconsistent ;
      clo = InconsistentContextBundle ; every pending slot `NotRun ; NO further calls ;
      no finding (not a `capture` output — VERDICT_SEMANTICS.md §6.5).
    CtxLoaded lc ⇒ continue.

PREFLIGHT  — charge L preflight_fuel  ⇒  `Over ⇒ clo = CampaignFuelExhausted ; NO probe, NO candidate calls.
  preflight_O1_O2(lc)   — pure, NO runner call:
    O1 digest_bytes_v1("pcfw.model_artifact.v1", lc.model_bytes) = lc.descriptor.model_artifact_digest.
    O2 preproc_spec_bytes / preprocessing_digest ∧ inference_spec_bytes / inference_spec_digest.
    `Fail rn ⇒ ContextUnresolved rn ; NO probe, NO candidate calls ; every pending slot `NotRun.

PROBE  — charge L model_call_fuel  ⇒  `Over ⇒ clo = CampaignFuelExhausted ; probe NOT issued.
  req_p := {key={`ContextProbe,`Probe,0}; input=probe_input} ;  ev_p := issue env req_p.
  eval_O3(lc, ev_p, P):  ev_p.input = probe_input ∧ ev_p.outcome = `Ok probe_observation
      ∧ checkpoint shape/type from lc.inference_spec_bytes (§2.5.2).
    `Fail ⇒ ContextUnresolved RepNotReproduced ; NO candidate calls ; every pending slot `NotRun.
    `Ok rc ⇒ rc = {policy=P ; ctx=lc.ctx ; descriptor=lc.descriptor}.

STAGE 2  — issued ONLY after eval_O3 = `Ok rc.  For (i,ps) in pending:
  charge L cost_candidate (= 4*model_call_fuel)  ⇒  `Over ⇒ this + rest `NotRun ; clo = CampaignFuelExhausted.
  px := preproc rc.ctx ps.candidate.x ;  py := preproc rc.ctx ps.candidate.y   (kernel)
  issue 4 requests {`Stage2 i, X/Y, 0/1} with input px / py ;  stage2_check(rc, vcfg, tr, ps):
  ev(r,k) := lookup_unique tr {phase=`Stage2 i; role=r; repeat=k}   for r∈{X,Y}, k∈{0,1}.
  O6a  ev(X,0), ev(X,1), ev(Y,0), ev(Y,1) all `Some.                → `WitnessCheckObstructed ExecMissing
  O6b  ev(X,k).input = px ; ev(Y,k).input = py   (k ∈ {0,1}).       → `WitnessCheckObstructed ExecInputMismatch
  O6c  none of the four outcomes is `Failed / `Exhausted.           → `WitnessCheckObstructed ExecFailure / ExecFuelExhausted
  O6d  4 * model_call_fuel ≤ vcfg.per_candidate_limits.max_fuel_per_candidate.
                                                                    → `WitnessCheckObstructed ExecFuelExhausted
  O4   ev(X,0).value = ev(X,1).value (=: o_x); ev(Y,0).value = ev(Y,1).value (=: o_y).
                                                                    → `WitnessCheckObstructed NonDeterministic
  O5   o_x, o_y within expected_observation_range.                  → `WitnessCheckObstructed ObsOutOfRange
  C4   Q_P o_x = Q_P o_y  (ordinary inequality is a C-failure).     → `NotAWitness QuantisedObservationsDiffer
  otherwise → `ValidWitness wd  (wd from ps, px/py, transcript values, kernel Q_P/Φ_P).
```

**Every `charge` precedes the work it pays for** — a `stage1_check`, `preflight`,
the probe call, a candidate batch. The candidate-count check is first (no work); a
**stage-1 `charge` `` `Over `` is terminal** — the context is never reached.
`replay` runs the identical `charge`/gate sequence over the same `context_bundle`:
for a certificate whose `transcript_evidence = LiveCapture` a `` `NotRun `` slot ⟺
`capture` issued no `call_request` for that candidate and `rr.clo = co.clo`
(`(CAP1)`); for **any** certificate a `` `NotRun `` slot means the verified
schedule did not authorise that candidate (`(REP1)`) — a witness never comes from
a `` `NotRun `` slot (`VERDICT_SEMANTICS.md` §6.6). **O6 checks each event's
`input` equals `preproc rc.ctx x/y`** (`ExecInputMismatch`); **O6 precedes O4**; O4
establishes **repeatability only** — not `faithful_transcript`
(`CLAIM_AND_DEFINITIONS.md` §3.2.2).

## 7. Limits

### 7.1 Semantic policy bounds (payload, digest-bound)

`n_in`, `n_pre`, `n_obs`; `input_schema` / `model_input_schema`; quantisation
parameters and `quantisation_rounding_mode`; domain bounds;
`expected_observation_range`.

### 7.2 Operational limits — a deterministic fuel model, computable before any call

The **effective** limits are the `verifier_config` fields; `rec.resource_budget`
is advisory. Every fuel cost is a constant or a function of committed data,
**never** a runtime measurement or an input value:

- `model_call_fuel` — one forward-pass operation count (inference spec, §2.5.3);
- `vcfg.fuel_schedule = {commitment_parse_fuel ; signature_verify_fuel ;
  manifest_bind_fuel ; record_bind_fuel ; preflight_fuel ; stage1_base_fuel ;
  stage1_per_byte_fuel}`;
- **validation** (§2.4.1): `validation_fuel(reason)` = the sum of the phase
  charges completed before the failure; `validation_fuel_ok =
  commitment_parse_fuel + signature_verify_fuel + manifest_bind_fuel +
  record_bind_fuel`;
- `cost_stage1(b) := stage1_base_fuel + stage1_per_byte_fuel * min(|b|, max_wire_bytes + 1)` ;
  `cost_candidate := 4 * model_call_fuel`. The preflight and probe are charged as
  **two separate** amounts — `preflight_fuel` before `preflight_O1_O2`, then
  `model_call_fuel` before the probe call — so preflight work that fails is charged
  before it runs, and the probe cost is not paid if preflight fails.

`charge : fuel_ledger → nat → [ `Ok of fuel_ledger | `Over ]` is total and applied
**before** each unit of work: the `validate_campaign` phases (seeded `{budget =
max_fuel ; consumed = 0}`) and the gated capture (seeded with `vr.fuel`, i.e.
`validation_fuel_ok`). `fuel_model_digest` binds `model_call_fuel` +
`fuel_schedule`. The gated capture (`VERDICT_SEMANTICS.md` §6.4) issues a runner
call only past an open gate with a successful `charge` — so a `` `NotRun `` slot
corresponds to a call that **did not happen** (`(CAP1)`). Wall-clock / memory are a
weaker F.3 **watchdog** that can only add a `` `Failed `` / `` `Exhausted `` event
to `tr`; the fuel model is the normative bound.

#### 7.2.1 Bundle limits → `REJECTED_BUNDLE` (B6)

`bundle_limits`: `max_wire_bytes` (a pure byte-count check, **first** in stage 1),
`max_nesting_depth`, `max_parser_recursion` (the single bounded parse in B1b),
`max_transcript_bytes` (offline `parse_transcript`, §9). The first three →
`` `REJECTED_BUNDLE `BundleLimitExceeded ``; the last → `` `Malformed `` /
`TranscriptMalformed`. Deterministic.

#### 7.2.2 Per-candidate fuel → `WITNESS_CHECK_OBSTRUCTED` (O6d)

`per_candidate_limits.max_fuel_per_candidate`. O6 checks `4 * model_call_fuel ≤
max_fuel_per_candidate` explicitly; over ⇒ `` `WITNESS_CHECK_OBSTRUCTED
`ExecFuelExhausted ``.

#### 7.2.3 Campaign fuel and candidate count → `OBSTRUCTED`

`campaign_limits.max_fuel` — the gated capture (and `replay`, identically) charges
`cost_stage1` per submission, then `preflight_fuel`, then `model_call_fuel` (probe),
then `cost_candidate` per pending candidate, **each before its work**, seeded with
`validation_fuel_ok`. A **stage-1 `` `Over `` is a terminal return** (context never
reached); any later `` `Over `` sets `clo = CampaignFuelExhausted` and every step
from there is `` `NotRun `` (its call is never issued). A within-budget
`` `ValidWitness `` found earlier still wins (§6.7 precedence).
`campaign_limits.max_fuel ≥ validation_fuel_ok` is a config-load requirement
(§2.3), so a `` `FuelObstructed `` from `validate_campaign` never occurs. `campaign_limits.max_candidates` — `|subs| > max_candidates` →
all-`` `NotRun ``, `clo = CampaignCandidateCountExceeded` → `OBSTRUCTED` — an
**authentic oversized campaign** (`THREAT_MODEL.md` T14), not manifest tampering.
It is **not** a `validate_campaign` clause.

#### 7.2.4 The closed `limit_id` set (for `configured_limits` / `fired_limits`)

    limit_id ∈ { "bundle.max_wire_bytes", "bundle.max_nesting_depth",
                 "bundle.max_parser_recursion", "bundle.max_transcript_bytes",
                 "per_candidate.max_fuel", "campaign.max_candidates", "campaign.max_fuel" }

`configured_limits` lists every id the `verifier_config` set (ascending);
`fired_limits` is the subset that actually fired (ascending; `[]` if none). Both
canonicalise as `array` of `string` (§2.2.5).

## 8. Certificate binding and freshness

The certificate (§2.2.6) binds: `policy_digest`; `context_digests`;
`commitment_evidence` (`UnparsedCommitment` for `BadCommitmentEncoding`;
`ParsedCommitment mc.digest` for `SignerNotAuthorised` / `SignatureInvalid`; else
`AuthenticatedCommitment mc.digest`); `transcript_evidence` — `NoTranscript`
(validation obstruction), `MalformedTranscript {reason ; wire_digest}` (offline
parse failure — `wire_digest` binds the **raw wire bytes**), `LiveCapture
{transcript_digest}` (an unmodified `capture` output — **`(CAP1)` applies**), or
`OfflineTranscript {transcript_digest ; wire_digest}` (a retained transcript
re-checked — **`(REP1)` only**); `context_digests` (= `ac.M.context_digests`,
binds the `loaded_context` bytes via O1/O2); the exact candidate bundle
(`submission_digest`, `semantic_candidate_digest`, `witness_data` + `all_findings`
for `INADMISSIBLE`); `verifier_config_digest`; `fuel_model_digest` and the
`fuel_ledger` (`vr.fuel` on an obstruction branch, `rr.fuel` on the replay
branch); the verifier and extracted-kernel digests; the Rocq commit; the
extraction-assumptions list; the compiled-execution-chain descriptor; the O1–O3
`context_findings` on an `OBSTRUCTED` context failure; `configured_limits` /
`fired_limits`; the assumption list — **including `faithful_transcript` and the
`loaded_context` well-formedness** for `INADMISSIBLE`. The verdict is
`verdict(cert.body)`, not a stored field (`VERDICT_SEMANTICS.md` §9).

Freshness: `expiry = null` for the offline v0 demonstration. `created_at`, if
present, is metadata only. Replay-across-policies is defeated by the
`policy_digest` binding.

## 9. Independent replay (OFFLINE entry point)

The Phase-1+ release ships a replay package: the policy document; the model
weights; the canonical inference specification (with the O3 probe and
`model_call_fuel`); the preprocessing specification; the in-kernel target
definition; **every candidate submission (raw bytes)**; the committed
`campaign_manifest M`; the `manifest_commitment_wire MCW`; the `verifier_config`
(limits + `fuel_schedule` + `trust_anchor`); **the retained raw-wire
`exec_transcript` bytes**; the campaign record; the certificate; kernel and
verifier version information; build instructions.

Offline replay: **(a)** `vr := validate_campaign ti` (once); **(b)** reconstruct
the `context_bundle` — `load_context env′ (context_descriptor ac)` where `env′`
reads the shipped model/preproc/inference-spec bytes; **(c)**
`pr := parse_transcript vcfg <retained wire bytes>` — `` `Malformed {reason ;
wire_digest}`` (over `bundle_limits.max_transcript_bytes`, or an ill-formed event)
→ `OBSTRUCTED` / `TranscriptMalformed` binding `wire_digest`; else
`` `Wellformed {transcript ; wire_digest}``; **(d)** `assess_validated ti vr
(` `OfflineParse { result = pr ; ctx_bundle = cb }``)` = `replay ac cb …` then
`decide` (`transcript_evidence = OfflineTranscript`, so the certificate carries
`(REP1)` only — not `(CAP1)`). Given `(trusted_inputs, vr, cb, pr)` the verdict —
and the `fuel_ledger` — reproduce **exactly** on any machine (fuel is a
deterministic constant model). Re-capturing an equivalent transcript on new
hardware is the F.3 assurance argument, separate from the pure-function claim.
`MCW` + `M` are the authenticated provenance of the submission set.

## 10. Cross-language agreement battery — implementation acceptance obligation

**Not a Phase 0 completion criterion.** Acceptance criterion for the wire-format /
standalone-verifier implementation phase. It must eventually check: canonical
policy-payload encoding agreement; `to_cv` agreement for every hashed type;
`digest_v1` / `digest_bytes_v1` agreement (all normative vectors); raw-submission
parsing and `Vec`/`Mat` construction agreement; rejection of malformed and
duplicate-key JSON; policy-binding agreement; witness-outcome agreement (all eight
evaluation-order steps); `validate_campaign` and replay agreement; certificate
encoding agreement; adversarial boundary vectors; Python↔OCaml agreement over a
generated corpus. It cannot run during Phase 0 because the implementation does not
exist.
