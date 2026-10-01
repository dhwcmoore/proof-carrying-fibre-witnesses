# Phase-1 Closure Batch 3: concrete bytes and retained loader contracts

> Historical evidence: this report preserves the pre-Batch-5 interfaces and
> acceptance boundary. Batch 5 replaces their universal policy digest injectivity
> with explicit local `policy_binding` and adopts a parametric release.
> The earlier injectivity/semantic-loader blocker below is superseded; absence
> of a concrete semantic loader is **NOT IN PHASE-1 SCOPE**. See
> [TRUST.md](TRUST.md) and [RELEASE_CRITERIA.md](RELEASE_CRITERIA.md).

2026-10-01. **Phase 1 OPEN / NOT YET CLOSED; Phase 2 unauthorised.**
This is implementation evidence awaiting review, not a closure disposition.
PCFW verifies claim conditions relative to a formally specified learned
observation regime; it does not thereby verify the learned system in its entirety.

## Baseline

Clean Batch-2 checkpoint: `e8fb7cd24f6d25605ee0c765c7fb6008230f616c`.
Before edits, `make check` and `make release` passed: 20 substantive modules,
26 compiled modules including six extraction drivers, 311 theorem/assumption
inspections, 12 harnesses, 59 integer differential cases and 116 manifest entries.
Toolchain: Coq 8.18.0, OCaml 4.14.1, Python 3.12.3; existing Zarith/sha libraries.
The byte-boundary inventory was produced before edits. No existing or new Rocq
source, extraction mapping, theorem statement or proof is changed in this batch.

## Byte-to-typed-object inventory

Categories: **1** fully executable and checked within the stated bounded scope;
**2** executable but formal binding still conditional on loader/component
premises; **3** formally/prose specified but not completely concretely parsed;
**4** documentation-only / not implemented. A category is not a claim of general
compiler or parser correctness. “B” below is `ocaml/phase1_bytes.ml`.

| Artefact; baseline → current category | Representation, decoder and typed destination | Canonical form, validation and binding | Governing formal result / exact residual |
|---|---|---|---|
| Manifest commitment; 1 → 1 | B.commitment parses a three-key object, then extracted parse_commitment_impl produces the existing wire/validated commitment | digest/signature/signer in sorted order; ASCII strings; 64/128 lowercase hex; existing signer/key/signature checks | ManifestAuthentication.validate_campaign_authenticates; SHA/Ed25519 contracts retained; host envelope parser unproved |
| Campaign manifest; 1 → 1 | extracted parse_manifest_impl, guarded by B.manifest, to campaign_manifest_view | five fixed keys, three descriptor digests, ordered submission list with multiplicity retained; schema/digest checks and exact render equality; signed canonical digest | parse_manifest_impl_wf and validate_campaign_authenticates; ASCII subset and crypto contracts |
| Record identity/results/budgets; 1 → 1 | extracted parse_record_impl/parse_record_full_impl plus B.record; full typed view and original record string | eight fixed keys, typed outcome/finding/budget decoding; bigint numerals; existing identity match and advisory crosscheck | CampaignRecord.record_identity_mismatch_impl_none_iff; RecordCrosscheck.parse_record_full_impl_projects/crosscheck_impl_nil_iff; projections lose information, advisory findings do not change verdict |
| Policy document/semantic policy; 3 → 3 | normative document/payload; executable policy_document/policy remain opaque strings; no complete semantic decoder | §2.3/§2.5 mandatory fields, registries, domain/quantisation/inference validation remain unimplemented | ManifestMatching.validate_campaign_concrete_binds_policy; policy_digest_load_validated, kernel-policy interpretation and injectivity contract remain |
| Opaque policy payload bytes; 3 → 2 | B.decode and bind_policy_bytes to the existing opaque string | ASCII canonical tree; literal equality to supplied committed bytes; tagged digest equality | No new theorem. This is not schema-valid semantic policy loading; committed bytes/digest supplied independently |
| Validation/context descriptor; 3 → 2 | B.descriptor to CanonicalV1.context_descriptor | exactly inference_spec_digest/model_artifact_digest/preprocessing_digest, sorted; 64 lowercase hex; compare with manifest descriptor | ContextResolution.preflight_ok_binds; formal parse_descriptor callback/correctness not instantiated or proved |
| Model/preproc/inference snapshots; 2 → 2 | B.bind_context accepts supplied immutable strings and produces loaded_context | recompute the three published domain-separated byte digests, compare descriptor and supplied manifest descriptor | preflight_ok_artifact_bound remains conditional; no file fetch, semantic interpreter, probe_of_spec or realises_C discharge |
| Completeness; 3 → 2 | B.completeness/B.record/B.bind_record derives completeness_status from record bytes | unknown string, incomplete limitations object/array, or complete scheme/body; closed shapes; existing structural predicate; assigns ti_completeness | ManifestPipeline.validate_campaign_completeness_bound_to_record remains conditional on record_completeness_of/load premise; adapter correctness unproved; empty registry keeps EXACT disabled |
| Offline transcript; 3 → 2 | B.parse_transcript to exec_transcript and existing atomic parse_result | published array/event/key/outcome schema; closed fields/tags, nat keys, supplied vector dimensions, byte limit, canonical re-encoding; wire digest on both branches | No new Gallina decoder theorem; dimensions supplied rather than loaded semantically; transcript_stage2_wf/faithfulness not discharged |
| Transcript digest input; 3 → 2 | B.transcript_bytes/transcript_digest_input/transcript_digest | exact tagged canonical event-array bytes, call order significant; existing SHA function; independent Python vectors | TranscriptDigest.live_evidence_digest_agrees/offline_evidence_digest_agrees retain abstract transcript_digest_v1/typed agreement premise; no proved to_cv correspondence |
| Registry/target/checkpoint IDs; 3 → 3 | normative strings; kernel functions and probe/context callbacks supplied externally | no concrete registry/selector loader; no inference checkpoint grammar invented | Kernel/Stage-2 conclusions retain supplied policy/context; registry selection and shape interpretation remain external |
| Audit/context identifiers; 2 → 2 | manifest/record decoders plus opaque policy/context callbacks | existing audit/record equality and descriptor/snapshot checks; manifest identifiers are canonical ASCII strings | policy_audit_instance_id_of/policy_context_of correctness remains external; transcript schema has no context ID |
| Raw submission snapshots; 2 → 2 | B.bind_submission to candidate_submission wire/length/digest | published candidate_submission byte tag; compare recomputed digest to supplied manifest entry; exact physical length | ManifestLedger typed binding results do not prove hash/retrieval/ledger provenance; no candidate semantic parser |
| Candidate semantic metadata; 3 → 3 | external lower_parse/parse_literal/candidate_id_of; existing parsed candidate/stage fields | published candidate schema; existing typed Stage-1 checks after supplied parsing | Stage1Wrapper.wrapper_pending_binds; parser conformance and semantic digest truthfulness remain |
| Witness/certificate metadata; 3 → 3 | typed witness/certificate data and published serializer mappings | no complete byte serializer; executable records omit some normative preproc/quantised/target evidence | Existing typed witness-selection/checker theorems remain conditional; full evidence byte correspondence absent |
| Verifier config/trust-anchor bytes; 3 → 3 | tests still construct verifier_config/trust_anchor | normative sorted keys/signers and load checks not concretely decoded; B uses typed max_transcript_bytes | Config/key/authority loading remains trusted; no new policy or operational model |
| Reports/replay package; 3 → 3 | normative report/certificate/package schemas and existing typed outputs | most full to_cv/package rows not implemented; no complete package roundtrip | Typed assessment results remain; byte output/package coverage is incomplete |
| File retrieval/authority chronology; 4 → 4 | files/environment intended; B accepts byte strings, not paths | source MANIFEST gate is distinct from campaign authentication; supplied snapshots checked after receipt | No fetch/TOCTOU/ledger/commit-before-search mechanism; environment, signing roots and authoritative expected bytes remain trusted |

## Concrete pre-repair counterexample

A probe linked against the untouched baseline integration modules printed:

```text
record completeness=42, supplied typed Unknown: full_decode=true; validation=VALID
record completeness={"k":"complete","v":{"body":0,"scheme":"registry-v0"}}, supplied typed Unknown: full_decode=true; validation=VALID
```

The record's syntactic value was skipped, while step 9 checked the independent
`ti_completeness`. This is a reproduced loader discrepancy, not a false theorem:
existing completeness-bound theorems require the explicit per-input loader premise.
The new adapter rejects `42` and derives Complete (including scheme and canonical
body) in the second case. Old extracted APIs remain unchanged and can still be
called with inconsistent trusted inputs; the repair is enforced on adapter paths,
not claimed globally for arbitrary OCaml callers.

Two different canonical records may legitimately have the same projected
identity/full-check view. Likewise Incomplete has no limitations payload in the
formal constructor: different limitation lists map to the same status. B retains
the full original record bytes; it does not claim that those partial typed views
uniquely determine the whole record. Different same-shaped contexts can also have
syntactically identical transcript arrays: that schema has no context identifier.

## Canonical encoding audit and established bounded checks

B implements a hand-written canonical tree parser/renderer over ASCII text. It
reuses the extracted string decoder/escaper and existing manifest/record decoders.
No new formal parser correctness or general roundtrip theorem is supplied.

- Objects sort keys on rendering; decoding requires strict ascending decoded
  keys, rejecting duplicates, alternate order, unknown/missing schema fields.
- Arrays retain order and multiplicity. Optional typed record fields use existing
  decoder rules; absent fields are omitted, not interpreted as null. Arbitrary
  completeness bodies may contain canonical null values by their value schema.
- Integers use bigint decimal `0 | -?[1-9][0-9]*`; `+`, leading zeros, `-0`,
  floats/exponents are rejected. Negative signed vectors remain exact; natural
  keys/budgets reject negatives. Huge values are supported rather than truncated.
- Whitespace outside strings, trailing bytes/commas, truncation and alternate
  escapes are rejected. The existing seven escapes and lowercase control-code
  escapes are used. All raw non-ASCII bytes are rejected, including valid UTF-8:
  this is an explicit subset of the normative Unicode language, not full UTF-8
  support. Malformed UTF-8 is consequently rejected as outside this subset.
- Successful full tree decoding must satisfy `render(tree) = original bytes`.
  Transcript decoding additionally requires exact re-encoding of its typed events.
  These are executable checks, not proofs about every possible parser input.
- The host parser has a configurable native host depth bound (default 128),
  outside the current reduced formal config. It is not a change to semantic
  bigint limits. Transcript byte limits use the supplied bigint config value.
  Runtime exhaustion remains possible and is not converted into success.

The established encodings cover bounded canonical trees, manifest/commitment
schemas, existing record fields plus completeness, context descriptors, and the
published typed transcript schema. They do not establish policy schema semantics,
all report/certificate to_cv rows, config loading, or full Unicode conformance.

## Loader bindings and completeness semantics

The adapter checks literal canonical policy-byte equality against independently
supplied committed bytes and recomputes the published payload digest. It returns
an **opaque policy string**. It does not validate mandatory policy fields,
registries, domain/quantisation, checkpoint/inference semantics or construct the
kernel's functional Policy. The integration policy fixture is deliberately a
small opaque canonical object, **not a schema-valid §2.5 policy document**.
No authoritative semantic-policy load claim is made from this fixture.

Descriptor and supplied immutable model/preproc/inference snapshots are checked
using their published tags. The expected descriptor must come from an
**authenticated** manifest before being trusted. B does not itself authenticate
that argument or fetch files. The integration subsequently authenticates the
same manifest before assessment and makes no model call. Digests bind the supplied
snapshots under retained crypto assumptions, not their behavioural realisation.

B.record derives Unknown, Incomplete or Complete from the record's concrete
`completeness` field; B.bind_record assigns the derived value together with those
same raw record bytes. A complete certificate retains its nonempty scheme and
canonical body. An incomplete status checks limitation shapes and retains the
limitations in raw bytes, while the formal status records only the constructor.
This is structural information, not proof of fibre completeness or a new scheme
registry. `valid_completeness_certificate_v0` remains false and EXACT unreachable.
The abstract denotation/loader premise is still present in Gallina; tests do not
replace a proof connecting this hand-written adapter to that denotation.

## Transcript and digest-input boundary

The offline parser consumes exactly the §2.2.5 array/event schema: input, key
(phase/repeat/role), outcome. All published phase and role tags are supported;
no extra relation between them is imposed. Execution-specific key requirements
remain with the checker. The parser does not invent a context ID or fuel field.
Vector lengths are checked against supplied `n_pre`/`n_obs`; negative parameters
and nat keys are rejected. It does not derive dimensions from verified policy or
inference loading and does not prove all Stage-2 shape/uniqueness premises.

Both Wellformed and Malformed carry the digest of the **original raw bytes**:

```text
SHA256("pcfw.exec_transcript_wire.v1" || 0x1f || raw bytes)
```

The new typed hook hashes deterministic, explicitly constructed bytes:

```text
SHA256("pcfw.exec_transcript.v1" || 0x1f || canonical event array)
```

Producer/decoder roundtrips and independent Python vectors check these exact
bytes, delimiter and digests for empty, successful and failed/exhausted bigint
transcripts, including escaped controls and significant event order. Noncanonical
wire forms are rejected rather than silently normalised. The Gallina
`transcript_digest_v1` remains abstract; equality to this concrete implementation
and general `to_cv` correctness are not proved. The original mock hook tests
remain separate regression evidence.

Syntactic transcript validity is distinct from `faithful_transcript tr ctx`.
Neither dimension checks, canonical encoding nor digest equality establishes
real execution, context provenance, collision resistance or authentication.

## policy_payload_digest_injective

The current policy is an unbounded string and its abstract digest function returns
strings. The surrounding policy-binding proof explicitly uses universal
injectivity to infer `ti_policy = p_committed` from digest equality
(`ManifestMatching.manifest_policy_matches_impl_sound`). Dropping that premise
without a replacement is unsound: a constant abstract digest makes different
policy strings pass the equality check. This is not a reproduced SHA-256 collision.

The formal contract is logically consistent with an injective string-valued
function; the existing `mm_ppd_injective` consistency example witnesses that.
It **cannot** be supplied by universal SHA-256 injectivity on this unbounded
policy domain: SHA-256's output range is finite. Collision resistance does not
supply that equality implication. Concrete SHA-backed instantiation of this
policy-equality theorem remains **BLOCKING**.

Per Batch-3 G's permitted second outcome, the premise is retained explicitly as
an abstract logical contract. B checks exact committed canonical bytes instead
of relying on digest equality to infer byte identity. There is no theorem rewrite
or attempted SHA instantiation. A formal replacement would need authoritative
committed bytes and a deterministic, validated byte-to-semantic-policy relation,
which the current opaque representation does not provide. A substantive change
to those theorem statements/architecture must be reviewed before implementation;
this batch does not change or hide the contract.

## Tests, integration and release evidence

The adversarial harness currently reports 61 passing checks: duplicate/order/
whitespace/escape/numeric/UTF-8/truncation failures, missing/unknown fields,
huge signed numbers, negative naturals, descriptor/artifact and policy mismatch,
stale submission entry, record-derived completeness/mismatch, transcript tags,
limits/dimensions/order, and digest input mutation. The existing integration adds
record/context mutation rejection through actual validation.

Three independent Python vectors compare canonical transcript bytes, exact digest
input bytes and SHA256 outputs. These are finite case evidence, not a parser,
compiler, cryptographic or general correspondence theorem. The release validates
that both the byte battery and integration executed and revalidates generated
vector evidence. A failed vector run overwrites old evidence with FAILED.

The gate regression suite passes 17 tests, including missing vector responses,
mutated digest-input bytes and omitted required log evidence. A live negative
simulation temporarily replaced the vector client with one returning a mutated
digest input: the real gate exited 1 and overwrote byte-vectors.json with FAILED.
Restoring the client returned PASS for all three vectors. No project formal
source was modified by these negative checks.

The existing integration remains **empty-campaign**:

```text
canonical commitment/manifest/record + opaque policy bytes + supplied snapshots
 -> byte adapters, derived completeness, descriptor/snapshot checks
 -> existing manifest authentication, validation and record checks
 -> canonical offline transcript decoding and concrete digest-input construction
 -> UNDERDETERMINED report; malformed transcript -> OBSTRUCTED
```

All original integration assertions remain. The new path authenticates with the
unchanged existing crypto fixture, uses exact fuel, and exercises canonical
record identity rejection. The formal model/stage/context execution callbacks
still fail if used. There is no model/witness execution, physical capture,
faithfulness simulation or new external-system correctness claim.

Implementation changes passed targeted tests, `make check`, and clean
`make release`; final results/counts are generated in
`implementation/release-audit/summary.json`, with per-vector evidence in
`byte-vectors.json`. Counts remain discovered. The working-tree manifest and
base SHA identify this uncommitted evidence, not a release commit/signature.
No commit or push is made; publishing and Phase 2 remain unauthorised.

## Remaining priorities

- **BLOCKING:** complete authority/config/semantic policy/inference/probe/registry
  loading and kernel-policy realisation; replace or otherwise justify the actual
  concrete policy-equality theorem surface before SHA-backed instantiation;
  formal or explicitly accepted parser/loader/to_cv contract account; full
  model/witness/package acceptance, capture/replay obligations and final closure
  review. `faithful_transcript` remains unresolved and unchanged.
- **SHOULD FIX:** broaden independent byte/parser corpora, review ASCII scope and
  parser resource bounds against governing config, add full validated output and
  config loading, reproducibility/CI/dependency evidence. Passing local tests do
  not complete those acceptance items.
- **DOCUMENTED RESIDUAL:** trusted hand-written byte adapter, supplied dimensions
  and authoritative committed-byte roots, hash/crypto/extraction/compiler/runtime
  trust, resource exhaustion, and filesystem/key/chronology environment. Typed
  projections may intentionally forget metadata; no global byte identity or
  faithfulness follows from those projections.

Stop after Batch 3. No existing formal theorem is changed or strengthened into
an unsupported concrete claim.

## Exact Batch-3 source change inventory

- `.gitignore`
- `IMPLEMENTATION_STATUS.md`
- `MANIFEST.sha256`
- `NONCLAIMS.md`
- `PHASE_1_BYTE_BINDING.md`
- `PHASE_1_STATUS.md`
- `README.md`
- `RELEASE_CRITERIA.md`
- `TRUST.md`
- `implementation/Makefile`
- `implementation/README.md`
- `implementation/ocaml/phase1_bytes.ml`
- `implementation/ocaml/test_byte_boundaries.ml`
- `implementation/ocaml/test_phase1_integration.ml`
- `implementation/scripts/byte_vectors.py`
- `implementation/scripts/integer_surface.py`
- `implementation/scripts/release.py`
- `implementation/scripts/test_gates.py`
