# Current Phase-1 trust account

**Phase 1 is OPEN; policy mode is PARAMETRIC (Closure Batch 5, 2026-10-01).**
The public claim is conditional on a supplied semantic `Policy`, supplied
`AuditContext`, local policy binding and the existing validation/evidence
contracts. [RELEASE_CRITERIA.md](RELEASE_CRITERIA.md) governs this release scope.
The broader designs in [TRUST_BOUNDARY.md](TRUST_BOUNDARY.md) and the Phase-0
specifications are historical specifications, not evidence of implemented capture,
concrete quantisation, target registration or arbitrary semantic policy loading.

## KERNEL-CHECKED

`make check` compiles the project-owned modules listed in
`implementation/_CoqProject`, regenerates extraction and runs `coqchk` on every
substantive module. Extraction drivers are compiled but are not explicit `coqchk`
targets. Kernel witness, orchestration, Stage-1/Stage-2 and binding results retain
their exact premises and conclusions; the v0 `EXACT` branch remains unreachable.

The assumption release surface includes every `Theorem`, `Lemma`, `Corollary`,
`Proposition`, `Fact`, `Remark` and `Example` in substantive modules, including
helpers. Legacy `Print*Assumptions.v` requests remain inspection requirements:
a stale name fails. The original lists selected 152 of the 311 declarations at
`ec8d7900935d7286ea4d175f420ad796df2ed6cc`; the others were omitted helpers.
Current counts and names are generated in `release-audit/inventory.json`, rather
than fixed to those historical counts.

Inspection compiles a temporary `.v` file using `coqc`. Every requested name must
produce exactly one marked `Closed under the global context` response. Process
failure, errors, missing/duplicate responses and unexpected axioms fail the gate.
The source gate scans only the project-owned Rocq inventory, blanking nested
comments and strings; it rejects `Admitted`, `admit`, `Axiom`, `Parameter` and
plural declaration forms. `Hypothesis` and `Variable` are inventoried separately.
Generated OCaml, libraries and historical delivery packages are not source inputs.

Kernel closure means no global logical axioms remain. It does not discharge
quantified parameters, implications or generalised section hypotheses. Theorem
premises remain theorem premises. In particular, `policy_binding p_committed ti`
is transparently **`ti_policy ti = p_committed`**, supplied for one input. The seven
formerly injectivity-dependent interfaces now use it, without a universal policy
hash-injectivity premise. Their conclusions are unchanged; the policy-only
conclusion restates the supplied equality. Validation does not construct binding.
The gate kernel-typechecks all seven exact interfaces, including parameter order.

Separate results prove manifest-policy digest agreement from parsing and the
matcher, and from successful validation with that matcher wired in. Neither
result constructs policy identity. `digest_agreement_does_not_bind_policy` gives
an abstract constant-digest example with truthful digest fields, matching hashes
and unequal policy tokens; it is not a SHA-256 collision.

## EXECUTABLE-CHECKED

Existing harnesses exercise validation, authentication, record/completeness and
cross-checks, transcript evidence, context handling and witness control flow.
The integrated pipeline harness has an empty-campaign boundary; its model,
candidate-parser, context-execution and capture callbacks are unused. This is
not an executed full learned-model/witness pipeline.

All normative extractions use `ExtrOcamlNatBigInt` / `ExtrOcamlZBigInt` and Zarith
`Big_int_Z.big_int`. The structural OCaml AST gate rejects native `int` interface
types and historical orchestration-mirror imports/linking. The finite differential
battery distinguishes actual Gallina cases from exact `Z` reference cases for
huge naturals. It does not evaluate huge unary-natural Gallina parsers or prove
general executable equivalence. See the historical
[Batch-2 evidence](PHASE_1_EXACT_INTEGER_CORRESPONDENCE.md).

`ocaml/phase1_bytes.ml` is a hand-written, unproved bounded ASCII-wire adapter.
It reuses extracted manifest/record/string checks; canonical-tree decoding,
completeness interpretation, transcript schema mapping and descriptor loading
remain trusted wrapper code. Successful full-tree decoding re-encodes identically;
exact schemas check unknown/missing fields, ordering, whitespace and numerals.
Non-ASCII input is rejected and nesting defaults to 128. This is narrower than
the historical Unicode language; full operational-config byte loading is absent.

Completeness is derived from the same record bytes. Complete scheme/body are
retained; Incomplete limitations survive only in raw bytes, because the typed
constructor is payload-free. The abstract `record_completeness_of` / per-input
load-validation premise remains. Independently supplied typed fields remain
possible through raw APIs. No semantic certificate registry is added.

Descriptor and immutable supplied model/preprocessing/inference snapshots are
checked against tagged digests and the supplied manifest descriptor. Canonical
policy bytes are checked against independently supplied committed bytes and their
tagged digest. These checks establish tested byte identity and digest agreement,
not functional `Policy` realisation or authoritative object retrieval.

The transcript adapter checks the event-array schema, tags, natural-number keys,
caller-supplied vector dimensions, byte limits and exact re-encoding. It preserves
raw-wire digest evidence on both branches. The schema has no context identifier:
syntactic validity cannot establish transcript/context identity. The hook hashes
`pcfw.exec_transcript.v1 || 0x1f || canonical bytes`; independent Python vectors
check tested encodings, inputs and digests. The Gallina `transcript_digest_v1` /
`to_cv` contract is still abstract for this wrapper. The old mock digest harness
remains an interface regression. See [Batch-3 evidence](PHASE_1_BYTE_BINDING.md).

## POLICY-REALISATION PREMISE

`FibreWitnessKernel.Policy` contains supplied total `domainb`, `quantise` and
`target` functions. `AuditContext` adds supplied `preproc` and `model` functions
and contains `context_policy`. Their intended external-specification realisation
is an external semantic contract. No Phase-1 loader interprets arbitrary policy
bytes into those functions; no concrete target registry or quantiser is required
by this parametric release.

The distinct lowercase `Orchestration.policy` is an opaque string token.
`policy_binding` equates that token with a selected committed token; it does not
by itself equate functional policies or establish their realisation. Callers must
supply the token/semantic-context association and truthful metadata callbacks,
including `policy_context_of`, `policy_audit_instance_id_of`, and relevant
`committed_context_wf`/load contracts. Stage-1/Stage-2 wiring closes over the same
supplied `C`; it does not verify where that `C` came from.

Raw extracted APIs retain caller-supplied semantic inputs and callbacks, with
logical premises erased. Even an accepted byte payload plus a successful
`validate_campaign` is insufficient to infer the caller's token or functional
policy is the intended committed policy. This batch changes proofs and the
claim boundary, not runtime enforcement of that association.

## TRANSCRIPT-FAITHFULNESS PREMISE

F.3 `faithful_transcript tr ctx` and the slot/transcript realisation premises in
the Stage-2 connection remain unresolved/external. The explicit kernel
`ObservationBinding` premises connect supplied observations to the supplied
context, not to independently verified external events. Repeatability, parsing,
hashing, input checks and replay do not establish observation truth or capture
faithfulness. No capture/replay implementation or faithfulness contract changes
in Batch 5. This premise is distinct from policy realisation.

## IMPLEMENTATION TRUST

Coq extraction and its mappings, OCaml compilation/linking, Zarith/C bindings,
`sha`, the existing test-fixture Ed25519 implementation, runtime and build tools
remain trusted. Frozen/RFC vectors and rejection tests do not prove cryptographic
security. Digest comparison truth (`eqb = true -> equality of digest strings`)
is a different contract from hash injectivity; digest determinism proves neither
collision resistance nor authentication.

Extracted `nat` values must be nonnegative and `positive` values positive. Raw
bigint types do not enforce these refinements. Fixture conversions and the byte
adapter check relevant natural inputs; arbitrary callers must preserve domain
and vector invariants. Bigint prevents fixed-width semantic truncation, but not
resource exhaustion. Host byte/string utilities still use bounded native indices.
The retained native-integer orchestration mirror is non-normative and excluded
from required execution.

Canonical-tree parsing, record interpretation, descriptor/probe/parser conformance,
`to_cv`, config/key/authority loading, filesystem retrieval, OS behaviour, runner
behaviour and signing-key custody retain their stated implementation or environment
contracts. No general correspondence proof connects all handwritten adapters to
Gallina. The source manifest detects changes against recorded bytes; it is not
an authenticated release signature.

`make release` verifies the manifest, cleans, runs the full check and rechecks the
manifest. It records the base SHA, dirty status, manifest digest, tool versions
and generated counts, with policy mode `PARAMETRIC` and semantic loader status
`NOT_IN_PHASE1_SCOPE`. Passing always records **OPEN / NOT YET CLOSED**. This is
local build evidence, not byte-identical dependency reproducibility; CI/dependency
locking and final premise/trust acceptance remain review work.
