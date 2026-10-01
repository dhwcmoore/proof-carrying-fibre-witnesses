# Current Phase-1 trust account

Phase 1 is **OPEN**. This document describes implementation evidence as of
Closure Batch 3 (2026-10-01). [TRUST_BOUNDARY.md](TRUST_BOUNDARY.md) remains the
normative trust specification; descriptions there of capture and the intended
compiled-execution assurance strategy are not evidence that those mechanisms
have been completed. [PHASE_1_STATUS.md](PHASE_1_STATUS.md) records open work.

## Kernel checks and release surface

`make check` compiles the modules listed in `implementation/_CoqProject`,
regenerates the six extractions, and explicitly runs `coqchk` on all substantive
modules. Extraction drivers are compiled but are not explicit `coqchk` targets.

The assumption release surface includes **every Theorem, Lemma, Corollary,
Proposition, Fact, Remark and Example declaration** in the substantive modules,
including helper results. The existing `Print*Assumptions.v` requests are also
retained as inspection requirements: a stale request fails rather than vanishing
from coverage. The release inventory verifies that compilation and `coqchk`
coverage match `_CoqProject` and that every existing OCaml harness is run.

The pre-Batch-1 lists selected 152 obligations, all contained in the 311
theorem-like declarations found at the baseline SHA
`ec8d7900935d7286ea4d175f420ad796df2ed6cc`. The other 159 were supporting results
omitted from those lists. The new count is discovered from source, not fixed at
311. `implementation/release-audit/inventory.json` names the inspected surface.

Inspection uses a generated temporary `.v` file compiled by `coqc`. Each requested
declaration must produce exactly one marked `Closed under the global context`
response. Nonzero exit, errors, missing/duplicate responses and unexpected axiom
reports fail the gate. The old unchecked `coqtop` invocation is no longer used.

The source gate scans only the project-owned `implementation/rocq` source
inventory, with nested comments and strings blanked. It rejects `Admitted`,
`admit`, `Axiom`, `Parameter` and their plural declaration forms. Libraries,
extracted OCaml and historical delivery packages are not source-gate inputs.
`Hypothesis` and `Variable` declarations are inventoried separately.

## Premises are not discharged by closure

Kernel closure says that a result has no remaining global logical axioms. It does
not establish its quantified parameters, implications or generalised section
hypotheses for an executable assessment. Important remaining premises include:

- faithful model/preprocessing realisation of committed artifact bytes;
- descriptor/probe/parser and policy-loader correctness;
- digest comparison contracts, authenticated-object retrieval and per-input
  policy/completeness load validation;
- candidate well-formedness, transcript shape and observation-binding premises;
- F.3 `faithful_transcript tr ctx`, represented by slot/transcript faithfulness
  premises in the Stage-2 connection. It remains unresolved. Repeatability and
  input-correctness checks do not establish it.

`policy_payload_digest_injective` is a formal premise in the manifest binding
results. It must not be described as a proved property of SHA-256 or inferred
from collision resistance. Closure Batches 1–3 do not change that premise. Universal SHA-256 injectivity
on the unbounded policy-string domain is not a valid instantiation: SHA-256 has a
finite output range. The abstract formal contract is consistent (the existing
consistency example uses a string-valued injective function), but concrete
SHA-backed policy-equality claims under this theorem remain blocked. The new
byte adapter checks literal committed-policy byte equality instead; it does not
reformulate the theorem or discharge its premise.

## Extraction, implementation and compiler trust

All current extraction units use `ExtrOcamlNatBigInt` and `ExtrOcamlZBigInt`,
with the kernel's Zarith `Big_int_Z.big_int` representation: kernel,
orchestration, Stage-1/Stage-2, manifest/authentication, transcript-digest, and
one shared closure for the existing Phase-1 pipeline builder. The structural
OCaml AST gate rejects native `int` types in regenerated interfaces. Counts,
roots and numeric signature fields are generated in
`implementation/release-audit/integer-correspondence.json`.

Exactness is conditional on the Rocq domains: extracted `nat` values must be
nonnegative, and `positive` values positive. Raw `Big_int_Z` types do not enforce
these refinements. Fixture input conversions reject negative naturals; the
existing decimal record decoder rejects negative syntax. Arbitrary callers must
preserve these invariants. The byte adapter checks its nat inputs; complete production schema/domain and
parser correctness are not established.
No fixed-width truncation is used for semantic counters, budgets, indices or
coordinates. Resource exhaustion remains possible; bigint does not promise
unlimited memory or stack.

The historical `ocaml/orchestration.ml` mirror retains native integers and reduced
records, without a correspondence proof. It is explicitly non-normative and is
excluded from compilation/linking by the release gate. The context regression
now uses extraction. Host byte/bit/string/list utilities still use bounded native
integers, including the unchanged test crypto fixture; they do not implement
unbounded semantic counters.

The finite differential battery compares small actual Gallina functions and
signed `Z` values, plus labelled exact `Z` reference cases for enormous natural
arithmetic/decimal values. Those reference cases do not evaluate the full
Gallina unary-natural parser or fuel function at enormous magnitudes. Passing
differential tests demonstrate agreement on those cases. They are not a general
correspondence theorem. The integrated harness exercises an empty typed campaign,
real existing authentication, record checks and exact fuel. Batch 3 adds an
offline byte path with derived record completeness, descriptor/snapshot checks
and a concrete ASCII transcript digest hook. Model, candidate-parser, formal
context-execution and capture hooks remain unused;
a full model/witness pipeline is still outstanding.

Extraction mappings, Coq extraction, OCaml compilation/linking, Zarith/C bindings
and build tools remain trusted. See
[PHASE_1_EXACT_INTEGER_CORRESPONDENCE.md](PHASE_1_EXACT_INTEGER_CORRESPONDENCE.md)
for the reproduced former overflow failures and exact test boundaries.

## Parser, I/O, transcript and cryptographic trust

Canonical manifest rendering and ASCII-wire record/manifest decoding have
formal results and test vectors. `ocaml/phase1_bytes.ml` adds a **hand-written,
unproved, bounded ASCII-wire adapter**. It reuses the extracted string decoder
and record/manifest checks; canonical-tree parsing, completeness interpretation,
transcript schema mapping and descriptor loading in this wrapper are trusted
implementation code, not new Gallina results. See
[PHASE_1_BYTE_BINDING.md](PHASE_1_BYTE_BINDING.md) for the full boundary inventory.

Within that adapter, successful full canonical-tree decoding must re-encode to
identical bytes. Exact schemas reject unknown/missing fields and noncanonical
order/whitespace/numerals; semantic integers are bigint. Raw non-ASCII text is
rejected, so this is narrower than the normative Unicode language. The default
host parser nesting bound is 128; full operational-config byte loading is absent.

Completeness is derived from the same record bytes before assigning
`ti_completeness`. Unknown/Incomplete/Complete are interpreted; complete scheme
and canonical body are retained. Incomplete limitations survive in raw record
bytes but are absent from the formal payload-free Incomplete constructor. Old
extracted APIs still accept independently supplied typed fields. The abstract
`record_completeness_of`/per-input loader premise remains: no formal correctness
proof of the new wrapper is supplied. No semantic certificate registry is added;
EXACT remains disabled.

Descriptor fields and immutable supplied model/preprocessing/inference snapshots
are checked against tagged digests and the supplied manifest descriptor. Literal
canonical policy bytes are checked against independently supplied committed bytes
and their tagged digest. This is **opaque byte identity**, not §2.3 policy semantic
loading, registry conformance, inference/probe decoding, or model realisation.
There is no file-fetch/authority loader or proof connecting these callbacks to
kernel policy semantics.

The transcript adapter atomically decodes the published event-array schema,
checks tags/nat keys, vector dimensions supplied by its caller, byte limits and
exact re-encoding. It preserves raw-wire digest evidence on both result branches.
It does not derive dimensions from a verified semantic policy loader or prove
`transcript_stage2_wf`. The schema contains no context identifier; syntactic
validity cannot distinguish same-shaped transcripts from different contexts.

The new hook hashes exactly `pcfw.exec_transcript.v1 || 0x1f || canonical bytes`
using the existing SHA implementation; independent Python vectors check tested
bytes and digests. The Gallina `transcript_digest_v1`/`to_cv` contract remains
abstract and unproved for this wrapper. The old colliding mock harness is retained
as a separate interface regression. Digest determinism proves neither collision
resistance nor authentication. Transcript hashing/parsing establishes no
faithfulness. Capture/replay, candidate parsing and full Unicode/schema conformance
remain open.

The manifest harness links the existing `sha` library and unchanged shared test
Ed25519 fixture. Tests do not prove cryptographic security; Batch 3 changes no
cryptographic algorithm.

The manifest harness links the `sha` library and a shared test-fixture OCaml Ed25519
implementation. Frozen/RFC vectors and rejection tests do not prove those
implementations secure. Batch 2 moves the existing fixture unchanged; no cryptographic algorithm changes.

Filesystem retrieval, OS/runtime behaviour, runner behaviour and signing-key
custody remain environmental trust. The source manifest detects changes relative
to its recorded bytes; it is not itself an authenticated release signature.

## Process evidence

`make release` verifies the manifest, cleans, runs the existing full check, and
rechecks the manifest. It records the commit SHA, dirty working-tree status,
manifest digest, compiler versions and mechanically generated counts. A passing
run always records **OPEN / NOT YET CLOSED**. It is a clean local check in the
recorded environment, not a byte-identical rebuild result or proof of dependency
reproducibility. No complete CI workflow or dependency lock is established here.
