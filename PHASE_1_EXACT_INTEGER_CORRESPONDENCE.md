# Phase-1 Closure Batch 2: exact integers and executable evidence

Date: 2026-10-01. **Phase 1 OPEN / NOT YET CLOSED. Phase 2 unauthorised.**
This is a local implementation/evidence report, not reviewer concurrence.
PCFW verifies claim conditions relative to a formally specified learned
observation regime; it does not thereby verify the learned system in its entirety.

## Baseline and inventory

The Batch-1 checkpoint was clean on `main`, SHA
`8b3a8137d115ad801576e7ed1bf2b8f265b99895`. Before edits, `make check` and
`make release` both passed: 20 substantive modules, five extraction units,
311 assumption inspections, ten OCaml harnesses and 107 manifest entries.
Coq 8.18.0, OCaml 4.14.1, Python 3.12.3, Zarith 1.14 and sha v1.15.4 were
observed locally. Library paths resolved through `/data/.opam/default/lib`.

The full pre-edit mechanically collected inventory, including roots, signature
lines, active mappings and source-definition examples, is preserved in
[integer_correspondence_baseline.json](implementation/scripts/integer_correspondence_baseline.json).
The release generates the current full inventory in
`implementation/release-audit/integer-correspondence.json`.

Classification: 1 = extraction with the existing trusted bigint mappings,
2 = extraction containing native semantic integers, 3 = hand-written analogue,
4 = host wrapper/fixture with no direct formal implementation counterpart.
Category 1 is conditional on valid Rocq integer domains and trusted extraction;
it is not a proved general compiler-correctness result.

| Module / executable path | Baseline → current category | Numeric representation / coverage |
|---|---|---|
| `extracted_fibre_witness_kernel` | 1 → 1 | bigint vector coordinates and dimensions; domain/quantisation/target/observation roots |
| `extracted_orchestration` | 1 → 1 | bigint coordinates, event values, indices, lengths, fuel and budgets; validation/replay/decision roots |
| `extracted_stage2` | 1 → 1 | bigint Stage-1/2, vector dimensions, adapter fuel, context and manifest-matching data |
| `extracted_manifest_auth` | 2 → 1 | native nat → bigint; previously structural binary `Z` was already exact, now uniformly bigint; record indices/budgets, ledger indices, lengths and validation configuration |
| `extracted_transcript_digest` | 2 → 1 | native nat and `Z` → bigint; signed input/output values, repeat/phase indices, counters and budgets; digest output remains a string |
| `extracted_phase1_integration` | absent → 1 | one closure of existing pipeline, validation, assessment, record parsing and digest-evidence functions; all semantic integers bigint |
| `orchestration.ml/.mli` | 3 → 3, non-normative | native integers remain, with observable overflow; excluded from required compilation/linking |
| `test_context_bundle` | 4 → 4 | migrated from native mirror to bigint extraction; all existing context regressions retained |
| `test_context_resolution` | 4 → 4 | bigint extracted context fixture values |
| `test_fibre_witness_kernel_bigint` | 4 → 4 | bigint vectors/dimensions and small host fixture utilities |
| `test_manifest_authentication` | 4 → 4 | checked bigint naturals; existing real crypto tests; huge record/configuration and decimal roundtrips |
| `test_manifest_matching` | 4 → 4 | bigint extraction; existing small matching fixtures |
| `test_orchestration_bigint` | 4 → 4 | bigint coordinates, fuel and indices |
| `test_stage1` | 4 → 4 | bigint coordinates/literal ranges; existing host parser fixture callbacks |
| `test_stage1_wrapper` | 4 → 4 | bigint indices/dimensions/coordinates; existing parser fixtures |
| `test_stage2` | 4 → 4 | bigint witness/adapter budget fixtures |
| `test_transcript_digest` | 4 → 4 | migrated typed fields to bigint; checked nat conversion; abstract deterministic digest fixture |
| `manifest_crypto_fixture` | formerly embedded → 4 | moved byte-for-byte; Zarith field/scalar arithmetic, bounded native byte/bit indices and byte/sign conversions |
| `test_phase1_integration` | absent → 4 | empty typed campaign, real existing authentication/record checks, bigint fuel/events and abstract digest observer |
| `test_integer_differential` | absent → 4 | checked decimal-to-bigint test inputs; finite comparator client |

No category-2 module remains in the required extraction surface. The baseline
manifest extraction contained 64 signature lines mentioning native `int`, and
the transcript extraction 42; these are line counts from the inventory, not
counts of independent obligations. Both paths were required by the release and
could overflow. Neither had an automated cross-language battery or a general
correspondence theorem. Source examples include `RecordCrosscheck.nat_digits`,
`parse_nat`, `crosscheck_budget_impl`, `ManifestLedger.ld_mismatch`,
`Orchestration.charge` and `stage1_cost`.

The native analogue was required only by `test_context_bundle` and the old
`ocaml` build target. In addition to arithmetic differences, it has reduced
records: Boolean findings instead of three-way outcomes with offending fields,
no candidate identifier in parsed candidates, reduced stage/witness evidence,
and loaded context without committed artifact bytes. Extraction already supplies
the required regression behavior. It remains solely as marked historical demo
source; its agreement is not release evidence and no equivalence proof exists.

Host machine integers remain for finite in-memory byte/string/list operations,
small fixture literals and the unchanged crypto byte/bit utilities. There is
no bigint-to-native conversion of unbounded semantic counters/coordinates in
the required wrappers. Python audit/oracle tooling uses Python's exact integers;
the OCaml AST checker uses host source locations and argument-array indices.

## Reproduced pre-repair divergences

A probe compiled against the untouched baseline generated modules and native
mirror produced the following actual output on this 64-bit environment:

```text
host max_int=4611686018427387903; exact max_int+1=4611686018427387904
manifest parse_nat: decoded=-4611686018427387904; remaining=""
native extracted charge: ACCEPTED, consumed=-4611686018427387904 (exact result rejects)
native extracted multiplication: max_int*2=-2; exact=9223372036854775806
hand-written charge: ACCEPTED, consumed=-4611686018427387904 (exact result rejects)
```

Inputs were `parse_nat (string_of(max_int+1))`,
`charge {budget=max_int; consumed=max_int} 1`, and `mul max_int 2`.
These are reproduced executable failures, not inferred hazards. The migrated
extractions now return the positive decoded value, reject the over-budget
charge, and return the exact positive product. The demo is removed from the
required path instead of receiving an independent bigint rewrite.

## Repairs and adversarial cases

`ExtractManifestAuthentication.v` and `ExtractTranscriptDigest.v` now import
`ExtrOcamlNatBigInt` and `ExtrOcamlZBigInt`, consistently with the kernel.
Manifest structural binary `Z` was not machine-width before this batch;
its migration provides a shared representation. No formal definition, theorem
statement or proof is changed. The additional integration driver extracts only
existing definitions; it introduces no new mathematics.

Existing test expectations remain; numeric fixture types are adapted. New cases
cover zero, `max_int`, `max_int+1`, larger-than-64-bit values around `10^80`,
addition/multiplication, equality/one-past fuel boundaries, huge decoded indices
and budgets, signed events around `-4*10^40`, and checked negative-nat rejection.
Record decimal decoding rejects negative/leading-zero forms and roundtrips huge
values through existing schemas. The manifest schema has **no numeric fields**:
positive authentication cases use huge typed configuration and campaign-record
fields; a numeric manifest identifier is rejected rather than inventing a schema.

Extracted `nat`/`positive` types are raw bigints. The mapping does not prove every
host-supplied bigint belongs to the formal domain. Test boundary conversions
reject negative naturals. A future production wrapper must preserve the same
invariants. Runtime resource limits remain; exact representation does not imply
unbounded execution resources.

## Integrated harness boundary

`ExtractPhase1Integration.v` creates one dependency closure of the existing
`ManifestPipeline.pipeline_ops`, validation/assessment and transcript projections.
It avoids nominal OCaml type incompatibilities between separate extractions.
`test_phase1_integration.ml` runs:

```text
typed empty campaign + signed manifest + existing record + bigint configuration
 → existing pipeline validation/authentication
 → exact validation fuel and record crosscheck
 → supplied signed-bigint events observed by an abstract digest hook
 → UNDERDETERMINED report and typed digest evidence
```

The test uses the existing SHA-256/Ed25519 fixture; the original crypto block
was moved unchanged and all prior vectors/rejections still run. Tampered manifest,
unauthorised signer and insufficient fuel are rejected. A record budget mismatch
produces an advisory finding while preserving the verdict, as specified.
All model, candidate-parser, stage and context hooks fail if invoked. It tests
composition at this bounded interface and passes no proof-bearing faithfulness
or policy-loader claims. It is not a full model/witness executable path and
does not implement capture/replay or a concrete transcript digest/encoding.

## Differential and fail-closed evidence

`differential.py` generates a temporary oracle `.v`, compiles it with `coqc`,
validates exactly one marked response per case, and compares the same inputs
with `test_integer_differential --cases`. Nonzero process results, compiler
errors, missing/duplicate responses, count differences and unequal values fail.
Every case records its oracle expression, scope, expected value and OCaml value
in generated `differential.json`.

The current generated battery has 59 passing cases: 38 evaluate actual Gallina
functions, and 21 use explicitly labelled Rocq `Z` numeric/arithmetic references.
It covers small nat arithmetic, project fuel charging and decimal parsing;
bigint signed equality/events; malformed decimal inputs; huge arithmetic,
decimal values and fuel boundaries; and `INADMISSIBLE`, `OBSTRUCTED`,
`UNDERDETERMINED` decisions on supplied typed control-flow fixtures.
A supplied complete-certificate/context fixture still returns UNDERDETERMINED:
version 0's EXACT branch is disabled. Those decision fixtures do not establish
witness validity or transcript faithfulness. Huge reference cases do not pretend
to evaluate enormous unary-natural Gallina decoders or charge directly.

**Passing differential tests demonstrate agreement on those cases. They are not
a general correspondence theorem.** The current battery also does not compare
all Stage-1/Stage-2/manifest/crypto computations with an independent oracle;
their existing regression harnesses remain separate evidence.

`integer_surface.py` checks approved drivers and generated-output coverage, then
uses compiler-libs `Parse.interface`/AST traversal to reject native `int` and
standard aliases, including nested/function types. It parses required wrappers
to reject historical `Orchestration` references; build/link commands are tokenised
and checked as well. Comments/strings do not trigger the structural checks.
The gate remains an audit of the current trusted extraction strategy, not a
proof about arbitrary future custom extraction mappings.

Real negative simulations after the repair, restored immediately:

- Appending a harmless `val harmless_native_probe : Int.t` to a generated
  interface made the structural gate exit 1; restoring it made the gate pass.
- Replacing the comparator binary temporarily with a test client returning `1`
  for `0+0` made the real oracle/comparator gate exit 1 and record FAILED;
  restoring the binary restored all 59 passing comparisons.

`make gate-tests` additionally passes 16 tests, including native type aliases,
comments, malformed interfaces, historical imports/linking, missing/duplicate
oracle replies, unequal results, and the existing Batch-1 fail-closed cases.
No project formal source is altered by these negative tests.

Each substantive implementation change passed its closest targeted tests and
then `make check` and `make release`. Final current-check evidence and counts are
regenerated by those commands in `implementation/release-audit/summary.json`.
The release checks the source manifest before and after a clean rebuild, never
refreshes it automatically, and reports **OPEN / NOT YET CLOSED** even on PASS.
The base SHA, working-tree status and manifest digest identify an uncommitted run.

## Files and retained priorities

Changes are confined to extraction drivers, `_CoqProject`/Makefile/ignore and
source-manifest bookkeeping, migrated/new harnesses, shared unchanged crypto
fixture, audit/comparator tooling, historical-demo labels, and current evidence
and status documentation. Existing substantive Rocq files are unchanged.
No commit or push is made.

- **BLOCKING:** model/artifact realisation, parser/loader and canonical-encoding
  acceptance, concrete transcript digest, capture/replay correspondence and
  explicit treatment of unresolved `faithful_transcript`/other theorem premises;
  full model/witness composition and final Phase-1 closure review.
- **SHOULD FIX:** broaden differential coverage beyond these finite cases,
  especially independent full decoder/Stage-1/Stage-2 oracles; specify checked
  numeric domains in eventual production wrappers; complete CI/dependency and
  reproducibility arrangements. These do not authorise any next batch.
- **DOCUMENTED RESIDUAL:** trusted extraction/mappings/compiler/Zarith/runtime
  and crypto implementation, bounded host utility integers, resource exhaustion,
  and the explicitly excluded historical native demo. Tests do not discharge
  premises or prove general executable equivalence or cryptographic security.

Policy-digest injectivity remains a formal premise, not a proved SHA-256 property.
Digest determinism remains distinct from collision resistance. No Batch-3/4
boundary is resolved or relabelled by this work. Stop after Batch 2.

## Exact Batch-2 source change inventory

- `.gitignore`
- `IMPLEMENTATION_STATUS.md`
- `MANIFEST.sha256`
- `NONCLAIMS.md`
- `PHASE_1_ARBITRARY_PRECISION_EXTRACTION.md`
- `PHASE_1_EXACT_INTEGER_CORRESPONDENCE.md`
- `PHASE_1_STATUS.md`
- `README.md`
- `RELEASE_CRITERIA.md`
- `TRUST.md`
- `implementation/Makefile`
- `implementation/README.md`
- `implementation/_CoqProject`
- `implementation/ocaml/manifest_crypto_fixture.ml`
- `implementation/ocaml/orchestration.ml`
- `implementation/ocaml/orchestration.mli`
- `implementation/ocaml/test_context_bundle.ml`
- `implementation/ocaml/test_integer_differential.ml`
- `implementation/ocaml/test_manifest_authentication.ml`
- `implementation/ocaml/test_orchestration_bigint.ml`
- `implementation/ocaml/test_phase1_integration.ml`
- `implementation/ocaml/test_transcript_digest.ml`
- `implementation/rocq/ExtractManifestAuthentication.v`
- `implementation/rocq/ExtractOrchestration.v`
- `implementation/rocq/ExtractPhase1Integration.v`
- `implementation/rocq/ExtractStage2.v`
- `implementation/rocq/ExtractTranscriptDigest.v`
- `implementation/scripts/check_integer_interfaces.ml`
- `implementation/scripts/differential.py`
- `implementation/scripts/integer_correspondence_baseline.json`
- `implementation/scripts/integer_surface.py`
- `implementation/scripts/release.py`
- `implementation/scripts/test_gates.py`
