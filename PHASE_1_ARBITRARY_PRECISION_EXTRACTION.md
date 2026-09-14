# Phase 1 -- closure-report obligation 3: arbitrary-precision extracted OCaml

Date: 2026-09-13/14. **First unit** (`ExtractOrchestration.v` +
`ExtractFibreWitnessKernel.v`, archives `phase1_arbitrary_precision_extraction_r{1,2}`):
revision 1 HELD -- candidate-coordinate passage untested, two misleading "the
ONE extraction" / "every other harness" scope claims; **revision 2
reviewer-concurred by source inspection and promoted**, ZIP sha256
`49fa79e16aa44b79c148ae10c78fb5750c5a6878d0b63b94c3de9def1cfe03c8`, committed
`bf81fe3`. **Second unit** (`ExtractStage2.v` + its five dependent harnesses,
archives `phase1_arbitrary_precision_stage2_r{1,2}`, 2026-09-14): revision 1
HELD -- an unpreserved test-input claim in `test_stage1_wrapper.ml`, three
scope statements left stale by this unit's own conversion, and an unused
`huge_index` binding/claim in `test_stage2.ml`; **revision 2
reviewer-concurred by source inspection and promoted**, ZIP sha256
`4c9436442d669224b8595131138215818843f220b0858015f10d81ac7843e230` -- see §7.

Status: **PARTIAL, cumulative across both units** -- not a claim that
obligation 3 is complete, and not a Phase 1 closure.

> Complete extracted-OCaml compilation, linking and execution with the
> required arbitrary-precision library.

Status before the first unit: **OPEN**, per `PHASE_1_STATUS.md`'s own words --
"Every extraction so far is `Z` / `nat` -> OCaml `int`... The exact-integer
verifier -- `Z` -> an arbitrary-precision type, compiled, linked and executed
-- is not done. (The verifying environment's `zarith` ships no `.cmi` files;
this remains an environment gap plus unfinished work.)"

Status after the first unit (promoted): **PARTIAL** -- obligation 3 stays open
until `ExtractStage2.v`, `ExtractManifestAuthentication.v`, and
`ExtractTranscriptDigest.v`, together with their validation harnesses, run
under arbitrary precision.

Status after the second unit (§7, reviewer-concurred and promoted): still
**PARTIAL** -- `ExtractStage2.v` and its five harnesses now run under
arbitrary precision; `ExtractManifestAuthentication.v` and
`ExtractTranscriptDigest.v` (and their harnesses) do not, so obligation 3
remains open. This is unit-promotion authority only, not a Phase 1 closure.

## 0. Revision history

**Revision 1** (author-reported): implemented the two harnesses and the
`ExtractOrchestration.v` fix described below. **HELD** by the reviewer on
two grounds: (1) `op_stage2_check`'s stub ignored the `pending_submission`
argument `run_stage1`/`run_stage2` actually threaded to it and returned a
separately constructed witness, so the harness could pass even if the
candidate coordinates were corrupted in transit -- only the witness
coordinates were genuinely checked; (2) `ExtractOrchestration.v`'s header and
`test_orchestration_bigint.ml`'s header both overclaimed scope ("the ONE
extraction in the project" and "unlike every other Extract*.v" -- false,
`ExtractFibreWitnessKernel.v` is also `ExtrOcamlZBigInt`/`ExtrOcamlNatBigInt`;
"every other harness in this project" -- imprecise, since it also describes
itself and its own companion harness). A third, independent finding (the
top-level `MANIFEST.sha256` omitting three tracked files -- `.gitignore`,
root `README.md`, `MANIFEST_REV15_CLOSURE.sha256` -- a pre-existing gap
unrelated to this unit's own file set) was folded into the same HOLD.

**Revision 2**: `op_stage2_check` now binds the `pending_submission` it is
actually called with and asserts `pending_candidate.candidate_x`/
`candidate_y` equal `huge_pos`/`huge_neg` before constructing the witness,
failing otherwise -- so the harness now fails if `run_stage1 -> run_stage2`
corrupts or drops the candidate data, not only if the (separately
constructed) witness is wrong. `ExtractOrchestration.v`'s header rewritten to
say it is "ONE OF TWO arbitrary-precision extractions" (naming
`ExtractFibreWitnessKernel.v` as the other) and to name the three remaining
native-int extractions explicitly; `test_orchestration_bigint.ml`'s header
rewritten to name the eight pre-existing validation-tier harnesses and its
own companion harness explicitly, rather than "every other". The top-level
`MANIFEST.sha256` regenerated exhaustively (100 entries covering all 101
delivered files bar itself), adding `.gitignore`, `README.md`, and
`MANIFEST_REV15_CLOSURE.sha256`. The r1<->r2 delta is exactly those two
Coq/OCaml source files plus the manifest; no proof, theorem, extraction
target, or previously promoted harness changed, and `ExtractFibreWitnessKernel.v`
is byte-identical to r1. **Reviewer-concurred by source inspection and
promoted.**

## 1. What was already there, dormant

Two extraction units, `ExtractOrchestration.v` (the central validation
pipeline) and `ExtractFibreWitnessKernel.v` (the T1 kernel), already used
`ExtrOcamlZBigInt` / `ExtrOcamlNatBigInt` (mapping `Z`/`nat`/`N`/`positive` to
`Big_int_Z.big_int`, Zarith's arbitrary-precision representation) since the
very first commit of this project. Both were listed in `_CoqProject` and
`coqc`'d by the Makefile's `rocq:` target -- but **only** `coqc`'d: neither
generated `.ml` was ever passed to `ocamlc`, no harness existed for either,
and the `Makefile`'s own `test:` target never touched them. `git log` shows
neither file has been modified since the repository's initial commit.

## 2. The environment claim in `PHASE_1_STATUS.md` does not hold here

That doc attributes the OPEN status partly to "the verifying environment's
`zarith` ships no `.cmi` files." That claim is accurate for at least one
zarith install location on this machine (the apt-packaged
`/usr/lib/ocaml/zarith`, which indeed has only `.cma`/`.cmxs`, no `.cmi`).
It is **not** accurate for the zarith install the Makefile itself already
resolves to: `ZARITH ?= $(OCAML_LIB)/zarith` where
`OCAML_LIB ?= $(shell opam var lib ...)`, which on this machine is
`/data/.opam/default/lib/zarith` -- a complete install with `z.cmi`,
`big_int_Z.cmi`, `.mli`, `.cmx`, `.cmxa`, `.a`. This is the exact same
directory `implementation/ocaml/test_manifest_authentication.ml` already
links against for its hand-rolled Ed25519/SHA-512 arithmetic (Zarith's `Z`
module, not `Big_int_Z`) -- so this project was already depending on a
`.cmi`-complete zarith for that harness; the claim that arbitrary-precision
*extraction* specifically was blocked by a `.cmi`-less zarith did not survive
contact with the Makefile's own variable resolution.

This is reported as an observation about **this** build environment, not as
a correction of what some other (e.g. the reviewer's, source-inspection-only)
environment provides. If the reviewer's environment differs, that is a fact
for them to report back, not something this revision can verify.

## 3. What was done

**`ExtractOrchestration.v`**: added `ExtrOcamlNativeString` to the import
list (it was missing -- without it, Coq's `string`/`ascii` extract as a
custom two-constructor inductive rather than native OCaml `string`/`char`,
which broke every string field the moment a harness tried to write an OCaml
string literal into one). No other change; still extracts exactly
`validate_campaign replay decide assess_validated verdict_of`. Header comment
rewritten to describe the file's actual, now-exercised, purpose.

**`ExtractFibreWitnessKernel.v`**: unchanged (it has no string-typed fields,
so the same gap didn't apply).

**Two new harnesses**, both compiled, linked (`-custom`, against the real
zarith `.cma`), and **executed** by `make check` (via the `test:` target,
not merely `coqc`'d):

- `implementation/ocaml/test_orchestration_bigint.ml` against
  `extracted_orchestration.ml`. Two scenarios, both driving the *real*
  exported entry points (not a reimplementation):
  1. `validate_campaign`'s authentication-fuel charging (`Orchestration.charge`)
     at a ~10^29 boundary -- accepts at exact equality with the fuel budget,
     rejects one unit past it. This magnitude cannot be represented, let
     alone correctly computed, by a native 63-bit OCaml `int`
     (`max_int = 4611686018427387903` on a 64-bit system) -- silent
     wraparound at this scale is exactly the failure class arbitrary
     precision exists to rule out.
  2. Z-valued candidate/witness coordinates (~4*10^40 magnitude, both signs)
     carried, unmodified, through `run_stage1 -> run_stage2 -> decide ->
     assess_validated`. Verified at **two** points (r1 checked only the
     second): the *candidate* coordinates `op_stage1_check` installs into the
     `pending_submission` are checked, bit-exact via `Big_int_Z.eq_big_int`,
     by `op_stage2_check` against the actual `pending_submission` argument
     `run_stage1`/`run_stage2` threads to it (not a value pulled from
     enclosing scope) -- and the *witness* coordinates in the returned
     `InadmissibleBody` are checked bit-exact against the same magnitudes.
- `implementation/ocaml/test_fibre_witness_kernel_bigint.ml` against
  `extracted_fibre_witness_kernel.ml`: a `CheckedWitness`-shaped scenario
  (`domainb`/`quantise`/`target` at ~4*10^40 magnitude, quantised
  observations agreeing while targets differ by sign) plus an `observation`
  call whose `preproc` performs a genuine arithmetic transform (negation) on
  a huge `Z` value, confirming the transform -- not just storage -- stays
  exact.

**`implementation/Makefile`**: `test:` target gained four new compile/link/run
steps (both harnesses, run first, before the existing native-int harnesses);
`clean:` gained the two new binaries. No existing target's behaviour changed.

**`implementation/_CoqProject`**: unchanged -- both `Extract*.v` files were
already listed.

`make check`: **EXIT 0**, **152** "Closed under the global context" (unchanged
-- no new Coq theorems, only an extraction-directive import and two new OCaml
files), `coqchk` 20 modules (unchanged), **10** harnesses (8 existing + 2 new),
no admits/axioms introduced.

## 4. What this establishes

- Arbitrary-precision extraction from this project's Coq sources is possible,
  compiles, links, and **executes correctly** against a real zarith install,
  including at magnitudes a native-int extraction could not represent at all.
- The specific arithmetic already used by the production pipeline
  (`Orchestration.charge`'s `Nat.leb`-gated addition) and the specific data
  shape used by candidate/witness coordinates (`list Z`) both survive the
  switch to `Big_int_Z.big_int` with no adaptation to the underlying Coq
  source beyond a missing string-extraction import.

## 5. What the first unit did NOT establish (residual as of its promotion)

- **The other three active extractions remained native-int.**
  `ExtractStage2.v`, `ExtractManifestAuthentication.v`, and
  `ExtractTranscriptDigest.v` -- which carry the bulk of this project's
  harness coverage (O6a-O6d, C1-C5, the manifest/ledger/audit/record/
  crosscheck suite, the Ed25519 signature path, the transcript-digest evidence
  suite) -- still used `ExtrOcamlNatInt`/`ExtrOcamlZInt`, unaffected by the
  first unit. There was no single build that ran the *whole* validation
  pipeline, end to end, under arbitrary precision; the first unit demonstrated
  the two previously-dormant, pipeline-level extractions (the central
  `Orchestration` entry points and the `FibreWitnessKernel`), not the
  concrete stage-1/stage-2/manifest checkers wired underneath them in the
  other harnesses. **`ExtractStage2.v` is now converted -- see §7.**
  `ExtractManifestAuthentication.v` and `ExtractTranscriptDigest.v` remain
  native-int, still out of scope.
- This project's status docs make no claim about closure-report obligation 4
  (capture/replay correspondence, canonical encoding, cross-language battery)
  or any of the other Phase 1 residuals listed in `PHASE_1_STATUS.md`, and
  neither unit under this obligation changes that.
- The `.cmi`-completeness finding in §2 is an observation about the build
  environment used for the first unit; it is not a claim about what tooling
  the reviewer has available, and does not by itself resolve any concern the
  reviewer may have about environment portability of this build step.

## 6. Harness scope note

Following this project's established practice (see e.g.
`PHASE_1_TRANSCRIPT_DIGEST.md`'s mock-digest disclosure), every new or
converted harness's header states exactly what it exercises and does not
silently extend to claims about other harnesses' coverage.

## 7. Second unit: `ExtractStage2.v` and its five dependent harnesses (2026-09-14)

**Revision history for this unit.** Revision 1 (author-reported) delivered
the conversion described below but was **HELD** on three grounds: (1)
`test_stage1_wrapper.ml` did not in fact preserve every existing test input
as claimed -- `submission_wire_length` (1 -> huge) and `max_wire_bytes` (100
-> huge) were silently bumped for *all* calls in the file even though
neither field is examined by `op_stage1_wrapper`'s stubbed `lower_parse`
path, adding no meaningful coverage, and the file's one shared target
predicate was changed from nonzero-based to sign-based, an unannounced
behavioural change to the converted baseline (harmless for that file's
existing non-negative test values, but not something revision 1 disclosed
as a change); (2) three present-tense scope statements went stale the
moment `ExtractStage2.v` itself was converted by this very unit --
`ExtractOrchestration.v`'s header still said "ONE OF TWO" / "the remaining
three... ExtractStage2.v"; `test_orchestration_bigint.ml`'s header still
listed `test_stage2.ml` et al. among harnesses linking against native-int
extractions; `PHASE_1_STATUS.md`'s "Next" section still said "converting the
other three extractions"; (3) `test_stage2.ml` defined `huge_index` and
claimed "a huge index" in its header but never used the binding -- dead
code advertising untested coverage.

**Revision 2** (this delivery): `test_stage1_wrapper.ml`'s `sub`/`cfg`
restored to the converted baseline (`submission_wire_length = bi 1`,
`max_wire_bytes = bi 100`) and its shared `ctx` restored to the nonzero-based
target (`not (eqbi (hd1 v) (bi 0))`, matching the original `<> 0`); a
*separate* `ctx_sign` (sign-based target) added and used only by the one new
huge-signed-coordinate case, which needs it (that file's default target
would otherwise call the huge-magnitude x/y "TargetsAgree" and never reach
`S1Pending`). `ExtractOrchestration.v`, `test_orchestration_bigint.ml`, and
`PHASE_1_STATUS.md` updated to say "ONE OF THREE" / "the remaining two
(`ExtractManifestAuthentication.v`, `ExtractTranscriptDigest.v`)" wherever
that claim is present-tense (revision 1's and the first unit's own
*historical* narrative paragraphs, e.g. this file's §0 and §5, are left as
history, per the reviewer's explicit instruction). `test_stage2.ml`'s unused
`huge_index` binding and its header's "a huge index" claim removed, with a
note that a huge pending/witness index is already covered by
`test_stage1.ml`/`test_stage1_wrapper.ml`.

Authorised scope, based on the first unit's promoted commit `bf81fe3`: convert
`implementation/rocq/ExtractStage2.v` and its five dependent harnesses
(`test_stage2.ml`, `test_stage1.ml`, `test_stage1_wrapper.ml`,
`test_context_resolution.ml`, `test_manifest_matching.ml`) to
`ExtrOcamlNatBigInt`/`ExtrOcamlZBigInt`, preserving every existing test case
and its expected result, adding beyond-63-bit cases, without touching any
Rocq theorem, proof, validation semantics, canonical encoding, digest
implementation, Ed25519 integration, transcript parsing/capture, or Phase 1
closure status. `ExtractTranscriptDigest.v` (and `ExtractManifestAuthentication.v`)
explicitly left untouched, so obligation 3 remains PARTIAL after this unit
regardless of its disposition.

**`ExtractStage2.v`**: `ExtrOcamlNatInt`/`ExtrOcamlZInt` replaced with
`ExtrOcamlNatBigInt`/`ExtrOcamlZBigInt`; `ExtrOcamlNativeString` unchanged
(strings stay native). Header rewritten to state the new representation and
to name `ExtractManifestAuthentication.v`/`ExtractTranscriptDigest.v` as the
two extractions that remain native-int. Extraction target list
(`stage2_check`, `adapter_stage2_check`, `stage1_semantic_check`,
`op_stage1_wrapper`, `wire_parse`, `preflight_check`, `eval_o3_check`,
`resolve`, `descriptor_eqb`, `manifest_policy_matches_impl`,
`manifest_context_matches_impl`, `Vector.of_list`/`to_list`, etc.) unchanged.
Confirmed (`grep`) the regenerated `.mli` contains zero occurrences of bare
`int` for any of these -- every former `Z`/`nat` site is `Big_int_Z.big_int`.
No naming collision with `Orchestration.policy`/`FibreWitnessKernel.Policy`
was reintroduced (`ExtractTranscriptDigest.v` was already isolated into its
own extraction output for exactly this reason, and remains untouched here).

**The five harnesses**: every `int`/`int vec`/`int list` annotation and
record field became `Big_int_Z.big_int`/`Big_int_Z.big_int vec`/`... list`;
every numeric literal became `bi <n>` (`Big_int_Z.big_int_of_int`) or, for
beyond-63-bit values, `big "<digits>"` (`Big_int_Z.big_int_of_string`);
every `=`/`<>` comparison or pattern-match guard on such a value or list of
such values became `Big_int_Z.eq_big_int` / a small `list_eqbi` helper
(`Big_int_Z.big_int` uses a boxed representation -- Zarith's own guidance is
to compare via `Z`/`Big_int_Z` functions, not OCaml's polymorphic `=`, so
every such site was converted, not just the new ones). Every pre-existing
test case's inputs and expected outcome are unchanged; only the OCaml
literal syntax carrying them changed.

Beyond-63-bit additions (magnitudes ~4*10^40 positive/negative, ~10^29 for
indices/thresholds -- all well past `max_int = 4611686018427387903` on a
64-bit system), placed where the underlying Coq logic genuinely performs
arithmetic or exact-equality comparison on the value in question (not force-
fitted into files where a field is merely stored/passed through unexamined):

- `test_stage1.ml` (`Stage1.stage1_semantic_check`, C1 `InputsEqual`): huge
  equal coordinates correctly trigger C1; one unit past that same huge value
  does *not* spuriously trigger C1 and correctly falls through to C5; a huge
  positive x / huge negative y (sign-based target) reaches a genuine
  `S1Pending` with a huge pending index, all three values verified bit-exact.
- `test_stage1_wrapper.ml` (`Stage1Wrapper.wire_parse`, B5 literal
  representability): a *second*, huge-threshold `parse_literal` variant
  (never substituted for the original 100-threshold one, so no pre-existing
  case's result can be affected) accepts exactly at a ~4*10^40 boundary and
  rejects one unit past it; a full success path (using a *separate*
  sign-based context, `ctx_sign`, needed only by this one case) with a huge
  positive x, huge negative y, and huge pending index, bit-exact.
  `submission_wire_length` / `max_wire_bytes` stay at the converted baseline
  (`bi 1` / `bi 100`, unchanged from the pre-existing values) for every
  pre-existing test in the file -- both fields are F.3-external
  (`lower_parse` is stubbed here) and unexamined by `op_stage1_wrapper`'s
  own logic, so a huge value there would add no meaningful coverage.
- `test_stage2.ml` (`Stage2.stage2_check`, `Stage2Adapter.fuel_ok`): a valid
  witness (`S2Valid`) with a huge positive x / huge negative y and huge,
  differing observation values, both observation vectors verified bit-exact;
  `fuel_ok`'s `4 * model_call_fuel <=? max_fuel_per_candidate` (a genuine
  multiplication + comparison, directly analogous to `Orchestration.charge`
  in the first unit) accepts at exact equality and rejects one unit short, at
  ~4*10^40 magnitude.
- `test_context_resolution.ml` (`ContextResolution.eval_o3_check`, O3's
  `list_zeqb` probe-input/observation equality): a dedicated huge-magnitude
  probe spec (wired to its own `loaded_inference_bytes` token, so it cannot
  interfere with the file's existing small-value probe/tests) accepts at
  exact match and rejects one unit off, on both the input and the
  observation side.
- `test_manifest_matching.ml`: **no beyond-63-bit case added**, and this is
  stated in the file's own header, not left implicit --
  `manifest_policy_matches_impl`/`manifest_context_matches_impl` never
  inspect `trusted_inputs.ti_config` at all (only string-typed manifest/
  policy/digest fields), so there is no arithmetic or numeric comparison in
  this file for such a case to exercise; adding one would be padding, not
  coverage.

**`implementation/Makefile`**: the five existing `extracted_stage2.mli`/`.ml`
compile lines and five harness link lines gained `-I $(ZARITH)` /
`-custom -I ocaml -I $(ZARITH) $(ZARITH)/zarith.cma` (mirroring the pattern
already used for `test_manifest_authentication` and the first unit's two
harnesses). No new harness was added -- the existing five were converted in
place, so the harness count stays at ten (unchanged from after the first
unit). No other target's behaviour changed.

`make check`: **EXIT 0**, **152** "Closed under the global context"
(unchanged -- no Rocq theorem, proof, or extraction target changed), `coqchk`
20 modules (unchanged), **10** harnesses, no admits/axioms introduced.

Archive `phase1_arbitrary_precision_stage2_r2` (ZIP sha256
`4c9436442d669224b8595131138215818843f220b0858015f10d81ac7843e230`, a
distinct name from the first unit's already-promoted
`phase1_arbitrary_precision_extraction_r{1,2}`, which are left unchanged as
reviewed artefacts; this unit's own r1 -- HELD -- is likewise left unchanged,
per the same convention). **Reviewer-concurred by source inspection and
promoted** (unit-promotion authority only -- not a Phase 1 closure; obligation
3 stays PARTIAL, since `ExtractManifestAuthentication.v` and
`ExtractTranscriptDigest.v` remain native-int).
