# Phase 1 -- closure-report obligation 3: arbitrary-precision extracted OCaml

Date: 2026-09-13 (revision 1 HELD -- candidate-coordinate passage untested,
two misleading "the ONE extraction" / "every other harness" scope claims;
**revision 2 reviewer-concurred by source inspection and promoted**, ZIP
sha256 `49fa79e16aa44b79c148ae10c78fb5750c5a6878d0b63b94c3de9def1cfe03c8`).
Status: **reviewer-concurred and promoted as PARTIAL progress on obligation
3** -- not a claim that obligation 3 is complete, and not a Phase 1 closure.

> Complete extracted-OCaml compilation, linking and execution with the
> required arbitrary-precision library.

Status before this unit: **OPEN**, per `PHASE_1_STATUS.md`'s own words --
"Every extraction so far is `Z` / `nat` -> OCaml `int`... The exact-integer
verifier -- `Z` -> an arbitrary-precision type, compiled, linked and executed
-- is not done. (The verifying environment's `zarith` ships no `.cmi` files;
this remains an environment gap plus unfinished work.)"

Status after this unit: **PARTIAL** (see "What this does NOT establish"
below -- this is a real, tested capability, not a full conversion of the
project's numeric extraction; obligation 3 stays open until `ExtractStage2.v`,
`ExtractManifestAuthentication.v`, and `ExtractTranscriptDigest.v`, together
with their validation harnesses, run under arbitrary precision).

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

## 5. What this does NOT establish (residual, flagged for reviewer disposition)

- **The other three active extractions remain native-int.**
  `ExtractStage2.v`, `ExtractManifestAuthentication.v`, and
  `ExtractTranscriptDigest.v` -- which carry the bulk of this project's
  harness coverage (O6a-O6d, C1-C5, the manifest/ledger/audit/record/
  crosscheck suite, the Ed25519 signature path, the transcript-digest evidence
  suite) -- still use `ExtrOcamlNatInt`/`ExtrOcamlZInt` and are unaffected by
  this revision. There is no single build that runs the *whole* validation
  pipeline, end to end, under arbitrary precision; this revision demonstrates
  the two previously-dormant, pipeline-level extractions (the central
  `Orchestration` entry points and the `FibreWitnessKernel`), not the
  concrete stage-1/stage-2/manifest checkers wired underneath them in the
  other harnesses.
- Converting the other three files (and their ~7 harnesses' numeric literals)
  to `Big_int_Z` was judged out of scope for this revision -- a much larger,
  separately-reviewable lift with its own regression risk against already
  reviewer-concurred and promoted harness coverage.
- This revision does not address, and makes no claim about, closure-report
  obligation 4 (capture/replay correspondence, canonical encoding, cross-
  language battery) or any of the other Phase 1 residuals listed in
  `PHASE_1_STATUS.md`.
- The `.cmi`-completeness finding in §2 is an observation about the build
  environment used for this revision; it is not a claim about what tooling
  the reviewer has available, and does not by itself resolve any concern the
  reviewer may have about environment portability of this build step.

## 6. Harness scope note

Following this project's established practice (see e.g.
`PHASE_1_TRANSCRIPT_DIGEST.md`'s mock-digest disclosure), both new harnesses'
headers state exactly what they exercise and do not silently extend to
claims about the machine-int harnesses' existing coverage, which is
unaffected and unchanged.
