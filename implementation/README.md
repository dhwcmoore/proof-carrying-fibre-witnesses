# Compiler-checkable orchestration skeleton

This directory pins the orchestration algebra that Revision 14 expressed as
pseudocode. It is intentionally small enough to review as code.

## What is real

`rocq/Orchestration.v` contains ordinary Gallina definitions. The four governing
functions are total by construction and contain no pseudocode:

```text
validate_campaign : primitive_ops -> trusted_inputs -> validation_result
replay             : primitive_ops -> authenticated_campaign -> context_bundle
                     -> verifier_config -> policy_document -> policy ->
                     fuel_ledger -> exec_transcript -> replay_result
decide             : primitive_ops -> replay_result -> authenticated_campaign ->
                     trusted_inputs -> exec_transcript -> transcript_evidence ->
                     commitment_evidence -> assessment_outcome
assess_validated   : primitive_ops -> trusted_inputs -> validation_result ->
                     transcript_source -> assessment_outcome
```

The functions encode these decisions directly:

- validation occurs outside `assess_validated` and is supplied exactly once;
- validation's nine checks use first-failure precedence;
- every fuel charge precedes the work it pays for;
- stage-1 fuel exhaustion is a terminal return;
- replay constructs `Done` and `NotRun` slots;
- decision precedence is witness, campaign obstruction, all-checked-obstructed,
  v0 exactness (dead), then underdetermined;
- malformed offline input is handled before replay;
- live and offline transcript provenance remain distinct.

## What is abstract

`primitive_ops` is the typed boundary for parsing, signature verification,
hashing, the stage-1 and stage-2 semantic checks, O1/O2, O3, record
cross-checking and certificate/report construction. Each member is a total
function. Phase 1 must replace each member with its implementation and prove its
contract.

## Deliberate proof holes

The file includes named `Admitted` obligations for `(T2-sound)`, `(T2-complete)`,
stage-1 terminality, v0 exactness unreachability and validation fuel
reachability. This repository therefore must not yet run the production
forbidden-token gate.

`(REP1)` is **no longer** among them. The earlier
`REP1_not_run_has_no_witness` quantified over an arbitrary `list stage2_slot`
and was *false* (e.g. `[mkStage2Slot 0 NotRun; mkStage2Slot 0 (Done r)]` with
`r` a `ValidWitness` of index `0`): its `Admitted` made `PCFW.Orchestration`
inconsistent as an imported theory. It is restated over slot lists that are
well formed in the sense a real `replay` output is — distinct slot indices, and
every `ValidWitness` slot carrying a witness whose index is its own slot index
(`stage2_slots_wf`) — and proved (`Qed`). `replay_stage2_wf` discharges that
predicate for every `replay` output, given the stage-2 witness-index contract
`stage2_witness_index_contract` on `op_stage2_check`; `REP1_replay_not_run_has_no_witness`
is the direct corollary for `replay` outputs. `make assumptions` shows all three
are `Closed under the global context`.

Two supporting repairs:

- **Orchestration owns the pending index.** `run_stage1` now builds each pending
  submission with `with_pending_index i`, so pending indices are the checking
  positions by construction; `run_stage1_pending_nodup` proves them distinct. No
  index value from `op_stage1_check` is trusted.
- **Stage-2 witness-index contract.** `stage2_witness_index_contract ops` states
  that a `ValidWitness w` returned by `op_stage2_check` for `ps` has
  `witness_index w = pending_index ps`. Phase 1 must discharge it for the real
  `op_stage2_check`.

## Totality case: `CtxNotNeeded` with pending candidates — resolved

Revision 14 permits a caller to supply `CtxNotNeeded` together with a valid
campaign whose stage 1 *completes* with pending candidates. That pairing is
**never produced by `capture`**, but a total `replay` must return a truthful
result for an arbitrary bundle (`VERDICT_SEMANTICS.md` §6.6 scopes `(REP1)` over
an arbitrary `context_bundle`).

This is distinct from **terminal stage-1 fuel exhaustion**, where `capture`
legitimately returns `CtxNotNeeded` even though an earlier submission already
reached `Pending`; `replay` handles that in the `Stage1Stopped` branch
(`NoContextNeeded`, `clo = Some CampaignFuelExhausted`) before the bundle is ever
consulted. The missing case is precisely **`Stage1Complete` ∧ `pending ≠ []` ∧
`cb = CtxNotNeeded`**.

The skeleton now reports it as: `clo = Some InconsistentContextBundle` (a new
nullary `campaign_obstruction`, sibling of `CampaignFuelExhausted`), `context =
ContextBundleInconsistent` (a new nullary `context_state` — **no reason, no
findings**, since no digest comparison or probe ran), every pending stage-2 slot
`NotRun`, `decide` → `OBSTRUCTED` with obligation
`reconstruct_or_supply_context_bundle`.

The new case is deliberately **not** a `ctx_reason`. `ctx_reason`
(`ArtifactMismatch | SpecMismatch | RepNotReproduced`) is the shared O1/O2/O3
outcome type used by `CtxUnavailable`, `PreflightFail` and `eval_o3`; adding a
constructor there would make `CtxUnavailable <it>` constructible and the
unchanged `CtxUnavailable` branch would emit it with a fabricated `O1` finding.
Leaving `ctx_reason` alone makes that a type error.
`ocaml/test_context_bundle.ml` (run by `make test`) exercises the `CtxNotNeeded`
path, checks the real `CtxUnavailable ArtifactMismatch` path is unchanged, and
confirms terminal stage-1 exhaustion is unaffected.

The new constructors are a proposed amendment to `VERDICT_SEMANTICS.md` §2/§6
and the `AUDIT_POLICY_AND_EVIDENCE.md` §2.2 encoding — see
`CONTEXT_BUNDLE_AMENDMENT.md`. Phase 1 may alternatively make the pairing
unconstructible with a dependent input type.

## Build

Expected toolchain: Rocq/Coq 8.18.0 and OCaml 4.14.1.

```sh
make check
```

**Built and verified** (a different session, with `coqc`/`coqchk`/`ocamlc` 8.18.0 /
4.14.1 present) after four source fixes and one `Makefile` fix, all applied in
this tree:

- `rocq/Orchestration.v` line ~490: `Open Scope string_scope` (line 3) rebinds
  `++` to `String.append` for the rest of the file. Inside a bare tuple literal
  `(rev slots_rev ++ stage2_not_run pending, fuel, Some CampaignFuelExhausted)`
  there is no top-down expected type to force list scope, so `++` resolved to
  string append and elaboration failed with "expected type string". Two other
  occurrences of `++` happened to sit as direct constructor arguments with a
  statically known `list` type and were unaffected by the same shadowing. Fixed
  by scoping the one bad occurrence: `(... )%list`.
- `rocq/Orchestration.v` lines 513, 754: `Import String` shadows the unqualified
  `length` from `List`, so bare `length (authenticated_submissions ac)` (a
  `list candidate_submission`) resolved to `String.length : string -> nat` and
  failed to typecheck. Fixed by qualifying both call sites as `List.length`.
- `ocaml/orchestration.ml`, `stage2_not_run`: `pending_submission`, `stage1_result`,
  and `stage2_result` all declare a field named `index`. OCaml's unannotated
  field-disambiguation binds a bare `p.index` to the most recently declared type
  in scope (`stage2_result`), which then forced `run_stage2`'s `pending`
  parameter to the wrong type and mis-reported the resulting error at the
  `stage2_check` call site several lines away. Fixed by annotating both the
  outer parameter and the inner lambda parameter as `pending_submission`.
- `ocaml/orchestration.ml`, `decide`: the same mechanism, with `authenticated_campaign`
  and `trusted_inputs` both declaring `submissions` / `manifest` / `record` /
  `completeness`. `decide`'s unused `_ti` parameter left `ac`'s type to be
  inferred from `ac.completeness` inside `decide`'s own body, which bound to
  `trusted_inputs` (declared later) instead of `authenticated_campaign`,
  surfacing as a mismatch at the call site in `assess_validated`. Fixed by
  annotating `decide`'s `ac` parameter explicitly.
- `Makefile`: `ocamlc -c ocaml/orchestration.mli` / `.ml` compiled the `.mli`
  successfully but then could not find its own `.cmi` when compiling the `.ml`,
  because this `ocamlc` does not implicitly add a source file's own directory to
  its search path when it differs from the invocation's working directory.
  Fixed by adding `-I ocaml` to both `ocaml:` recipe lines.

After those five fixes: `coqc` builds both `rocq/Orchestration.v` and
`rocq/ExtractOrchestration.v` clean; `coqchk` reports "Modules were successfully
checked"; `Print Assumptions` on each of the six named theorems shows exactly
that theorem as its own sole axiom — no stray `Admitted`s leaked in from
elsewhere; extraction regenerates `ocaml/extracted_orchestration.{ml,mli}`; the
hand-written `ocaml/orchestration.{ml,mli}` skeleton compiles clean.

**Not verified**: linking the Coq-*extracted* OCaml end-to-end. `ExtrOcamlZBigInt`
extracts `Z`/`positive`/`nat` to `Big_int_Z`-backed big integers, and the `zarith`
install in the verifying environment (1.13, apt-packaged) ships only `.cma`/`.cmxs`
archives with no `.cmi` interface files at all — not specific to this project, a
gap in that environment's `zarith` package. The generated `.ml`/`.mli` themselves
were not edited and are presumed correct pending a `zarith` install with dev
interfaces present.

### Follow-up build (this repo): REP1 repair + context-bundle reporting

Applied in this tree and rebuilt with `coqc`/`coqchk`/`coqtop`/`ocamlc` 8.18.0 /
4.14.1:

1. `REP1_not_run_has_no_witness` restated over `stage2_slots_wf` slot lists and
   proved (`Qed`), with `replay_stage2_wf` + `REP1_replay_not_run_has_no_witness`
   connecting it to `replay` outputs. Supporting: `with_pending_index` in
   `run_stage1` (+ `run_stage1_pending_nodup`), and the
   `stage2_witness_index_contract` primitive obligation.
2. `context_state` gains `ContextBundleInconsistent` and `campaign_obstruction`
   gains `InconsistentContextBundle` (both nullary); `ctx_reason` is unchanged
   so `CtxUnavailable`/`PreflightFail` cannot carry the new case; the `replay`
   `CtxNotNeeded` branch and `obstruction_obligation` updated; no fabricated
   finding.
3. OCaml mirror (`ocaml/orchestration.{ml,mli}`) updated to match; the pending
   index is orchestration-assigned there too.
4. `rocq/PrintOrchestrationAssumptions.v` + `make assumptions`; new `make test`
   runs `ocaml/test_context_bundle.ml`.

`make check` exits 0: `coqc` builds all four `.v` files; `coqchk` → "Modules
were successfully checked" (`PCFW.FibreWitnessKernel`, `PCFW.Orchestration`);
`make assumptions` shows `REP1_not_run_has_no_witness`,
`REP1_replay_not_run_has_no_witness` and `replay_stage2_wf` as
`Closed under the global context` and the five still-`Admitted` obligations
(`T2_sound`, `T2_complete`, `stage1_over_is_terminal`, `exact_unreachable_v0`,
`validation_fuel_obstructed_unreachable_when_sufficient`) each as their own sole
axiom; extraction regenerates `ocaml/extracted_orchestration.{ml,mli}` (carrying
the new constructor); the hand-written skeleton compiles; `make test` prints
`PASS`.

**Still not verified**: linking the Coq-*extracted* OCaml against `zarith` (this
environment's `zarith` ships no `.cmi` files — an environment gap, not a source
defect).

## Current status (this section only; not updated per Phase 1 unit)

`primitive_ops` (§ "What is abstract" above) is, as of this section, no longer
uniformly abstract: every validation-tier member EXCEPT `op_transcript_digest`
(discussed separately below) has a concrete implementation, each in its own
`rocq/*.v` module wired into `ManifestPipeline.pipeline_ops`
(`ManifestAuthentication`, `ManifestLedger`, `ManifestAudit`,
`CampaignRecord`, `RecordCrosscheck`, `CompletenessWellformed`) -- see
`PHASE_1_STATUS.md`, the authoritative, kept current per-unit ledger, for
exact status and reviewer disposition of each.
`op_stage1_check` / `op_preflight` / `op_eval_o3` / `op_stage2_check` are
concrete and wired (`Stage1Wrapper`, `ContextResolution`, `Stage2Adapter`,
`PipelineWiring`). The five "Deliberate proof holes" `Admitted` obligations
listed above were all discharged in `PHASE_1_ORCHESTRATION_PROOFS.md`; none
remain `Admitted` in `rocq/Orchestration.v`.

`op_transcript_digest : exec_transcript -> digest`, the last `primitive_ops`
member, has an **author-reported** (not yet reviewer-concurred, not promoted)
treatment in `rocq/TranscriptDigest.v` -- an interface-and-evidence-binding
unit, not a cryptographic implementation: it stays a primitive hook (its
normative target, `digest_v1("pcfw.exec_transcript.v1", to_cv(tr))`, is an
abstract Section `Variable`, F.3), proves ordinary functional determinism (not
collision resistance), and proves that `validate_campaign` / `replay` / the
campaign verdict are all independent of which function occupies this hook --
only `transcript_evidence` can carry the digest it produces. See
`PHASE_1_TRANSCRIPT_DIGEST.md`.

If that unit is promoted, every named `primitive_ops` member will have either
a concrete implementation or an explicit, contract-bound primitive treatment.
Phase 1 remains open regardless -- `parse_transcript` / capture
well-formedness, `transcript_stage2_wf`, digest-function correctness,
artefact binding to the committed model/inference spec, arbitrary-precision
extraction, and the final closure review are all separate, still-open
obligations. See `PHASE_1_STATUS.md` for exact, current status.

