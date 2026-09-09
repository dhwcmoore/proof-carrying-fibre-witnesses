# Phase 1 — concrete stage-2 witness checker and its connection to the kernel

Date: 2026-09-05/06
Baseline: reviewer-issued Revision 15; orchestration proofs promoted
(`PHASE_1_ORCHESTRATION_PROOFS.md`). Revised twice after source review (four
corrections then the boundary-contract completion; see "Review corrections"
below).
**Reviewer concurrence:** the designated reviewer verified the archive integrity
and the source, and concurred with promotion of this bounded, conditional
kernel-connection unit, with two reporting corrections applied here:
`lookup_unique = None` means "no unique event (absent **or** duplicated)", not
"genuinely absent"; and the boundary predicates *condition* the conformance
theorem -- they are not runtime-enforced. Compilation evidence is from the
implementation machine; the reviewer's concurrence is by source inspection.

Two new modules, both `Qed` and axiom-free (`Print Assumptions` -> "Closed under
the global context" for every result below; `make assumptions` prints them).

One skeleton change: `Orchestration.v` `verifier_config` gains
`max_fuel_per_candidate : nat` (the `per_candidate_limits` field, already in the
frozen spec at AUDIT_POLICY_AND_EVIDENCE.md 2.2.5, previously unmodelled). This
is additive; the five orchestration proofs and the OCaml mirror are unaffected
(rebuilt clean).

## `implementation/rocq/Stage2.v` -- the checker (kernel-facing)

`stage2_check C rng fuel_ok x y eX0 eX1 eY0 eY1 : Stage2Verdict` -- a pure,
extraction-friendly function over the kernel carriers (`Vec Z n`), implementing
the frozen order **O6a -> O6b -> O6c -> O6d -> O4 -> O5 -> C4**
(VERDICT_SEMANTICS.md 6.5 / AUDIT_POLICY_AND_EVIDENCE.md 6):

- O6a all four keyed events present (`None` -> `S2ExecMissing`);
- O6b every event's input equals `preproc C x` / `preproc C y` -- inputs are
  carried on **every** outcome (`OeOk` / `OeFailed` / `OeExhausted`), so this is
  checked **before** O6c; a wrong input on a failed event is
  `S2ExecInputMismatch`, not a failure;
- O6c all four outcomes are `OeOk` (exhaustion dominates plain failure);
- O6d `fuel_ok` -- the caller-supplied
  `4 * model_call_fuel <= max_fuel_per_candidate` predicate;
- O4 the two X values agree and the two Y values agree;
- O5 `rng` (the policy-bound `expected_observation_range`) accepts both;
- C4 `quantise P o_x = quantise P o_y`, else `S2NotWitness`;
- otherwise `S2Valid o_x o_y`.

`stage2_valid_forces`: `S2Valid o_x o_y` implies `eX0 = Some (OeOk (preproc C x)
o_x)`, `eY0 = Some (OeOk (preproc C y) o_y)`, and `quantise P o_x = quantise P
o_y`.

**`stage2_valid_checked_witness`**: `Stage1Evidence C x y` (the C1/C2/C3/C5 facts
stage 1 establishes) plus `stage2_check ... = S2Valid o_x o_y` gives
`FibreWitnessKernel.CheckedWitness (context_policy C) x y o_x o_y`.

**`stage2_valid_observation_binding`**: `ObservationBinding C x o_x /\
ObservationBinding C y o_y` follows from `S2Valid` **and** `slot_faithful C` for
the two acquired "0"-repeat events -- the F.3 transcript-faithfulness residual
assumption (CLAIM_AND_DEFINITIONS.md 3.2.2 / 5.2). The checker never establishes
it; O4 (repeatability) does not imply it.

## `implementation/rocq/Stage2Adapter.v` -- as an `op_stage2_check`

`adapter_stage2_check : resolved_context -> verifier_config -> exec_transcript ->
pending_submission -> stage2_result` -- parses `list Z` into `Vec Z n`,
re-establishes C1/C2/C3/C5 locally, computes O6d's `fuel_ok` from `cfg`, runs
`stage2_check`, maps `Stage2.stage2_fail` to `Orchestration.o_reason`.

### Boundary conditions (hypotheses that scope the conformance theorem)

These are Coq predicates that **condition** `adapter_reporting_conformance`;
the adapter does **not** enforce them at runtime. Connecting them to stage 1,
the parser and capture is an outstanding integration obligation (table below).

Two dimensional-well-formedness predicates, relative to the adapter's `C`:

- **`adapter_candidate_wf ps`**: `length (candidate_x (pending_candidate ps)) =
  n_in` and likewise for `candidate_y`.
- **`transcript_stage2_wf tr idx`**: for each of the four stage-2 keys, if
  `lookup_unique tr key = Some ev` then `length (event_input ev) = n_pre` and,
  when `event_outcome ev = ExecOk obs`, `length obs = n_obs`
  (`event_dims_ok`).

Proved that these exclude the adapter's parsing-failure branches:

- **`adapter_candidate_wf_parses`**: under `adapter_candidate_wf ps`, both
  `parse_vec n_in` calls return `Some` -- so the `WitnessCheckObstructed
  ExecFailure` catch-all is not reached.
- **`slot_at_wf_none_iff`**: under `slot_present_wf`, `slot_at tr idx r rep =
  None` **iff** `lookup_unique tr (s2_key idx r rep) = None` (no unique event
  for that key -- absent or duplicated) -- a present, uniquely-keyed but
  malformed event cannot masquerade as a lookup failure.
- **`stage2_check_missing_char`** (in `Stage2.v`): `stage2_check … =
  S2Obstructed S2ExecMissing` implies one of the four slots is literally `None`
  (the reason is produced only by O6a, never inside the all-present branch).

Reporting conformance, **scoped to those conditions**:

- **`adapter_reporting_conformance`**: under `adapter_candidate_wf ps` and
  `transcript_stage2_wf tr (pending_index ps)`, (a) the candidate-parse fallback
  branch is not taken, and (b) the adapter reports
  `WitnessCheckObstructed ExecMissing` **only** when at least one stage-2 key
  has no unique event in `tr` -- `lookup_unique … = None`, i.e. absent or
  duplicated (`lookup_unique` fails on both).

Proved for arbitrary inputs (no well-formedness hypothesis needed -- a
`ValidWitness` result already forces well-formed slots):

- **`adapter_satisfies_index_contract`**: any `primitive_ops` whose
  `op_stage2_check` is this adapter satisfies
  `Orchestration.stage2_witness_index_contract` -- the premise the repaired
  `REP1_not_run_has_no_witness` carries.
- **`adapter_valid_supplies_checked_witness`**: a `ValidWitness w` result exposes
  `x y : Vec Z n_in`, `o_x o_y : Vec Z n_obs` with `w`'s list fields equal to
  their `to_list`, and `CheckedWitness (context_policy C) x y o_x o_y`.
- **`adapter_valid_observation_binding`**: `ObservationBinding` for x and y,
  conditional on `transcript_faithful_for tr (pending_index ps)`.

### Integration obligations (outstanding until implemented)

`adapter_reporting_conformance` is scoped to two conditions that a
Phase-1-complete pipeline must establish:

| Condition | Established by | Status |
|---|---|---|
| `adapter_candidate_wf ps` | the concrete `stage1_check` -- tier B4 parses `x`, `y` to exactly `n_in` `Z` values (`S1Rejected InputStructureError` otherwise), so any `Pending` submission satisfies it | not yet connected (`stage1_check` is abstract; see `PHASE_1_ORCHESTRATION_PROOFS.md`) |
| `transcript_stage2_wf tr idx` (offline) | `parse_transcript` -- atomic; a `Wellformed` transcript rejects any wrong-length event vector | not yet implemented (`parse_transcript` is an abstract `primitive_ops` member) |
| `transcript_stage2_wf tr idx` (live) | `capture` -- emits `exec_event`s with typed `Vec` inputs, so a wrong length is not representable | not yet implemented |

Until those are wired, the conformance claim holds only relative to the
hypotheses, and this is stated where the theorem is used.

## Executable exercise

`implementation/rocq/ExtractStage2.v` extracts with `Z`/`nat` -> OCaml `int`, Coq
string -> OCaml `string` (no bignum, no Coq-string runtime).

**This extraction is NOT the exact-integer verifier.** It carries no
overflow-safety guarantee -- the machine-int arithmetic here can wrap, unlike the
Coq `Z` the proofs are about. The exact-integer verifier extracts `Z` to an
arbitrary-precision type (deferred -- the verifying environment's `zarith` ships
no interface files). This extraction is for exercising control flow and verdicts
only.

`implementation/ocaml/test_stage2.ml` (`make test`) exercises, on a concrete
1-dimensional context:

- a valid witness; a not-a-witness (C4);
- every obstruction: `S2ExecMissing`, `S2ExecInputMismatch`, `S2ExecFailure`,
  `S2ExecFuelExhausted` (both from O6c exhaustion and from O6d), `S2NonDeterministic`,
  `S2ObsOutOfRange`;
- **O6b before O6c**: wrong input on a failed event -> `S2ExecInputMismatch`;
- **O6d fuel boundary**: `fuel_ok = false` on otherwise-valid events;
- the `o_reason` mapping;
- the adapter end-to-end: `ValidWitness` (index preserved), O6d via `cfg`,
  `S2NotAWitness InputsEqual` (C1 re-check), `WitnessCheckObstructed ExecMissing`
  (missing events);
- **malformed candidate length** -> `WitnessCheckObstructed ExecFailure` (not
  `InputsEqual`);
- **malformed event-vector length** -> `WitnessCheckObstructed ExecMissing`
  (event present but unusable; excluded upstream by atomic `parse_transcript`).

`make check` exits 0: four `.v` modules compile; `coqchk` checks
`PCFW.FibreWitnessKernel`, `PCFW.Orchestration`, `PCFW.Stage2`,
`PCFW.Stage2Adapter`; `make assumptions` shows all Stage2 / adapter results
"Closed under the global context"; `make test` prints `PASS` for both harnesses.

## Review corrections (this revision)

1. **O6d implemented.** `verifier_config` gains `max_fuel_per_candidate`;
   `adapter_stage2_check` computes `fuel_ok = 4 * model_call_fuel <=?
   max_fuel_per_candidate` and passes it to `stage2_check`, which returns
   `S2ExecFuelExhausted` on failure. Campaign-level charging is separate and does
   not replace this.
2. **O6a -> O6b -> O6c order preserved.** `obs_event` carries the input on
   `OeFailed` / `OeExhausted`; `stage2_check` checks O6b (inputs) before O6c
   (outcome success).
3. **Boundary contracts formalised, proved to exclude the parsing-failure
   branches, and used to scope the reporting claim.**
   `adapter_candidate_wf` / `transcript_stage2_wf` / `event_dims_ok` are Coq
   predicates; `adapter_candidate_wf_parses`, `slot_at_wf_none_iff` and
   `stage2_check_missing_char` prove the fallback / spurious-`ExecMissing`
   branches are unreachable under them; `adapter_reporting_conformance` states
   the truthful-reporting claim relative to those conditions. Their
   establishment by the concrete `stage1_check`, `parse_transcript` and
   `capture` is recorded as an outstanding integration obligation (table
   above).

   (A second review noted the first revision only *documented* these; this
   revision makes them Coq predicates and *proves conformance under them* via
   the supporting theorems. They remain hypotheses -- the adapter does not
   enforce them at runtime; that is the integration obligation below.)
4. **Machine-int extraction explicitly scoped to the test harness** -- see the
   `ExtractStage2.v` header and the "Executable exercise" note above.

## Still open in Phase 1

- A concrete `preproc` / `model` / `quantise` / `domainb` / `target` bound to
  the committed model artifact and inference spec; an O3-resolved
  `resolved_context` carrying that context rather than the current string stub.
- `stage1_check` carrying `Stage1Evidence` forward instead of the adapter
  re-checking C1/C2/C3/C5.
- Physical capture/replay correspondence, canonical encoding, parser/boundary
  acceptance, the exact-integer (arbitrary-precision) extraction and its
  compile/link/execute, cross-language agreement battery.
- `transcript_faithful_for` remains a stated F.3 assumption, by design.
