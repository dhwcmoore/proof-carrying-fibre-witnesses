# Phase 1 -- F.3 stage-1 parser wrapper; discharge of `op_stage1_sound`

Date: 2026-09-06
Baseline: `PHASE_1_ORCHESTRATION_INVARIANT.md` (reviewer-concurred, promoted).
One new module, `implementation/rocq/Stage1Wrapper.v`, `Qed` and axiom-free.

`op_stage1_check` receives a raw `candidate_submission`. This wrapper wire-parses
it, then -- on success -- runs `Stage1.stage1_semantic_check` under the committed
context `C`, and discharges `Stage1Invariant.op_stage1_sound`.

## `wire_parse` and `op_stage1_wrapper`

Section parameters (F.3 inputs, abstract):

- `lower_parse : verifier_config -> policy_document -> candidate_submission ->
  b_reason + (list token * list token)` -- tiers B1a/B6/B1b/B1c/B2/B3 as one
  structural parse to two coordinate token lists, or a `b_reason`.
- `parse_literal : token -> option Z` -- B5, one integer literal to a `Z` within
  its declared `integer_type`, or `None`.
- `semantic_digest_of : parsed_candidate -> digest` -- the
  `digest_v1 "pcfw.candidate.v1"` of the parsed candidate.

```
wire_parse cfg pd sub :=
  match lower_parse cfg pd sub with
  | inl r         => WireReject r                         (* B1a/B6/B1b/B1c/B2/B3 *)
  | inr (xs, ys)  =>
      if length xs = n_in AND length ys = n_in            (* B4 -- checked FIRST *)
      then match map parse_literal xs, map parse_literal ys with
           | Some xz, Some yz => WireOk {x = xz; y = yz}
           | _                => WireReject MalformedIntegerLiteral   (* B5 *)
           end
      else WireReject InputStructureError
  end

op_stage1_wrapper cfg pd p i sub :=
  let sd := submission_digest sub in
  match wire_parse cfg pd sub with
  | WireReject r => {s1_index=i; s1_submission_digest=sd; s1_verdict=S1Rejected r; s1_findings=[]}
  | WireOk c     => {s1_index=i; s1_submission_digest=sd;
                     s1_verdict = stage1_semantic_check C sd (semantic_digest_of c) i c;
                     s1_findings=[]}
  end
```

## Precedence (the ordering detail flagged in review)

The semantic checker folds B4 with C1/C2/C3/C5; the full wire order is
**B4 -> B5 -> C1**. `wire_parse` checks the **B4 dimension before the B5
literal check**, and runs entirely before the semantic checker, so:

- **`wire_parse_B4_before_B5`**: if `lower_parse` yields token lists but a
  coordinate has the wrong length, `wire_parse = WireReject InputStructureError`
  -- even if a literal is also unrepresentable. B5 never outranks B4.
- B5 precedes C1 because `wire_parse` (which produces `MalformedIntegerLiteral`)
  completes before `stage1_semantic_check` (which produces `InputsEqual`) is
  called.

## Proved (`Print Assumptions`: "Closed under the global context" for all)

1. **`wrapper_reject_not_pending`**: `wire_parse cfg pd sub = WireReject r`
   implies `op_stage1_wrapper cfg pd p i sub = {s1_index=i;
   s1_submission_digest=submission_digest sub; s1_verdict=S1Rejected r;
   s1_findings=[]}` -- a rejection, never `S1Pending`.
2. **`wrapper_pending_binds`**: `s1_verdict (op_stage1_wrapper …) = S1Pending ps`
   implies `wire_parse … = WireOk c` and `pending_candidate ps = c`,
   `pending_submission_digest ps = submission_digest sub`,
   `pending_semantic_digest ps = semantic_digest_of c`, `pending_index ps = i`,
   `pending_findings ps = []` -- exactly (via `Stage1.stage1_pending_identity`).
3. **`wrapper_fields`**: `s1_index` / `s1_submission_digest` / `s1_findings` are
   `i` / `submission_digest sub` / `[]`; on `WireOk c`, `s1_verdict` is literally
   `stage1_semantic_check C (submission_digest sub) (semantic_digest_of c) i c`.
4. **`wrapper_op_stage1_sound`**: any `primitive_ops` whose `op_stage1_check` is
   `op_stage1_wrapper` satisfies `Stage1Invariant.op_stage1_sound C` -- the
   pending-output soundness contract the orchestration invariant assumes. Proof:
   a `WireReject` gives `S1Rejected`, not `S1Pending`; a `WireOk` gives a
   semantic verdict, and `Stage1Invariant.stage1_pending_invariant` turns a
   semantic `S1Pending` into `pending_invariant C ps`.

Chaining `wrapper_op_stage1_sound` with `Stage1Invariant.replay_op_stage2_local`
and `adapter_c_recheck_redundant` gives an unconditional (modulo the F.3
externals below) redundancy of the stage-2 adapter's C-recheck for a
concrete wrapper-backed `op_stage1_check`.

## Executable exercise

`op_stage1_wrapper` / `wire_parse` extracted via `ExtractStage2.v`;
`implementation/ocaml/test_stage1_wrapper.ml` (`make test`, harness only,
`Z -> int`) exercises: structural `lower_parse` failure -> `S1Rejected`;
**B4 before B5** (bad literal + wrong dimension -> `InputStructureError`);
**B5 before C1** (both literals unrepresentable and equal ->
`MalformedIntegerLiteral`); and a successful parse -> `S1Pending` with all five
`pending_submission` fields bound to the raw submission / parsed candidate.

`make check` exits 0: `coqchk` covers `PCFW.Stage1Wrapper`; across `make check`,
**32** `Print Assumptions` commands print "Closed under the global context" -- 30
from `make assumptions` (`PrintOrchestrationAssumptions.v` + `PrintStage2Assumptions.v`)
plus the 2 kernel ones (`PrintKernelAssumptions.v`, run by the `rocq` target);
four `make test` harnesses print `PASS`.

## Still F.3-external (this unit does not close them)

- `submission_digest sub` being the true `digest_bytes_v1` of the wire bytes,
  and `semantic_digest_of` the true `digest_v1` of the parsed candidate.
- `lower_parse`'s correctness for tiers B1a/B6/B1b/B1c/B2/B3, and
  `parse_literal`'s conformance to the declared `integer_type` ranges.
- Transcript well-formedness (`transcript_stage2_wf`), a concrete artifact-bound
  `AuditContext`, O3-resolved `resolved_context`, capture/replay correspondence,
  canonical encoding, the arbitrary-precision extraction, the cross-language
  battery.
