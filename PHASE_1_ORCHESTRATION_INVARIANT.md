# Phase 1 -- evidence preservation through orchestration

Date: 2026-09-06
Baseline: `PHASE_1_STAGE1_CONNECTION.md` (reviewer-concurred; two documentation
corrections applied -- "five Stage1 results" and the stale
`PrintOrchestrationAssumptions.v` comment). One new module,
`implementation/rocq/Stage1Invariant.v`, `Qed` and axiom-free.

**Reviewer concurrence:** after two review rounds -- the first replacing the
weak `replay_pending_invariant` (which never mentioned `replay`) with
`replay_op_stage2_local` (an equality of actual `replay` outputs), and rewording
`op_stage1_sound` as a pending-output soundness contract -- the designated
reviewer verified archive integrity and source and concurred with promotion of
this bounded unit. Compilation evidence (`make check` exit 0, 27 closed-assumption
outputs, tests) is from the implementation machine; the reviewer's concurrence is
by source inspection (`coqc` / `ocamlc` unavailable there).
`replay_op_stage2_local` guarantees output *independence* from `op_stage2_check`
behaviour outside the invariant; it does not forbid an extra call whose result is
discarded.

The stage-2 adapter's theorems carry per-candidate hypotheses
(`Stage2Adapter.adapter_candidate_wf`, and `Stage2.Stage1Evidence` via the
C-recheck). `PHASE_1_STAGE1_CONNECTION.md` established them for one
`stage1_semantic_check` call; this unit propagates them through `run_stage1` and
`replay`, and shows the adapter's C-recheck is then redundant.

## The invariant

`pending_invariant C ps` :=

```
exists x y,
  parse_vec n_in (candidate_x (pending_candidate ps)) = Some x /\
  parse_vec n_in (candidate_y (pending_candidate ps)) = Some y /\
  Stage2.Stage1Evidence C x y
```

A `Prop` over the *existing* `pending_submission` representation -- no
proof-carrying record, erased at extraction. `pending_invariant_candidate_wf`:
it implies `@Stage2Adapter.adapter_candidate_wf n_in ps`.

## The pending-output soundness contract (F.3-pending)

`op_stage1_sound ops` :=

```
forall cfg pd p i sub ps,
  s1_verdict (op_stage1_check ops cfg pd p i sub) = S1Pending ps ->
  pending_invariant C ps
```

A **soundness contract on `op_stage1_check`'s pending outputs**: every
`S1Pending` verdict satisfies `pending_invariant`. It does **not** compare
`op_stage1_check` with `stage1_semantic_check`, establish parser correspondence,
or preserve submission identity. Its discharge -- a parser wrapper that accounts
for parse failure and binds the successful parse to the supplied submission and
digests -- is an F.3 obligation, still open (see "Still open"). An arbitrary
`op_stage1_check` satisfies nothing; this is a hypothesis, like
`transcript_stage2_wf` and transcript faithfulness.

## Proved (`Print Assumptions`: "Closed under the global context" for all)

1. **`stage1_pending_invariant`**: `stage1_semantic_check C sd cd idx c =
   S1Pending ps` implies `pending_invariant C ps` (from
   `Stage1.stage1_pending_evidence`).
2. **`run_stage1_preserves_invariant`** / **`run_stage1_all_pending_invariant`**:
   given `op_stage1_sound ops`, every pending submission in
   `stage1_run_pending (run_stage1 ops cfg pd p subs 0 l0 [] [])` satisfies
   `pending_invariant C`. The general lemma carries the invariant on the
   `pending_rev` accumulator; the entry-point corollary discharges it (empty
   accumulator). `run_stage1`'s `with_pending_index i` reassignment is handled
   by `with_pending_index_invariant` (`pending_invariant` depends only on
   `pending_candidate ps`, which `with_pending_index` preserves).
3. **`run_stage1_stage2_list_invariant`** (list-level) + **`replay_op_stage2_local`**
   (about `replay`). The list-level fact: every element of the `Stage1Complete` /
   `Stage1Stopped` `pending` field that `replay` computes satisfies the
   invariant. The statement about `replay` itself:

   ```
   ops_eq_except_stage2 ops ops'  ->  op_stage1_sound ops  ->
   (forall rc' cfg' tr' ps, pending_invariant C ps ->
      op_stage2_check ops rc' cfg' tr' ps = op_stage2_check ops' rc' cfg' tr' ps)  ->
   replay ops ac cb cfg pd p l0 tr = replay ops' ac cb cfg pd p l0 tr
   ```

   `ops_eq_except_stage2` fixes all fifteen `primitive_ops` fields except
   `op_stage2_check`. So `replay`'s output depends on `op_stage2_check` *only*
   through its behaviour on invariant-satisfying pending submissions -- a
   machine-checked statement about `replay` (proof: `run_stage1` agreement,
   then the invariant on its pending list, then `run_stage2` agreement under
   that invariant; every other branch of `replay` calls no `op_stage2_check`).
4. **`adapter_c_recheck_redundant`**: under `pending_invariant C ps`,
   `adapter_stage2_check C rng rc cfg tr ps` equals the mapped result of
   `Stage2.stage2_check` directly -- none of the four C-recheck early returns
   (`domainb x`, `domainb y`, `veqb x y`, `Bool.eqb (target x) (target y)`)
   fires. The adapter's local C-recheck is provably redundant for reachable
   pending submissions.

## Scope

Discharges the candidate / evidence hypotheses only. Does **not** touch
`transcript_stage2_wf`, does **not** imply any stage-2 check succeeds, and
changes **no executable behaviour** (the redundant C-recheck is left in place;
this is a proof of redundancy, not a rewrite).

`make check` exits 0: `coqchk` now covers `PCFW.Stage1Invariant`;
`make assumptions` reports 27 "Closed under the global context" tree-wide.

## Still open

- Discharge `op_stage1_sound` by implementing `op_stage1_check` over the wire
  parser (F.3) -- the pipeline link.
- `transcript_stage2_wf` from `parse_transcript` / `capture`.
- Concrete artifact-bound `preproc` / `model` / `quantise` / `domainb` /
  `target`; O3-resolved `resolved_context`; capture/replay correspondence;
  canonical encoding; arbitrary-precision extraction; cross-language battery.
