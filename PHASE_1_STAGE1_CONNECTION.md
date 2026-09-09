# Phase 1 -- concrete stage-1 semantic checker, connecting the adapter's upstream hypotheses

Date: 2026-09-06
Baseline: `PHASE_1_STAGE2_KERNEL_CONNECTION.md` (promoted). One new module,
`Qed` and axiom-free.

`Stage2Adapter.adapter_reporting_conformance` and
`adapter_valid_supplies_checked_witness` carry hypotheses about the pending
candidate -- `adapter_candidate_wf ps` (dimensions) and, implicitly via the
re-check, `Stage1Evidence C x y` (C1/C2/C3/C5). This unit establishes both from
a concrete stage-1 checker.

## `implementation/rocq/Stage1.v`

`stage1_semantic_check C sub_digest sem_digest idx c : stage1_verdict` -- the B4
dimension check and C1/C2/C3/C5, in the frozen order
**B4 -> C1 -> C2 -> C3 -> C5** (VERDICT_SEMANTICS.md 4.1 /
AUDIT_POLICY_AND_EVIDENCE.md 6). It takes an already-parsed `parsed_candidate`
(`list Z` x `list Z`) plus the two digests the wire layer computed; wire-level
tier B (B1a/B6/B1b/B1c/B2/B3/B5) is the F.3 parser's job and is out of scope.

- B4: both `candidate_x` and `candidate_y` parse to `Vec Z n_in`, else
  `S1Rejected InputStructureError`.
- C1: `x <> y`, else `S1NotAWitness InputsEqual`.
- C2/C3: `domainb P x` / `domainb P y`, else `XNotInDomain` / `YNotInDomain`.
- C5: `target P x <> target P y`, else `TargetsAgree`.
- otherwise `S1Pending (mkPendingSubmission idx sub_digest sem_digest c [])`.

### Proved

- **`stage1_pending_identity`**: `stage1_semantic_check sd cd idx c = S1Pending
  ps` implies `ps` is *exactly* `mkPendingSubmission idx sd cd c []`:
  `pending_candidate ps = c`, `pending_index ps = idx`,
  `pending_submission_digest ps = sd`, `pending_semantic_digest ps = cd`,
  `pending_findings ps = []`. (The internal `stage1_pending_parses` gives the
  full `ps = mkPendingSubmission …` equation.) Taking digests as arguments
  claims nothing about their computation or binding to the raw submission --
  wire-layer obligations.
- **`stage1_pending_candidate_wf`**: `S1Pending ps` implies
  `Stage2Adapter.adapter_candidate_wf ps` -- discharging that adapter
  hypothesis.
- **`stage1_pending_evidence`**: `S1Pending ps` implies `pending_candidate ps =
  c` **and** the candidate of that same `ps` parses to kernel vectors `x`, `y`
  (`parse_vec n_in (candidate_x (pending_candidate ps)) = Some x`, likewise `y`)
  with `Stage2.Stage1Evidence C x y` under the same `C` -- so `x`, `y` are tied
  to the returned `ps`, not merely to `c`. This is the premise
  `Stage2.stage2_valid_checked_witness` needs and the adapter currently
  re-derives.
- **`stage1_reject_char`**: `S1NotAWitness r` implies, for the parsed `x`, `y`,
  `match r with InputsEqual => x = y | XNotInDomain => x <> y /\ ~InDomain P x |
  YNotInDomain => x <> y /\ InDomain P x /\ ~InDomain P y | TargetsAgree =>
  x <> y /\ InDomain P x /\ InDomain P y /\ target P x = target P y |
  QuantisedObservationsDiffer => False end`. Stated as a `match` on the returned
  reason (not a disjunction) -- it fixes *which* reason and its meaning, with no
  exclusivity question; the `x <> y` / `InDomain` conjuncts are the precedence.
- **`stage1_dim_reject`**: a wrong `candidate_x` or `candidate_y` length yields
  `S1Rejected InputStructureError` -- B4 dominates every C-check.

`Print Assumptions` for all five: "Closed under the global context".

## Executable exercise

`stage1_semantic_check` is added to `ExtractStage2.v`;
`implementation/ocaml/test_stage1.ml` (`make test`) exercises a valid `Pending`,
each of `InputsEqual` / `XNotInDomain` / `YNotInDomain` / `TargetsAgree`, and the
precedence: C1 before C2 (equal + out-of-domain -> `InputsEqual`), C2 before C5
(out-of-domain + targets-agree -> `XNotInDomain`), B4 before C1 (malformed +
equal -> `InputStructureError`).

`make check` exits 0: `coqchk` now covers `PCFW.Stage1`; `make assumptions`
shows all five Stage1 results "Closed under the global context"; `make test`
prints `PASS` for `test_stage1`.

## Still open (this connects one set of hypotheses; others remain)

- **Evidence preservation through orchestration** (next bounded unit). Prove
  that every pending submission `run_stage1` produces -- and that `replay`
  subsequently consumes -- satisfies `adapter_candidate_wf` and yields
  `Stage1Evidence`, as an invariant over the existing `pending_submission`
  representation (a proof-carrying record is not required; a `Prop` proof is
  erased at extraction). Then prove the adapter's C-recheck necessarily
  succeeds for those reachable pending submissions -- a precise redundancy
  result -- before any executable behaviour changes.
- **The pipeline link.** `stage1_semantic_check` is still not `op_stage1_check`
  (which takes a raw `candidate_submission`; the wire parser is F.3). This unit
  connects *semantic* stage 1 to the adapter locally; it does not connect raw
  submissions to the verified pipeline.
- **Transcript well-formedness** (`transcript_stage2_wf`) is still established
  only by hypothesis -- `parse_transcript` / `capture` remain abstract.
- Concrete `preproc` / `model` / `quantise` / `domainb` / `target` bound to the
  committed artifacts; O3-resolved `resolved_context`; capture/replay
  correspondence; canonical encoding; the arbitrary-precision extraction;
  cross-language battery.
