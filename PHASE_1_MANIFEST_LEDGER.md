# Phase 1 -- concrete `op_ledger_mismatch` (AUDIT_POLICY 2.4 step 6 / VERDICT_SEMANTICS 5 step 7)

Date: 2026-09-08
Baseline: `PHASE_1_MANIFEST_AUTHENTICATION.md` (r5). One new module,
`implementation/rocq/ManifestLedger.v`, `Qed` and axiom-free; small additions to
`ValidationBinding.v` and `ManifestPipeline.v`.

The validation step being made concrete:

> step 7 -- `ti.M.submission_digests = mapi (…) ti.subs`
> (element-wise, ordered, multiplicity kept) -> else `LedgerMismatch{index}`.

## 1. The checker

`ManifestLedger.v`, `Section Ledger` over one equality decider:

```
Variable digest_eqb : digest -> digest -> bool.
Hypothesis digest_eqb_true : forall a b, digest_eqb a b = true -> a = b.
Hypothesis digest_eqb_refl : forall a, digest_eqb a a = true.
```

```
Fixpoint ld_mismatch (xs ys : list digest) : option nat :=
  match xs, ys with
  | [], []            => None
  | [], _ :: _        => Some 0
  | _ :: _, []        => Some 0
  | x :: xs', y :: ys' =>
      if digest_eqb x y then option_map S (ld_mismatch xs' ys') else Some 0
  end.
```

`ld_mismatch` returns the **least** index at which the two lists disagree: the
first position whose elements differ, or -- when one list is a strict prefix of
the other -- the length of the shorter list (the first length-divergence index).

```
Definition ledger_mismatch_impl
  (parse : manifest -> option campaign_manifest_view)
  (M : manifest) (subs : list candidate_submission) : option nat :=
  match parse M with
  | None   => Some 0
  | Some v => ld_mismatch (cm_submission_digests v) (map submission_digest subs)
  end.
```

The decoder is a parameter; the pipeline supplies
`ManifestAuthentication.parse_manifest_impl`. A decode failure is reported as a
mismatch at index 0 -- there is no ledger to compare against. This is pure list
bookkeeping: no F.3 component is used inside `ManifestLedger.v`.

## 2. Proved (`Qed`, `Print Assumptions` = "Closed under the global context")

- **`ld_mismatch_none_iff`** : `ld_mismatch xs ys = None <-> xs = ys`
  (forward uses `digest_eqb_true`; backward uses `digest_eqb_refl`).
- **`ld_mismatch_some_spec`** : `ld_mismatch xs ys = Some i` implies
  `firstn i xs = firstn i ys` (agreement on the whole common prefix -- the
  "least" part) **and** `nth_error xs i <> nth_error ys i` (a genuine divergence
  at `i`: either different elements, or one list ends there).
- **`ledger_mismatch_impl_none_iff`** : `ledger_mismatch_impl parse M subs = None`
  iff `exists v, parse M = Some v /\ cm_submission_digests v = map submission_digest subs`
  -- the **`None` equivalence** the review asked for.
- **`ledger_mismatch_impl_some_spec`** : a `Some i` result, given `parse M = Some v`,
  is a least-index divergence between `cm_submission_digests v` and
  `map submission_digest subs`.
- **`ValidationBinding.validate_campaign_valid_ledger`** : any `ops`,
  `validate_campaign ops ti = ValidCampaign ac l0` implies
  `op_ledger_mismatch ops (ti_manifest ti) (ti_submissions ti) = None`
  (a standalone fact, so the existing `validate_campaign_valid_guards`
  destructures are undisturbed).

## 3. Wiring into `pipeline_ops`

`ManifestPipeline.pipeline_ops` now sets its `op_ledger_mismatch` field to
`ManifestLedger.ledger_mismatch_impl digest_eqb parse_manifest_impl` (was the
abstract `op_ledger_mismatch` inherited from `base`). `pipeline_ops` gained a
`digest_eqb_refl` section hypothesis. `pipeline_ops_ledger` is the `reflexivity`
projection.

`validate_campaign_pipeline` is **unchanged** -- still the same three conclusions.
The ledger fact is a **separate theorem**:

```
validate_campaign_ledger_agrees :
  validate_campaign (pipeline_ops … base) ti = ValidCampaign ac l0 ->
  exists v, parse_manifest_impl (ti_manifest ti) = Some v
         /\ cm_submission_digests v = map submission_digest (ti_submissions ti)
```

(from `validate_campaign_valid_ledger` + `pipeline_ops_ledger` +
`ledger_mismatch_impl_none_iff`).

## 4. Harness -- `ocaml/test_manifest_authentication.ml`

`ld_mismatch` and `ledger_mismatch_impl` are extracted
(`ExtractManifestAuthentication.v`). New assertions (`digest_eqb` = OCaml string
`=`):

- **`ld_mismatch`** on raw digest lists: equal -> `None`; **reorder** -> `Some 0`;
  a single mid-list change -> that index (not a later one); **add** (manifest
  longer) -> first length-divergence index; **remove** (manifest shorter) -> first
  length-divergence index; **duplicate** where a distinct digest was expected ->
  the index of the first offending position; a 2-element agreeing prefix then a
  divergence -> `Some 2` (least index, not the last).
- **`ledger_mismatch_impl`** end-to-end through `parse_manifest_impl` over a
  schema-valid rendered manifest: matching submission list -> `None`; reorder ->
  `Some 0`; drop last -> `Some 1`; append extra -> `Some 2`; duplicate first ->
  `Some 1`; a manifest that fails to decode (`{}`) -> `Some 0`.

## Effect on the status ledger

`op_ledger_mismatch`: **was OPEN, now concrete standalone AND integrated**
(`pipeline_ops`), residual = the decoder passed in (`parse_manifest_impl`, itself
concrete) and, downstream, retrieval integrity (that the manifest and the
submission list are this audit's -- `ManifestPipeline.validated_manifest_is_audit`
and the analogous premise for the submission list).

`op_manifest_audit_matches` is likewise concrete (`ManifestAudit`,
VERDICT_SEMANTICS step 5 -- `PHASE_1_MANIFEST_AUDIT.md`).

`op_completeness_wellformed` is concrete and reviewer-concurred + promoted (`CompletenessWellformed`, r3 -- `PHASE_1_COMPLETENESS_WELLFORMED.md`); `op_transcript_digest` has a contract-bound primitive treatment, reviewer-concurred + promoted (`TranscriptDigest`, r3 -- `PHASE_1_TRANSCRIPT_DIGEST.md`; the hook itself stays primitive, its normative digest realisation stays F.3, so it is NOT concrete). No validation-tier `primitive_ops` member is left unaddressed.
(`op_record_identity_mismatch` -- `CampaignRecord` -- and `op_record_crosscheck`
-- `RecordCrosscheck`, `PHASE_1_RECORD_CROSSCHECK.md` -- are now concrete.)

`make check` exits 0: `coqchk` covers **20** modules (this unit added
`PCFW.ManifestLedger`; the later units added `PCFW.ManifestAudit`,
`PCFW.CampaignRecord`, `PCFW.RecordCrosscheck`); across `make check`, **152**
`Print Assumptions` "Closed under the global context"; **eight** `make test`
harnesses PASS.

Phase 1 remains **open**; Phase 2 is not authorised. **Reviewer-concurred by source inspection and promoted** as part of the cumulative r5–r13 validation block (reviewer disposition on r13; the reviewed r13 bytes, ZIP sha256 `7691bc1d05d1fb85648da9126372476589acd9971b2decc997c37dd424335419`). Not a Phase 1 closure.
