# Phase 1 -- `op_transcript_digest`: the final `primitive_ops` member

Date: 2026-09-14 (revision 1 HELD -- narrow documentation/wording and one
harness-coverage correction; revision 2 HELD -- three residual wording/version-label
stragglers; **revision 3 reviewer-concurred and promoted**)
Baseline: `PHASE_1_COMPLETENESS_WELLFORMED.md` (r3, reviewer-concurred and
promoted). One new module, `implementation/rocq/TranscriptDigest.v` (`Qed`,
axiom-free); a small addition to `ManifestPipeline.v` (two theorems, no
change to `pipeline_ops`'s existing conclusions). No change to
`Orchestration.v`, `RecordCrosscheck.v`, `CompletenessWellformed.v`, or any
other promoted unit.

Status: **reviewer-concurred by source inspection and promoted** (2026-09-14;
reviewed r3 ZIP sha256
`8b6e3b01533c1f8cfa864a05a36383e2e814ff7b78e7ef42515b24818e5b60ad`). Not a
Phase 1 closure.

## 0. Revision 1 HOLD and the corrections

Revision 1's formal construction (proofs, extraction, harness structure) was
accepted by source inspection without changes. The HOLD was narrowly for
imprecise status wording and one harness-coverage gap:

1. **"Concrete" overstated.** `op_transcript_digest` REMAINS a primitive
   hook -- its normative realisation (`transcript_digest_v1`) stays an
   uninstantiated F.3 abstraction. Every "concrete" description of this unit
   is corrected below and throughout the other status documents to
   "contract-bound primitive."
2. **Field count.** `primitive_ops` has fifteen fields;
   `set_transcript_digest` preserves the other **fourteen**, not thirteen
   (the `set_transcript_digest_preserves_others` lemma already stated all
   fourteen correctly -- only the prose undercounted them).
3. **Build counts.** Corrected to the actual `make check` output throughout:
   `coqchk` **20** modules, **152** `Print Assumptions`, **eight** `make
   test` harnesses.
4. **Harness coverage.** §9's "event reordering / a modified event" claim
   only exercised reordering; a modified-event case is added below (no claim
   that its digest differs).

No proof, theorem statement, or extraction target changed.

Revision 2 was HELD narrowly for three residual stragglers the r1 fix missed:
`TranscriptDigest.v`'s own module-header title comment still read "Concrete
`op_transcript_digest`"; a second, separate comment (near
`run_stage1_set_transcript_digest` / `run_stage2_set_transcript_digest`) still
said "the OTHER 13 fields"; and nine status documents still labelled this
unit's *current* status "r1"/"revision 1" although this document already said
revision 2. All three fixed in **revision 3**, with no further proof,
theorem, extraction-target, or harness change; genuinely historical
revision-1 references (e.g. `op_completeness_wellformed`'s own history) were
left untouched. **Revision 3 is reviewer-concurred and promoted.**

## 1. Purpose and frozen scope

This closes the final open `primitive_ops` member by formally specifying and
integrating the transcript-digest hook `transcript_evidence` carries. This is
an **interface-and-evidence-binding unit, NOT a cryptographic implementation
unit**. Frozen, not reopened here:

- `op_transcript_digest : exec_transcript -> digest` REMAINS a primitive hook.
- The normative target remains `digest_v1("pcfw.exec_transcript.v1",
  to_cv(exec_transcript))`.
- Phase 1 does not require a concrete canonicaliser or SHA-256 realisation for
  this hook.
- The required formal guarantee is **deterministic equality on identical
  typed canonical inputs** -- ordinary Gallina functional congruence. **No
  injectivity or collision-resistance claim is made or needed**: different
  transcripts are NOT required to produce provably different digests.
- This unit does **not** implement or prove `parse_transcript`, does **not**
  discharge `transcript_stage2_wf`, and does **not** establish transcript
  faithfulness -- all three stay open, separate obligations.
- The offline raw-wire digest `digest_bytes_v1("pcfw.exec_transcript_wire.v1",
  wire_bytes)` is a SEPARATE quantity (computed upstream over the wire bytes,
  never over a typed `exec_transcript`) and is never conflated with the
  typed-transcript digest.

## 2. The two digests, kept apart

| digest | over | where it is computed | carried in |
|---|---|---|---|
| typed-transcript digest | a typed `exec_transcript` | `op_transcript_digest ops tr`, called only inside `assess_validated` | `LiveCapture d` / `OfflineTranscript d _` |
| raw-wire digest | the raw retained bytes | upstream, by `parse_transcript` (open, separate obligation) | `OfflineTranscript _ w` / `MalformedTranscript _ w` |

They never appear as the same argument position, and no theorem below equates
them.

## 3. The operation, and everything it does not touch

```
set_transcript_digest (ops : primitive_ops) (g : exec_transcript -> digest)
  : primitive_ops
  -- replaces ONLY op_transcript_digest; every other field is `ops`'s own
     (set_transcript_digest_field, set_transcript_digest_preserves_others).
```

`op_transcript_digest` is `primitive_ops`'s LAST field, used in exactly two
places in `Orchestration.v` -- both inside `assess_validated`, building
`LiveCapture (op_transcript_digest ops tr)` / `OfflineTranscript
(op_transcript_digest ops tr) wire_digest`. It is read NOWHERE inside
`validate_campaign`, `run_stage1`, `run_stage2`, `finish_replay`, or `decide`.
Consequently:

- **`validate_campaign_indep_of_transcript_digest`** -- `validate_campaign`
  is unaffected by `set_transcript_digest` (`reflexivity`: no unbounded
  recursion touches this field).
- **`replay_indep_of_transcript_digest`** -- the **entire** `replay_result`
  is unaffected (strictly stronger than the analogous
  `RecordCrosscheck.set_crosscheck` independence result, because unlike
  `op_record_crosscheck`, this field affects nothing inside `replay` at
  all -- not even `record_findings`). Proved by the same induction technique
  `RecordCrosscheck.run_stage1_set_crosscheck` / `run_stage2_set_crosscheck`
  established (`run_stage1_set_transcript_digest`,
  `run_stage2_set_transcript_digest`, `finish_replay_set_transcript_digest`).
- **`verdict_indep_of_transcript_digest`** -- the campaign verdict (the outer
  `assessment_outcome` constructor) is unaffected: `decide` never inspects
  `_ops`, `_tr`, `tev`, or `cev` -- only `rr` and `authenticated_completeness
  ac` (`decide_verdict_indep_of_tev`). **The digest hook records which
  transcript was assessed; it cannot manufacture or suppress a witness.**

## 4. Determinism -- exactly what it is, and is not

```
op_transcript_digest_deterministic : forall ops tr1 tr2,
  tr1 = tr2 -> op_transcript_digest ops tr1 = op_transcript_digest ops tr2.
```

This is ordinary Gallina functional congruence (any function maps equal
inputs to equal outputs) -- **not** a cryptographic claim, **not** collision
resistance, and it says **nothing** about different transcripts.

## 5. The normative denotation (F.3 residual)

```
Section Normative.
Variable transcript_digest_v1 : exec_transcript -> digest.   (* F.3 *)

transcript_digest_agrees (ops : primitive_ops) (tr : exec_transcript) : Prop :=
  op_transcript_digest ops tr = transcript_digest_v1 tr.
```

`transcript_digest_v1` stands for `digest_v1("pcfw.exec_transcript.v1",
to_cv(tr))`; its concrete canonicaliser and SHA-256 realisation stay F.3,
exactly like every other `digest_v1` use in this codebase.
`transcript_digest_agrees` is a **PER-TRANSCRIPT** predicate, deliberately
**not** a blanket `forall tr, ...` Section `Hypothesis` -- that shape is the
exact defect this project has already HELD twice
(`ManifestMatching.ti_policy_digest_truthful`;
`CompletenessWellformed`'s revision-2 `record_completeness_load_validated`).
Theorems needing correctness take `transcript_digest_agrees ops tr` as an
explicit premise about the one transcript being assessed.
`transcript_digest_implementation_valid` names the universal contract a host
implementation should aim for, but it is **never** installed as an ambient
hypothesis anywhere in this file.

## 6. Evidence binding

```
outcome_transcript_evidence (out : assessment_outcome) : transcript_evidence
typed_digest_of (tev : transcript_evidence) : option digest
  -- Some for LiveCapture / OfflineTranscript, None for Malformed / NoTranscript
```

- **`live_evidence_uses_typed_transcript_digest`** -- live processing records
  `LiveCapture (op_transcript_digest ops tr)`.
- **`offline_evidence_uses_both_digests`** -- well-formed offline processing
  records `OfflineTranscript (op_transcript_digest ops tr) wire_digest` --
  the SAME typed digest, plus its own, independent raw-wire digest.
- **`live_offline_typed_digest_agree`** -- for the SAME typed transcript, live
  and well-formed-offline evidence carry the SAME typed digest, regardless of
  the offline wire digest. This is **not** a claim that the two evidence
  VALUES are identical -- offline properly carries the extra raw-wire digest.
- **`live_evidence_digest_agrees`** / **`offline_evidence_digest_agrees`** --
  conditional on `transcript_digest_agrees ops tr`, the evidence carries the
  *normative* `transcript_digest_v1 tr`, not just whatever `op_transcript_digest`
  happens to compute.

## 7. Malformed-transcript separation

`assess_validated`'s `OfflineParse (MalformedParse reason wire_digest) _`
branch returns before `match src` is even reached by anything transcript- or
`ops`-dependent -- it is fully determined by `reason`/`wire_digest` alone:

- **`malformed_evidence_uses_only_wire_digest`** -- evidence is exactly
  `MalformedTranscript reason wire_digest`.
- **`malformed_no_typed_digest`** -- `typed_digest_of` of that evidence is
  `None`.
- **`malformed_assess_indep_of_transcript_digest`** -- the WHOLE
  `assess_validated` result (not just its evidence) is unaffected by
  `set_transcript_digest` (`reflexivity` -- this branch never calls `replay`,
  `decide`, or `op_transcript_digest` at all).

There is no accepted typed transcript to hash on this branch, so this is the
required separation, not an assumption.

## 8. Pipeline integration

`ManifestPipeline.pipeline_ops` passes `op_transcript_digest` straight through
from `base` (unchanged since before this unit -- `concrete_auth_ops` already
did the same):

- **`pipeline_ops_transcript_digest`** -- `op_transcript_digest (pipeline_ops
  base) = op_transcript_digest base` (`reflexivity`).
- **`pipeline_transcript_digest_agrees`** -- if the baseline `op_transcript_digest`
  agrees with the normative denotation for a transcript, so does the wired
  `pipeline_ops`'s (immediate corollary).

No change to validation ordering, the replay algorithm, certificate
precedence, or any other `primitive_ops` member.

## 9. Harness

`implementation/rocq/ExtractTranscriptDigest.v` extracts `assess_validated`,
`set_transcript_digest`, `outcome_transcript_evidence`, `typed_digest_of`, and
`op_transcript_digest` into a **dedicated** `extracted_transcript_digest.ml`
-- kept separate from `extracted_stage2.ml` so this unit's dependency closure
(which reaches `Orchestration.policy`, `= string`) cannot collide with the
unrelated `FibreWitnessKernel.Policy` record already extracted there.

`ocaml/test_transcript_digest.ml` (a submission-free `authenticated_campaign`
-- `run_stage1` completes immediately with `pending = []`, so `replay` reaches
`finish_replay` directly; every stage1/preflight/O3/stage2 op is stubbed
never-called) exercises, with a **deterministic mock digest** (explicitly
documented as NOT SHA-256, NOT the production digest):

- empty transcript, evaluated twice -- same digest;
- a one-event transcript, evaluated twice -- same digest;
- identical multi-event transcripts -- same digest;
- live and well-formed-offline evidence over the same typed transcript --
  same typed digest, and each carries the expected constructor/fields;
- a different offline `wire_digest` -- same typed digest, but the evidence
  VALUES differ (the wire digest is carried too);
- malformed offline input -- evidence is exactly `MalformedTranscript`, no
  typed digest, and unaffected by `set_transcript_digest`;
- replacing the digest operation -- evidence changes, the verdict (the outer
  `assessment_outcome` constructor) does not;
- event reordering, and a modified event (a different `event_input`) --
  each exercised as a structurally different input, with **no** assertion
  (and no reliance on one) that the resulting digest must differ.

## 10. Assumptions and non-claims

`implementation/rocq/PrintTranscriptDigestAssumptions.v`: 19 `Print Assumptions`
targets, every one "Closed under the global context" -- no `Axiom`,
`Parameter`, `Admitted`, or `admit` anywhere in `TranscriptDigest.v` or the
`ManifestPipeline.v` addition. The only abstract entity is the Section
`Variable transcript_digest_v1`, an explicit theorem parameter wherever used,
never an ambient global assumption. **This unit does NOT claim**: cryptographic
correctness of any realisation of `digest_v1`; collision resistance;
`parse_transcript` correctness; `transcript_stage2_wf`; transcript
faithfulness; or Phase 1 closure.

## Effect on the status ledger

`op_transcript_digest`: **contract-bound primitive, standalone AND
integrated** (`pipeline_ops`) -- the hook itself REMAINS primitive and is
NOT concrete; its normative digest realisation stays F.3 -- with
non-interference (`validate_campaign` / `replay` / verdict),
evidence-binding, and malformed-separation results, all `Qed`, axiom-free.
**Reviewer-concurred by source inspection and promoted** (revision 3; ZIP
sha256 `8b6e3b01533c1f8cfa864a05a36383e2e814ff7b78e7ef42515b24818e5b60ad`).

`make check` exits 0: `coqchk` covers **20** modules (adds
`PCFW.TranscriptDigest`); across `make check`, **152** `Print Assumptions`
"Closed under the global context" (133 + 19); **eight** `make test` harnesses
PASS (adds `test_transcript_digest`).

Every `primitive_ops` member now has either a concrete implementation or (for
this one) an explicit, contract-bound primitive treatment. Phase 1 remains
**open** regardless: `parse_transcript` / capture well-formedness,
`transcript_stage2_wf`, digest-function correctness, artefact binding to the
committed model/inference spec, arbitrary-precision extraction, and the final
Phase 1 closure review are all separate, still-open obligations. Phase 2 is
not authorised. The r5-r13, r17, and `op_completeness_wellformed` (r3)
promotions are unaffected.
