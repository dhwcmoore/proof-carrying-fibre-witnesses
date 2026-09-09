# Phase 0 — Cross-Document Consistency Audit (Run 14)

**Type:** Read-only. No governing document was edited during this audit run; the
edits it verifies were made before the run began, as Revision 14.
**Supersedes:** Runs 1–13 (all **void**). Only Run 14 is current.
**Trigger:** closure-review round 14 — four orchestration-plumbing defects
(§6.4/§6.5 stage-1 control-flow mismatch; `assessment_outcome` malformed;
`preflight_O1_O2` / `eval_O3` not constructible from their inputs; entry-point
provenance not retained). The mathematical core (`T1`/`A1`/`E1`) was not reopened.
**Governing set audited:** `PHASE_0_DECISIONS.md`, `PROJECT_CHARTER.md`,
`CLAIM_AND_DEFINITIONS.md`, `TRUST_BOUNDARY.md`, `VERDICT_SEMANTICS.md`,
`AUDIT_POLICY_AND_EVIDENCE.md`, `THREAT_MODEL.md`, `NON_CLAIMS.md`,
`PHASE_0_SPECIFICATION_AMENDMENTS.md`, `PRIOR_WORK.md`, `NOTICE`,
`THIRD_PARTY_NOTICES.md`, `LICENSE`.
**Non-governing (records; scope-excluded):**
`PHASE_0_CLAIM_SCOPE_TRUST_BOUNDARY.md`, `PHASE_0_PROPOSED_ANSWERS.md`,
`PHASE_0_REUSE_AUDIT.md`, `PHASE_0_REUSE_VERIFICATION.md`.

**Overall result:** **PASS.** A stage-1 fuel `` `Over `` is a **terminal return**
in both `capture` (§6.4) and `replay` (§6.5). `assessment_outcome` carries a
`certificate` in `Inadmissible` / `Exact` / `Obstructed` and a `campaign_report`
in `Underdetermined`. An explicit immutable `loaded_context` (one F.3
`load_context`) is threaded, as data, through `capture` / `replay` /
`assess_validated`; `preflight_O1_O2 lc` / `eval_O3 lc` / `resolved_context` are
constructible from it. `transcript_source` keeps entry-point provenance;
`transcript_evidence` distinguishes `LiveCapture` (`(CAP1)`) from
`OfflineTranscript` (`(REP1)` only). No literal `0x1F` byte (byte-scan = 0). The
governing set is internally consistent.

---

## 0. Resolution verification (round 14)

| # | Defect | Resolution — verified in | Verdict |
|---|---|---|---|
| 1 | §6.4 stage-1 `` `Over `` only `break`s, then falls through to preflight/probe/candidates — inconsistent with §6.5 / §7.2 | `VERDICT_SEMANTICS.md` §6.4: `` `Over `` → **`return { transcript=[] ; issued=[] ; clo=Some CampaignFuelExhausted ; ctx_bundle=CtxNotNeeded }`** — a terminal return; `pending` is over the fully-checked list (no partial prefix). §6.5 slot table row "stage-1 `charge` `` `Over `` at `j`": `context = NoContextNeeded`, all pending `` `NotRun ``. `CLAIM_AND_DEFINITIONS.md` §3.2.3, `AUDIT_POLICY_AND_EVIDENCE.md` §6 / §7.2.3, `TRUST_BOUNDARY.md` §F.3. `(CAP1)` restored (identical control flow). | **Resolved** |
| 2 | `assessment_outcome` — only `Obstructed` carried a `certificate` | `VERDICT_SEMANTICS.md` §6.7: `assessment_outcome := Inadmissible of certificate | Exact of certificate | Obstructed of certificate | Underdetermined of campaign_report`. `AUDIT_POLICY_AND_EVIDENCE.md` §2.2.5/§2.2.6, `CLAIM_AND_DEFINITIONS.md` §3.2.2, `PHASE_0_SPECIFICATION_AMENDMENTS.md` A2. | **Resolved** |
| 3 | `preflight_O1_O2` / `eval_O3` / `resolved_context` not constructible from their declared inputs | `VERDICT_SEMANTICS.md` §6.3 + `CLAIM_AND_DEFINITIONS.md` §3.2.3: `loaded_context := {descriptor ; model_bytes ; preproc_spec_bytes ; inference_spec_bytes ; ctx}` produced by `load_context : environment → context_descriptor → ` `Unavailable | `Loaded``; `preflight_O1_O2 : loaded_context → …` (O1/O2 = digest comparisons of `lc.*_bytes`); `eval_O3 : loaded_context → exec_event → Policy → …`, on `` `Ok `` yields `resolved_context := {policy = P ; ctx = lc.ctx ; descriptor = lc.descriptor}`. `context_bundle := CtxNotNeeded | CtxUnavailable of ctx_reason | CtxLoaded of loaded_context` is captured once and threaded through `capture` / `replay` / `assess_validated` (`replay` takes it as an argument). `AUDIT_POLICY_AND_EVIDENCE.md` §2.1/§2.4 step 7/§6/§9, `TRUST_BOUNDARY.md` §F.3/§F.3.1. | **Resolved** |
| 4 | Both paths reduce to `` `Wellformed tr ``; `decide` always records `CapturedTranscript`; entry-point provenance lost | `VERDICT_SEMANTICS.md` §3.1 (`parse_result` `` `Wellformed `` carries `wire_digest`), §6.7 (`transcript_source := ` `LiveTranscript {transcript ; ctx_bundle}`` | ` `OfflineParse {result ; ctx_bundle}``), §9: `transcript_evidence := NoTranscript | MalformedTranscript {reason ; wire_digest} | LiveCapture {transcript_digest} | OfflineTranscript {transcript_digest ; wire_digest}`. §6.6/§6.10: `(CAP1)` holds **only** for `LiveCapture`; `(REP1)` for every certificate. `CLAIM_AND_DEFINITIONS.md` §3.2.4/§6.3, `AUDIT_POLICY_AND_EVIDENCE.md` §2.2.5/§8/§9, `NON_CLAIMS.md` #14, `PROJECT_CHARTER.md` §4.3, `THREAT_MODEL.md` T29. | **Resolved** |

---

## 1. Terminology and constructor agreement — PASS

- `load_context` / `loaded_context` / `context_bundle` (`CtxNotNeeded` /
  `CtxUnavailable` / `CtxLoaded`) — one definition (`VERDICT_SEMANTICS.md` §6.3,
  `CLAIM_AND_DEFINITIONS.md` §3.2.3), used by `AUDIT_POLICY_AND_EVIDENCE.md`
  §2.1/§2.2.5/§2.4/§6/§9, `TRUST_BOUNDARY.md` §F.3/§F.3.1, `PHASE_0_DECISIONS.md`
  D-RESULT/D-TRUST. `preflight_O1_O2 : loaded_context → …`; `eval_O3 :
  loaded_context → exec_event → Policy → …` — everywhere.
- `assessment_outcome` = `Inadmissible | Exact | Obstructed of certificate |
  Underdetermined of campaign_report`; `verdict_of` total.
- `transcript_source` (`` `LiveTranscript `` / `` `OfflineParse ``) /
  `parse_result` (`` `Malformed {reason ; wire_digest}`` / `` `Wellformed
  {transcript ; wire_digest}``) / `transcript_evidence` (4 constructors) — one set
  (`VERDICT_SEMANTICS.md` §3.1/§6.7/§9, `AUDIT_POLICY_AND_EVIDENCE.md` §2.2.5).
- `validate_campaign` / `validation_result` (`` `Invalid `` / `` `FuelObstructed ``
  [dead] / `` `Valid ``) / `assess_validated` (re-uses the given result) /
  `replay ac cb vcfg pd P L0 tr` — consistent across `VERDICT_SEMANTICS.md` §5–§7,
  `CLAIM_AND_DEFINITIONS.md` §3.2.2/§6.3, `PROJECT_CHARTER.md` §4.3,
  `TRUST_BOUNDARY.md` §6, `NON_CLAIMS.md` #14.
- `call_request` / `runner : environment → call_request → exec_outcome` / `issue`;
  `charge` **before** each unit of work; a stage-1 `` `Over `` **terminal**.
- Every digest is `digest_v1(tag, ·)` / `digest_bytes_v1(tag, ·)`; tags incl.
  `pcfw.exec_transcript.v1`, `pcfw.exec_transcript_wire.v1`; `to_cv` (§2.2.5)
  covers the new / changed types.
- `Vec Z (n_· P)` / `Mat Z r c`; `AuditContext (P : Policy)` dependent.

## 2. Theorem-statement agreement — PASS

`(T1)`, `(A1)`, `(E1)` identical across `CLAIM_AND_DEFINITIONS.md` §6,
`PROJECT_CHARTER.md` §4, `VERDICT_SEMANTICS.md` §7, `NON_CLAIMS.md`. `(A1)`'s
`ObservationBinding` is **conditional** on O6 plus **two** F.3 assumptions —
`faithful_transcript tr ctx` (O4 = repeatability only) and `loaded_context`
well-formedness (`cb.lc.ctx` realises the committed spec bytes). `(T2)`:

    verdict_of (assess_validated ti V src) = INADMISSIBLE
      ⟺  (∃ ac L0, V = `Valid {campaign = ac ; fuel = L0})
          ∧ (∃ {_, `Done s} ∈ (replay ac cb ti.vcfg ti.AR.policy_document ti.AR.policy L0 tr).stage2,
                ∃ wd, s.verdict = `ValidWitness wd)

with `V := validate_campaign ti`, `src` carrying `(cb, tr)` — reproduced
**verbatim** in `CLAIM_AND_DEFINITIONS.md` §6.3, `PROJECT_CHARTER.md` §4.3,
`TRUST_BOUNDARY.md` §6, `NON_CLAIMS.md` #14, `VERDICT_SEMANTICS.md` §7. All with
`(T2-sound)`/`(T2-complete)`, "`assess_validated` re-uses the given `V`", and the
`(REP1)` (every cert) / `(CAP1)` (`LiveCapture` only) scoping.

## 3. Policy / hashing / schema agreement — PASS

- `policy_digest` non-circular; identical across §2.1, §2.4 step 3,
  `VERDICT_SEMANTICS.md` B3, `TRUST_BOUNDARY.md` §3.3, `PHASE_0_DECISIONS.md`
  D-POLICY.
- **Independently recomputed** hash-layer vectors: `pcfw.policy_payload.v1` →
  `14e86aab…` ✓; `pcfw.canonical_value.v1` → `b64f81d5…` ✓;
  `pcfw.campaign_manifest.v1` → `0714f76c…` ✓; `pcfw.candidate.v1` `70faafce…`,
  `pcfw.candidate_submission.v1` `9ec2679a…`, `pcfw.submission_check_result.v1`
  `90f8c820…`, `pcfw.generator.v1` `829ccc0f…` unchanged.
- Ed25519 = **PureEdDSA using Ed25519 (edwards25519), RFC 8032**; `parse_commitment`
  enforces 64-hex digest / 128-hex signature; unique-signer `trust_anchor`;
  `max_fuel ≥ validation_fuel_ok` is a config-load requirement.
- §2.4 step 7 (live): `validate_campaign` once → gated capture (stage-1 `` `Over ``
  terminal; `load_context` after stage 1; `preflight_O1_O2 lc`) → `assess_validated
  (` `LiveTranscript …``)`. §9 (offline): `validate_campaign` once → reconstruct
  `context_bundle` → `parse_transcript` → `assess_validated (` `OfflineParse …``)`.

## 4. Trust-boundary agreement — PASS

F.3 lists: policy loader; **`load_context`** (one fetch → immutable
`loaded_context`; assumption `ctx` realises the committed spec bytes); `N_P`;
inference re-execution; `canonicalise_v1`/`digest_*`; parser/schema/`to_cv`;
candidate ingestion + ledger; manifest-signing key + unique-signer `trust_anchor`;
**`validate_campaign` once, before any model call**; **the `runner` + the gated
capture** (charge precedes the work; stage-1 `` `Over `` terminal); **the
deterministic fuel model**; **`parse_transcript`** (offline, bounded); the weaker
wall-clock/memory watchdog. `faithful_transcript` the never-discharged residual
assumption. F.3.1: `load_context` `` `Unavailable `` / `preflight_O1_O2 lc`
`` `Fail `` ⇒ no probe; `eval_O3 lc` `` `Fail `` ⇒ no candidate call.

## 5. Campaign evaluation coherence — PASS

- `validate_campaign` (§5) — 9 ordered checks, first failure wins, no runner call;
  every branch carries a `fuel_ledger`; `` `FuelObstructed `` dead.
- `capture` (§6.4) — candidate-count first; stage-1 `charge`-then-check with a
  **terminal** `` `Over ``; `load_context`; preflight; probe; candidate batches —
  every `charge` before its work. Returns `{transcript ; issued ; clo ; ctx_bundle}`.
- `replay` (§6.5) — pure total in `(ac, cb, vcfg, pd, P, L0, tr)`; identical
  `charge`/gate sequence; slot rule table (10 rows) covers every §6.4 outcome.
- `decide` (§6.7) — total; binds `rc := r.context` for `ContextResolved r`;
  `EXACT` dead code (§6.9); passes `` `ReplayDone rr `` + `transcript_evidence` +
  `commitment_evidence` to `build_certificate`.
- `assess_validated` (§6.7) — matches `vr` first, then the `transcript_source`;
  `` `LiveTranscript `` → `LiveCapture`, `` `OfflineParse `Wellformed `` →
  `OfflineTranscript`, `` `OfflineParse `Malformed `` → `MalformedTranscript`.
- Frozen precedence: `` `Invalid `` > `` `FuelObstructed `` > `` `Malformed ``
  transcript > within-budget `` `ValidWitness `` > `clo` > all-obstructed > EXACT
  dead code > UNDERDETERMINED.

## 6. Bundle / witness / campaign separation — PASS

`stage1_result.verdict ∈ {` `Rejected `` / `` `NotAWitness `` / `` `Pending ``};
`stage2_result.verdict ∈ {` `WitnessCheckObstructed `` / `` `NotAWitness `` /
`` `ValidWitness ``}. `UNDERDETERMINED` campaign-level only. `(T1)` witness level.

## 7. Licence / reuse — PASS

Approved limited-statement wording verbatim in `PROJECT_CHARTER.md` §8/§8.1,
`NON_CLAIMS.md` #23/#25, `PHASE_0_DECISIONS.md` D-LIC; "do not propagate" absent.
Documentation roles distinct. `LICENSE` canonical Apache-2.0. Reuse audit +
verification records ratified (Run 9 A7 stands); Revision 14 touched only the
orchestration plumbing, so no reuse disposition is reopened.

## 8. Absence of stale claims (governing set) — PASS

Absent: float / saturation / decoder-equivalence / `list Z` / undefined rounding /
kernel-over-model / circular `policy_digest` / `EXACT`-via-"exhaustive coverage".
Newly checked and absent: a §6.4 stage-1 `` `Over `` that only `break`s and falls
through; `assessment_outcome` with `certificate` bound only to `Obstructed`;
`preflight_O1_O2` / `eval_O3` / `resolved_context` without the artifact bytes; an
unconditional `CapturedTranscript` that loses live/offline provenance; a
`` `Wellformed `` `parse_result` without a `wire_digest`; `(CAP1)` claimed for
offline replay; `assess_pure` / `capture_plan` / `resolve_context_from_transcript`;
`build_certificate` receiving `None`; `lookup` (bare); "`faithful_transcript`
failure is exactly what O4 catches"; literal `0x1F` byte (byte-scan = 0).

## 9. Specification §15–§21 coverage — PASS

Work units 0A–0F → the seven governing deliverables (Revision 14); 0G
(`PHASE_0_CLOSURE_REPORT.md`) **not issued**. §16 manual examples →
`VERDICT_SEMANTICS.md` §11, with a live vs offline `INADMISSIBLE` pair
(`LiveCapture` + `(CAP1)`/`(REP1)` vs `OfflineTranscript` + `(REP1)` only), an
"artifact bytes unavailable (`load_context` fails)" row, a stage-1-`` `Over ``-
terminal row. §17 reflected. §18 open questions consolidated; `INADMISSIBLE`
pinned by `(T2)`. §19 exit criteria — all satisfied except the closure report.
§20 answerable. §21 Phase 1 objective stated.

## 10. Deferred implementation-phase test obligations

For the Rocq / OCaml build (`AUDIT_POLICY_AND_EVIDENCE.md` §10):

1. stage-1 `charge` `` `Over `` at `j` ⇒ `capture` returns immediately (no
   `load_context`, no probe, no candidate calls); `replay` marks `≥ j`
   `` `NotRun `` and `context = NoContextNeeded`.
2. `assess_validated` on `` `Valid ``/`` `Wellformed `` with a within-budget
   witness ⇒ `Inadmissible of certificate` (not a bare `Inadmissible`).
3. `load_context` `` `Unavailable `` ⇒ `ContextUnresolved ArtifactMismatch`, no
   probe, no candidate calls, verdict `OBSTRUCTED`.
4. `preflight_O1_O2 lc` computes O1/O2 purely from `lc.*_bytes` vs `lc.descriptor`;
   an artifact-byte mismatch ⇒ `` `Fail ArtifactMismatch ``.
5. `eval_O3 lc` builds `resolved_context = {policy=P ; ctx=lc.ctx ;
   descriptor=lc.descriptor}` from `lc` alone.
6. live path ⇒ `transcript_evidence = LiveCapture`; offline replay of the same
   package ⇒ `transcript_evidence = OfflineTranscript`, same verdict, but the
   certificate carries only `(REP1)`.
7. `(CAP1)`: `capture` output replayed with `co.ctx_bundle` ⇒ `` `NotRun `` slots
   ⟺ keys absent from `co.issued`, and `rr.clo = co.clo`.
8. `parse_transcript` on a `` `Wellformed `` input still sets `wire_digest`;
   `OfflineTranscript` binds both `transcript_digest` and `wire_digest`.
9. `assessment_outcome` serialisation (`{"k":"inadmissible","v":<certificate>}` …)
   round-trips.
10. one `validate_campaign` per pipeline (live + offline); `assess_validated`
    never calls it.

---

## 11. Findings

| id | severity | finding |
|---|---|---|
| N1 | note | `PHASE_0_PROPOSED_ANSWERS.md` retains superseded prose behind the ARCHIVED banner — a scope-excluded process record. |
| N2 | note | §2.2.7 vectors are hash-layer conformance vectors. Schema-valid end-to-end bundles and `pcfw.verifier_config.v1` / `pcfw.exec_transcript.v1` / `pcfw.exec_transcript_wire.v1` / Ed25519 test vectors are implementation-phase deliverables (§10). |
| N3 | note | The `INADMISSIBLE` warrant now rests on **two** F.3 assumptions: `faithful_transcript` (runner) and `loaded_context` well-formedness (`ctx` realises the committed spec bytes). Both are listed on the certificate; the `loaded_context` bytes are additionally bound by `context_digests` (O1/O2). |
| N4 | note | The `fuel_schedule` constants, `model_call_fuel` counting convention, and `max_transcript_bytes` value are interface-level; concrete values bound by `fuel_model_digest` / `verifier_config_digest`. |
| N5 | note | `PHASE_0_SPECIFICATION_AMENDMENTS.md` B2/A6 still say "two-stage" in prose — a reading key to the original spec, not a governing contradiction. |

No finding is a semantic contradiction in the governing set. **The audit passes.**
Subject to the independent closure reviewer's concurrence with Revision 14,
`PHASE_0_CLOSURE_REPORT.md` may be issued. It has **not** been issued.
