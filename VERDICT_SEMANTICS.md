# Verdict Semantics

**Deliverable:** Phase 0, Unit 0D
**Status:** Draft for Unit 0G ratification. **Revision 15** — adds the
`InconsistentContextBundle` campaign obstruction and the `ContextBundleInconsistent`
context state for the one bundle/stage-1 pairing a total `replay` must handle but
`capture` never produces (`CtxNotNeeded` supplied with a completed stage 1 that
yielded `Pending` candidates); `ctx_reason` is unchanged. §6.4's `CtxNotNeeded`
description is corrected (it also legitimately arises on terminal stage-1 fuel
exhaustion). Full rationale: `phase0_closure_package_r1/CONTEXT_BUNDLE_AMENDMENT.md`.
Revision 14 — `assessment_outcome`
carries a `certificate` in **every** constructor. `loaded_context` is an explicit
immutable value produced by one F.3 `load_context` and threaded, as data, through
`capture` / `replay` / `assess_validated` (so `preflight_O1_O2` / `eval_O3` /
`resolved_context` are constructible). A stage-1 fuel `` `Over `` is a **terminal
return** in both `capture` and `replay`. `transcript_source` keeps entry-point
provenance: `transcript_evidence` distinguishes `LiveCapture` (`(CAP1)` applies)
from `OfflineTranscript` (`(REP1)` only). One `validate_campaign` per pipeline;
`assess_validated` re-uses its result. Charge-before-work; `FuelObstructed` dead.
**Normative.**

---

## 1. Three levels

```text
BundleResult      REJECTED_BUNDLE | ACCEPTED_BUNDLE
WitnessResult     VALID_WITNESS | NOT_A_WITNESS | WITNESS_CHECK_OBSTRUCTED
CampaignVerdict   INADMISSIBLE | EXACT | UNDERDETERMINED | OBSTRUCTED
```

`WitnessResult` is defined for **any submission tier B accepts**. `CampaignVerdict`
is `verdict_of (assess_validated ti (validate_campaign ti) src)` (§6.7). The campaign
record's candidate outcomes and resource budget are advisory; its identity/manifest
fields are verdict-affecting fail-closed inputs (§5); its `completeness` field is a
gated verdict input (§6.9). None of these types is an instance of a borrowed gate
abstraction (§8).

## 2. Result reasons (frozen constructor sets)

```ocaml
type b_reason =
  | BundleLimitExceeded | InvalidUtf8
  | MalformedStructure | DuplicateKeys
  | SchemaUnrecognised | SchemaVersionMismatch
  | UnknownCriticalField | OverrideField
  | PolicyHashMismatch | InputStructureError | MalformedIntegerLiteral

type c_reason =
  | InputsEqual | XNotInDomain | YNotInDomain
  | QuantisedObservationsDiffer | TargetsAgree

type ctx_reason =                  (* O1–O3, once — the resolution-outcome type;
                                     shared by CtxUnavailable / preflight_O1_O2 /
                                     eval_O3, so it takes no other constructor *)
  | ArtifactMismatch | SpecMismatch | RepNotReproduced

type o_reason =                    (* stage 2, per candidate *)
  | ExecMissing | ExecInputMismatch | ExecFailure | ExecFuelExhausted
  | NonDeterministic | ObsOutOfRange

type integrity_reason =            (* frozen first-failure precedence — top to bottom *)
  | BadCommitmentEncoding of string
  | SignerNotAuthorised
  | SignatureInvalid
  | ManifestPolicyMismatch
  | ManifestAuditInstanceMismatch
  | ManifestContextMismatch
  | LedgerMismatch          of { index : nat }
  | RecordIdentityMismatch  of { field : string }
  | CompletenessMalformed

type campaign_obstruction =
  | RecordIntegrity      of integrity_reason
  | ValidationFuelExhausted                        (* validate_campaign ran out — §5; unreachable for a loaded config *)
  | TranscriptMalformed  of { reason : string ; wire_digest : digest }
  | ContextObstruction   of ctx_reason         (* genuine O1/O2/O3 failure, once *)
  | CampaignFuelExhausted
  | CampaignCandidateCountExceeded
  | InconsistentContextBundle                   (* nullary; cb = CtxNotNeeded with a
                                                   completed stage 1 that produced
                                                   Pending candidates — not
                                                   producible by `capture`; no
                                                   O1/O2/O3 check ran *)
  | WitnessObstruction   of { primary_index : nat ; primary_reason : o_reason ; other_indices : nat list }

type check_outcome = [ `Pass | `Fail | `NotEvaluated ]
type finding = { check_id : string ; outcome : check_outcome ;
                 reason : string option ; offending : canonical_value option }
```

`check_id` ∈ `{ "B6","B1a","B1b","B1c","B2","B3","B4","B5",
               "C1","C2","C3","C5","O1","O2","O3","O6","O4","O5","C4" }` — stable
labels; the frozen order is the sequence here. This set is the domain for
**stage** findings (`stage1_findings`, `stage2` findings, `context_findings`,
`rejection_report.findings`).

Findings in `replay_result.record_findings` (the `crosscheck` /
`crosscheck_budget` output, §6.5) instead carry `check_id` from the **closed
advisory family** `{ "budget_advisory", "campaign_record_mismatch",
"campaign_record_undecodable" }`, disjoint from the stage set; for that family
`offending` is always omitted and `reason`, when present, is a fixed
lower-snake-case token. Grammar and deterministic order:
`PHASE_1_ADVISORY_FINDING_IDS_ERRATUM.md` (consistency erratum, reviewer-concurred
2026-09-10).

## 3. The runner, the transcript, and the faithfulness assumption

```ocaml
type exec_outcome = `Ok of Vec Z n_obs | `Failed of exec_fail_reason | `Exhausted
type call_key     = { phase : [ `ContextProbe | `Stage2 of nat ] ; role : [ `Probe | `X | `Y ] ; repeat : nat }
type call_request = { key : call_key ; input : Vec Z n_pre }
type exec_event   = { key : call_key ; input : Vec Z n_pre ; outcome : exec_outcome }   (* NO fuel field *)
type exec_transcript = exec_event list

runner : environment → call_request → exec_outcome                      (* F.3 — effectful, fallible *)
```

The **capture wrapper** turns a request into an event:

    issue (env) (req : call_request) : exec_event
      := { key = req.key ; input = req.input ; outcome = runner env req }

so `e.key` and `e.input` **equal the request's by construction** — the runner never
chooses the key or input. (For a *tampered offline* transcript these may not match;
O6b / O3 catch that.)

### 3.1 Atomic transcript parsing (offline replay only)

    parse_result   := `Malformed  of { reason : string ; wire_digest : digest }
                     | `Wellformed of { transcript : exec_transcript ; wire_digest : digest }

    parse_transcript : verifier_config → bytes → parse_result
      (* `wire_digest := digest_bytes_v1("pcfw.exec_transcript_wire.v1", <raw bytes>)` is set on BOTH
         branches.  `Malformed` if: |bytes| > vcfg.bundle_limits.max_transcript_bytes; or any wire
         event has a wrong-length input / `Ok` vector or an unrecognised outcome tag; or the wire
         structure is not a list of events. Otherwise `Wellformed`, with every exec_event well-formed
         by construction. *)

The **live** pipeline never parses — the gated capture (§6.4) yields a typed
`exec_transcript` directly and it is serialised to `pcfw.exec_transcript.v1` bytes
only for the replay package. `assess_validated` (§6.7) takes a `transcript_source`;
the live path passes `` `LiveTranscript {transcript = tr ; ctx_bundle = co.ctx_bundle}``.

    lookup_unique tr k := match [ e ∈ tr | e.key = k ] with       (* raw key matches counted FIRST *)
                          | [e] when event_schema_valid(e) → Some e
                          | _ → None

### 3.2 The faithfulness assumption (F.3) — never discharged

    faithful_transcript (tr) (ctx : AuditContext P) : Prop
      :=  ∀ e ∈ tr, ∀ v, e.outcome = `Ok v  →  v = model ctx e.input

- **O4 establishes repeatability only** — a repeatably-wrong runner passes O4.
- **O6 establishes input-correctness and success** — each event exists uniquely,
  is `` `Ok ``, and `e.input = preproc ctx x/y`.

`ObservationBinding(ctx, x, o_x)` follows **conditionally** from O6 plus the assumed
`faithful_transcript tr ctx`. O4 is a *guard* on non-repeatable unfaithfulness; the
residual (repeatable) risk is a listed `faithful_transcript` assumption on every
`INADMISSIBLE` certificate, which binds `tr` by `transcript_evidence` (§9).

## 4. Per-submission checks

### 4.1 `stage1_check` — tier B, then C1/C2/C3/C5. Pure; no transcript, no context.

    stage1_check :
      verifier_config → policy_document → Policy → nat → candidate_submission → stage1_result

    stage1_result := {
      submission_index ; submission_digest : digest ;
      candidate_id : string option ; semantic_candidate_digest : digest option ;   (* Some for EVERY `Parsed *)
      verdict : [ `Rejected of b_reason | `NotAWitness of c_reason | `Pending of pending_submission ] ;
      findings : finding list ;
    }

    pending_submission := {
      submission_index ; submission_digest ; semantic_candidate_digest : digest ;
      candidate : parsed_candidate ; stage1_findings : finding list ;
    }

Frozen order (first failure's reason wins; unreached `` `NotEvaluated ``):
B6 (wire size, **first** — pure length check) → B1a (UTF-8) → B1b (bounded
structural parse; nesting/recursion → `BundleLimitExceeded`) → B1c (`schema_version`
= payload) → B2 (no unknown critical / override field) → B3 (`policy_hash =
policy_digest`) → B4 (`x`,`y` each `n_in P` integer literals) → B5 (grammar +
representable in the component `integer_type`, `AUDIT_POLICY_AND_EVIDENCE.md` §2.5.1)
→ C1 (`x ≠ y`) → C2 (`D_P x`) → C3 (`D_P y`) → C5 (`Φ_P x ≠ Φ_P y`). If all pass,
`` `Pending ps ``. (Full table: `AUDIT_POLICY_AND_EVIDENCE.md` §6.)

### 4.2 `stage2_check` — pure function of the transcript. O6 → O4 → O5 → C4.

    stage2_check : resolved_context → verifier_config → exec_transcript → pending_submission → stage2_result

    stage2_result := {
      submission_index ;
      verdict : [ `WitnessCheckObstructed of o_reason | `NotAWitness of c_reason
                | `ValidWitness of witness_data ] ;
      findings : finding list ;
    }

    witness_data := {
      submission_index ; submission_digest ; semantic_candidate_digest : digest ;
      x : Vec Z n_in ; y : Vec Z n_in ; preproc_x : Vec Z n_pre ; preproc_y : Vec Z n_pre ;
      o_x : Vec Z n_obs ; o_y : Vec Z n_obs ; quantised_o_x : Vec Z n_obs ; quantised_o_y : Vec Z n_obs ;
      phi_x : bool ; phi_y : bool ; stage2_findings : finding list ;
    }

Let `i = ps.submission_index`, `px = preproc rc.ctx ps.candidate.x`,
`py = preproc rc.ctx ps.candidate.y`, `ev(r,k) = lookup_unique tr {`Stage2 i, r, k}`.

| # | id | check | fail → |
|---|---|---|---|
| 1a | O6 | `ev(`X,0/1)`, `ev(`Y,0/1)` all `` `Some `` | `ExecMissing` |
| 1b | O6 | `ev(`X,k).input = px`, `ev(`Y,k).input = py` | `ExecInputMismatch` |
| 1c | O6 | no outcome `` `Failed ``/`` `Exhausted `` | `ExecFailure` / `ExecFuelExhausted` |
| 1d | O6 | `4 * model_call_fuel ≤ vcfg.per_candidate_limits.max_fuel_per_candidate` | `ExecFuelExhausted` |
| 2 | O4 | `ev(`X,0).value = ev(`X,1).value` (=: `o_x`); `ev(`Y,0).value = ev(`Y,1).value` (=: `o_y`) | `NonDeterministic` |
| 3 | O5 | `o_x`, `o_y` within `expected_observation_range` | `ObsOutOfRange` |
| 4 | C4 | `Q_P o_x = Q_P o_y` — ordinary inequality is a C-failure | `` `NotAWitness QuantisedObservationsDiffer `` |

On all passing, the kernel decides `CheckedWitness(rc.policy, x, y, o_x, o_y)` and
`verdict = ` `ValidWitness wd``.

## 5. `validate_campaign` — pure, once per pipeline, before any model call

    authenticated_campaign := { mc : manifest_commitment ; M : manifest ;
                                subs : candidate_submission list ; rec : campaign_record }

    validation_result :=
      | `Invalid         of { reason : integrity_reason ; fuel : fuel_ledger ; evidence : commitment_evidence }
      | `FuelObstructed  of { fuel : fuel_ledger ; evidence : commitment_evidence }
      | `Valid           of { campaign : authenticated_campaign ; fuel : fuel_ledger }

    validate_campaign : trusted_inputs → validation_result

Nine checks in the frozen `integrity_reason` order; the **first** failure is
returned. `charge` (§6.2) is applied **before** each phase's work, seeded
`{ budget = vcfg.campaign_limits.max_fuel ; consumed = 0 }`:

| step | charge (before) | check | fail → |
|---|---|---|---|
| 1 | `commitment_parse_fuel` | `parse_commitment ti.MCW = ` `Parsed mc`` | `Invalid { BadCommitmentEncoding msg ; … ; evidence = UnparsedCommitment ti.MCW }` |
| 2 | — | `mc.signer ∈ ta.authorised_signers` | `Invalid { SignerNotAuthorised ; … ; ParsedCommitment mc.digest }` |
| 3 | `signature_verify_fuel` | `key_of ta mc.signer = ` `Some k`` ∧ `ed25519_verify(k, mc.signature_bytes, utf8(mc.digest))` ∧ `mc.digest = digest_v1("pcfw.campaign_manifest.v1", to_cv(ti.M))` | `Invalid { SignatureInvalid ; … ; ParsedCommitment mc.digest }` |
| 4 | `manifest_bind_fuel` | `ti.M.policy_hash = …policy_digest` | `Invalid { ManifestPolicyMismatch ; … ; AuthenticatedCommitment mc.digest }` |
| 5 | — | `ti.M.audit_instance_id = …payload.audit_instance_id` | `Invalid { ManifestAuditInstanceMismatch ; … ; AuthenticatedCommitment mc.digest }` |
| 6 | — | `ti.M.context_digests = context_descriptor(ti.AR)` | `Invalid { ManifestContextMismatch ; … ; AuthenticatedCommitment mc.digest }` |
| 7 | `record_bind_fuel` | `ti.M.submission_digests = mapi (…) ti.subs` (element-wise, ordered, multiplicity kept) | `Invalid { LedgerMismatch{index} ; … ; AuthenticatedCommitment mc.digest }` |
| 8 | — | `ti.rec.{campaign_id,audit_instance_id,policy_hash,context_digests,manifest_digest}` agree | `Invalid { RecordIdentityMismatch{field} ; … ; AuthenticatedCommitment mc.digest }` |
| 9 | — | `ti.rec.completeness = Complete c ⇒ c` well-formed | `Invalid { CompletenessMalformed ; … ; AuthenticatedCommitment mc.digest }` |

`validation_fuel(reason)` = the sum of the phase charges completed before the
failure; `validation_fuel_ok = commitment_parse_fuel + signature_verify_fuel +
manifest_bind_fuel + record_bind_fuel`. Every branch's `fuel` has
`consumed = validation_fuel(...)`.

If any `charge` returns `` `Over ``, `validate_campaign` returns
`` `FuelObstructed { fuel = <ledger at the Over> ; evidence = <the stage reached> } ``.
**A loaded `verifier_config` requires `max_fuel ≥ validation_fuel_ok`**
(`AUDIT_POLICY_AND_EVIDENCE.md` §2.3), so `` `FuelObstructed `` from
`validate_campaign` is a **totality constructor, provably unreachable** for a
loaded config. (`CampaignFuelExhausted` during *capture* — §6.4 — is the normal
fuel-out path.)

`|subs| > max_candidates` is **not** a `validate_campaign` check — §6.4/§6.5.

## 6. The gated capture and `assess_validated`

### 6.1 Trusted inputs

    trusted_inputs := { AR ; MCW ; M ; subs ; rec ; vcfg ; env }

### 6.2 The fuel model — deterministic, charged before the work

- `model_call_fuel` — one forward-pass op count (fixed MLP shape; `inference_spec_digest`;
  `AUDIT_POLICY_AND_EVIDENCE.md` §2.5.3);
- `vcfg.fuel_schedule := { commitment_parse_fuel ; signature_verify_fuel ;
  manifest_bind_fuel ; record_bind_fuel ; preflight_fuel ; stage1_base_fuel ;
  stage1_per_byte_fuel : nat }`;
- `cost_stage1(b) := stage1_base_fuel + stage1_per_byte_fuel * min(|b|, max_wire_bytes + 1)`;
- `cost_candidate := 4 * model_call_fuel`.

`charge : fuel_ledger → nat → [ `Ok of fuel_ledger | `Over ]`
`:= λ L c. if L.consumed + c > L.budget then `Over else `Ok { L with consumed = L.consumed + c }`
— total. `fuel_model_digest` binds `model_call_fuel` + `fuel_schedule`.

### 6.3 The loaded context and the pure context helpers

O1/O2 and `eval_O3` need the **artifact bytes**, so context resolution begins with
one F.3 side-effecting fetch that produces an **immutable value** threaded, as
data, through capture and replay:

```ocaml
type loaded_context = {
  descriptor           : context_descriptor ;
  model_bytes          : bytes ;
  preproc_spec_bytes   : bytes ;
  inference_spec_bytes : bytes ;
  ctx                  : AuditContext P ;   (* F.3: preproc/model faithfully realise the *_spec bytes *)
}

load_context : environment → context_descriptor → [ `Unavailable of ctx_reason | `Loaded of loaded_context ]
  (* fetches the three byte-strings from the retrieval store and builds `ctx`.
     `Unavailable ArtifactMismatch` if a byte-string is missing. F.3; runs once. *)

type context_bundle :=
  | CtxNotNeeded                              (* `capture` issued no `load_context`:
                                                either stage 1 produced no `Pending
                                                candidate, or stage 1 did not
                                                complete (terminal fuel `Over — an
                                                earlier submission may already be
                                                `Pending).  `replay` with this
                                                bundle AND a completed stage 1 that
                                                did produce `Pending candidates is
                                                not a `capture` output: see §6.5. *)
  | CtxUnavailable of ctx_reason              (* load_context failed *)
  | CtxLoaded      of loaded_context

preflight_O1_O2 : loaded_context → [ `Fail of ctx_reason * finding list | `Ok of finding list ]
  (* PURE.  O1: digest_bytes_v1("pcfw.model_artifact.v1", lc.model_bytes) = lc.descriptor.model_artifact_digest.
     O2: likewise for preproc_spec_bytes / preprocessing_digest and inference_spec_bytes / inference_spec_digest. *)

eval_O3 : loaded_context → exec_event → Policy → [ `Fail of finding list | `Ok of resolved_context ]
  (* PURE.  the checkpoint shape/type enumerated by lc.inference_spec_bytes; the probe event's
     input = probe_input and outcome = `Ok probe_observation (AUDIT_POLICY_AND_EVIDENCE.md §2.5.2).
     On `Ok:  resolved_context := { policy = P ; ctx = lc.ctx ; descriptor = lc.descriptor }. *)

`load_context` is the **only** effectful step in context resolution; both entry
points capture its result into a `context_bundle` and pass it, as data, to
`assess_validated` / `replay`.

### 6.4 `capture` — the gated pass (F.3). **Every charge precedes the work it pays for.**

    capture : authenticated_campaign → verifier_config → policy_document → Policy
              → environment → (call_request → exec_outcome) → fuel_ledger
              → { transcript : exec_transcript ; issued : call_key list ; clo : campaign_obstruction option ;
                  ctx_bundle : context_bundle }
    (* `issued` and `clo` are for (CAP1); only `transcript` + `ctx_bundle` are retained/shipped *)

```text
capture(ac, vcfg, pd, P, env, run, L0):
  if |ac.subs| > vcfg.campaign_limits.max_candidates:                       (* no work, no calls *)
     return { transcript=[] ; issued=[] ; clo=Some CampaignCandidateCountExceeded ; ctx_bundle=CtxNotNeeded }

  (* ---- stage 1: charge THEN check, per submission.  A charge `Over is TERMINAL. ---- *)
  L := L0 ; s1 := []
  for i in 0 .. |ac.subs|-1:
     match charge L (cost_stage1 (ac.subs!i)) with
     | `Over →
         return { transcript=[] ; issued=[] ; clo=Some CampaignFuelExhausted ; ctx_bundle=CtxNotNeeded }
     | `Ok L' → L := L' ; s1 := s1 ++ [ stage1_check vcfg pd P i (ac.subs!i) ]
  pending := [ (i, ps) | s1!i.verdict = `Pending ps ]                       (* every submission was checked *)

  if pending = [] :
     return { transcript=[] ; issued=[] ; clo=None ; ctx_bundle=CtxNotNeeded }

  (* ---- load the context (F.3 fetch, once) ---- *)
  match load_context env (context_descriptor ac) with
  | `Unavailable rn →
     return { transcript=[] ; issued=[] ; clo=Some (ContextObstruction rn) ; ctx_bundle=CtxUnavailable rn }
  | `Loaded lc :
     (* ---- preflight: charge THEN check ---- *)
     match charge L preflight_fuel with
     | `Over → return { transcript=[] ; issued=[] ; clo=Some CampaignFuelExhausted ; ctx_bundle=CtxLoaded lc }
     | `Ok L1 :
        match preflight_O1_O2(lc) with
        | `Fail (rn,_) → return { transcript=[] ; issued=[] ; clo=Some (ContextObstruction rn) ; ctx_bundle=CtxLoaded lc }
        | `Ok _ :
           (* ---- probe: charge model_call_fuel THEN issue ---- *)
           match charge L1 model_call_fuel with
           | `Over → return { transcript=[] ; issued=[] ; clo=Some CampaignFuelExhausted ; ctx_bundle=CtxLoaded lc }
           | `Ok L2 :
              req_p := { key = {`ContextProbe,`Probe,0} ; input = probe_input }
              ev_p  := issue env req_p
              match eval_O3(lc, ev_p, P) with
              | `Fail _ → return { transcript=[ev_p] ; issued=[req_p.key] ;
                                   clo=Some (ContextObstruction RepNotReproduced) ; ctx_bundle=CtxLoaded lc }
              | `Ok rc :
                 evs := [ev_p] ; ks := [req_p.key] ; L := L2 ; clo := None
                 for (i, ps) in pending:
                    match charge L cost_candidate with
                    | `Over → clo := Some CampaignFuelExhausted ; break
                    | `Ok L' :
                       L := L'
                       px := preproc rc.ctx ps.candidate.x ; py := preproc rc.ctx ps.candidate.y
                       reqs := [ {key={`Stage2 i,`X,0}; input=px}, {key={`Stage2 i,`X,1}; input=px},
                                 {key={`Stage2 i,`Y,0}; input=py}, {key={`Stage2 i,`Y,1}; input=py} ]
                       evs := evs ++ [ issue env r | r ∈ reqs ]
                       ks  := ks  ++ [ r.key | r ∈ reqs ]
                 return { transcript=evs ; issued=ks ; clo ; ctx_bundle=CtxLoaded lc }
```

### 6.5 `replay` — the same charge-then-check control flow, reading `tr` and the `context_bundle`

    replay : authenticated_campaign → context_bundle → verifier_config → policy_document → Policy
             → fuel_ledger → exec_transcript → replay_result

```ocaml
type stage1_slot = { submission_index : nat ; result : [ `Done of stage1_result | `NotRun ] }
type stage2_slot = { submission_index : nat ; result : [ `Done of stage2_result | `NotRun ] }
type fuel_ledger = { budget : nat ; consumed : nat }

type replay_result = {
  stage1  : stage1_slot list ;      (* exactly |ac.subs| slots *)
  context : context_state ;
  stage2  : stage2_slot list ;      (* exactly |pending| slots *)
  fuel    : fuel_ledger ;
  clo     : campaign_obstruction option ;
  record_findings : finding list ;
}
```

`replay ac cb vcfg pd P L0 tr` performs the **identical** sequence of `charge`
calls and gate tests as §6.4, using `cb` where §6.4 used `load_context`'s result
and `lookup_unique tr <key>` for each `run`. A stage-1 `charge` `` `Over `` is a
**terminal return** (matching §6.4). The slot rule:

| §6.4 outcome | `stage1` | `context` | `stage2` (per `pending`) | `clo` |
|---|---|---|---|---|
| `\|subs\| > max_candidates` | all `` `NotRun `` | `NoContextNeeded` | — | `CampaignCandidateCountExceeded` |
| stage-1 `charge` `` `Over `` at `j` | `` `Done `` for `< j`, `` `NotRun `` for `≥ j` | `NoContextNeeded` | `` `NotRun `` | `CampaignFuelExhausted` |
| `pending = []` | all `` `Done `` | `NoContextNeeded` | — | `None` |
| `pending ≠ []` ∧ `cb = CtxNotNeeded` (stage 1 completed) | all `` `Done `` | `ContextBundleInconsistent` | `` `NotRun `` | `InconsistentContextBundle` |
| `cb = CtxUnavailable rn` | all `` `Done `` | `ContextUnresolved {rn ; O1_fail}` | `` `NotRun `` | `ContextObstruction rn` |
| preflight `charge` `` `Over `` | all `` `Done `` | `NoContextNeeded` | `` `NotRun `` | `CampaignFuelExhausted` |
| `preflight_O1_O2 = ` `Fail (rn,f)`` | all `` `Done `` | `ContextUnresolved {rn ; f}` | `` `NotRun `` | `ContextObstruction rn` |
| probe `charge` `` `Over `` | all `` `Done `` | `NoContextNeeded` | `` `NotRun `` | `CampaignFuelExhausted` |
| probe key missing / `eval_O3 = ` `Fail f`` | all `` `Done `` | `ContextUnresolved {RepNotReproduced ; f}` | `` `NotRun `` | `ContextObstruction RepNotReproduced` |
| `eval_O3 = ` `Ok rc``, candidate `charge` `` `Over `` at `j` | all `` `Done `` | `ContextResolved {rc ; O3_pass}` | `` `Done (stage2_check rc vcfg tr ps) `` for `< j`, `` `NotRun `` for `≥ j` | `CampaignFuelExhausted` |
| `eval_O3 = ` `Ok rc``, all fit | all `` `Done `` | `ContextResolved {rc ; O3_pass}` | `` `Done `` for all | `None` |

`replay` is a pure total function of its arguments. `record_findings :=
crosscheck(ac.rec.recorded_results, stage1, stage2) ++ crosscheck_budget(ac.rec.resource_budget, vcfg)`.
`crosscheck` compares `ac.rec.recorded_results` position-by-position against the
list of `submission_check_result` values the replay produced — a stage-1
`` `NotRun `` slot and a `` `Pending `` submission whose stage-2 slot is
`` `NotRun `` contribute none (§2.2.5: mandatory `submission_digest`, no
`not_run` outcome). `record_findings` draw `check_id` from the closed advisory
family (§2); their grammar and deterministic order are in
`PHASE_1_ADVISORY_FINDING_IDS_ERRATUM.md`. `decide` / `verdict_of` never read
`record_findings` — the verdict is the replayed verdict (T26).

### 6.6 The `` `NotRun `` theorem — scoped

- **`(CAP1)`** — let `co = capture ac vcfg pd P env run L0` and
  `rr = replay ac co.ctx_bundle vcfg pd P L0 co.transcript`. Then a `stage2_slot`
  in `rr` is `` `NotRun `` **iff** its `call_key`s are absent from `co.issued`
  **iff** `capture` issued no `call_request` for that candidate, and
  `rr.clo = co.clo`. (Proof: `replay` runs the identical gate/charge sequence over
  the identical `stage1_check` results and the same `context_bundle`; the
  transcript is exactly what `issue` recorded.)
- **`(REP1)`** — for an **arbitrary** `context_bundle` + `` `Wellformed tr ``: a
  `` `NotRun `` slot means "the verified schedule does not authorise or evaluate
  that candidate" — `replay` charges and gates independently of `tr` for stage 1 /
  preflight / probe fuel, and ignores any stage-2 events for a candidate it did
  not reach. A witness never comes from a `` `NotRun `` slot.

`(CAP1)` holds **only for a live certificate** (`transcript_evidence = LiveCapture`,
§9), where `co.ctx_bundle` and `co.transcript` are the unmodified capture output.
An offline certificate (`OfflineTranscript`) carries only `(REP1)`.

### 6.7 `assess_validated` and `decide`

    context_state :=
      | NoContextNeeded
      | ContextUnresolved of { reason : ctx_reason ; findings : finding list }
      | ContextResolved   of { context : resolved_context ; findings : finding list }
      | ContextBundleInconsistent   (* nullary — no reason, no findings; §6.5 row
                                       `pending ≠ [] ∧ cb = CtxNotNeeded` *)

    resolved_context := { policy : Policy ; ctx : AuditContext policy ; descriptor : context_descriptor }

    assessment_outcome :=
      | Inadmissible    of certificate
      | Exact           of certificate          (* not produced in v0 *)
      | Obstructed      of certificate
      | Underdetermined of campaign_report
    verdict_of : assessment_outcome → CampaignVerdict          (* total *)

    replay_input := `InvalidFuel of fuel_ledger | `ReplayDone of replay_result

    transcript_source :=
      | `LiveTranscript   of { transcript : exec_transcript ; ctx_bundle : context_bundle }
      | `OfflineParse     of { result : parse_result ; ctx_bundle : context_bundle }

    build_certificate :
      cert_body_input → trusted_inputs → replay_input → transcript_evidence → commitment_evidence → certificate

    assess_validated : trusted_inputs → validation_result → transcript_source → assessment_outcome
      :=  match vr with
          | `Invalid { reason ; fuel ; evidence } →
              Obstructed (build_certificate
                (ObstructedInput { obstruction = RecordIntegrity reason ;
                                   failed_obligation = obligation_of_integrity reason ; context_findings = [] })
                ti (`InvalidFuel fuel) NoTranscript evidence)
          | `FuelObstructed { fuel ; evidence } →
              Obstructed (build_certificate
                (ObstructedInput { obstruction = ValidationFuelExhausted ;
                                   failed_obligation = "raise campaign_limits.max_fuel" ; context_findings = [] })
                ti (`InvalidFuel fuel) NoTranscript evidence)
          | `Valid { campaign = ac ; fuel = L0 } →
              let commit_ev := AuthenticatedCommitment ac.mc.digest in
              match src with
              | `OfflineParse { result = `Malformed { reason ; wire_digest } ; _ } →
                  Obstructed (build_certificate
                    (ObstructedInput { obstruction = TranscriptMalformed { reason ; wire_digest } ;
                                       failed_obligation = "supply a well-formed execution transcript" ;
                                       context_findings = [] })
                    ti (`InvalidFuel L0) (MalformedTranscript { reason ; wire_digest }) commit_ev)
              | `LiveTranscript { transcript = tr ; ctx_bundle = cb } →
                  let rr  := replay ac cb ti.vcfg ti.AR.policy_document ti.AR.policy L0 tr in
                  let tev := LiveCapture { transcript_digest = digest_v1("pcfw.exec_transcript.v1", to_cv(tr)) } in
                  decide rr ac ti tr tev commit_ev
              | `OfflineParse { result = `Wellformed { transcript = tr ; wire_digest } ; ctx_bundle = cb } →
                  let rr  := replay ac cb ti.vcfg ti.AR.policy_document ti.AR.policy L0 tr in
                  let tev := OfflineTranscript { transcript_digest = digest_v1("pcfw.exec_transcript.v1", to_cv(tr)) ;
                                                 wire_digest = wire_digest } in
                  decide rr ac ti tr tev commit_ev

`decide rr ac ti tr tev commit_ev` reads the single `rr`, binds `rc := r.context`
for `rr.context = ContextResolved r`, and returns `Inadmissible` / `Obstructed` /
`Exact` / `Underdetermined`, passing `` `ReplayDone rr `` + `tev` + `commit_ev` to
`build_certificate` (or `build_campaign_report` for `Underdetermined`).

**Frozen precedence:** `` `Invalid `` (record integrity, §5) **>** `` `FuelObstructed ``
(§5, dead) **>** `` `Malformed `` transcript (§3.1) **>** a within-budget
`` `ValidWitness `` **>** `rr.clo` **>** all-checked-obstructed **>** `EXACT`
(dead code, §6.9) **>** `UNDERDETERMINED`.

`rr.clo = Some InconsistentContextBundle` (the §6.5 row `pending ≠ [] ∧ cb =
CtxNotNeeded`) takes `failed_obligation = "reconstruct_or_supply_context_bundle"`
and `context_findings = []`. It cannot dominate a within-budget `` `ValidWitness ``
because that pairing makes every pending stage-2 slot `` `NotRun `` (no witness can
exist), so the precedence is not observably affected.

### 6.8 Two entry points, `validate_campaign` once each

- **Live** (`AUDIT_POLICY_AND_EVIDENCE.md` §2.4 step 7):
  `vr := validate_campaign ti` (once) → on `` `Valid {campaign=ac; fuel=L0}``,
  `co := capture ac vcfg pd P env run L0` → `assess_validated ti vr
  (` `LiveTranscript { transcript = co.transcript ; ctx_bundle = co.ctx_bundle }``)`.
  `co.transcript` and a serialised `context_bundle` are shipped in the package.
- **Offline replay** (`AUDIT_POLICY_AND_EVIDENCE.md` §9):
  `vr := validate_campaign ti` (once);
  `cb :=` reconstruct `context_bundle` from the shipped artifact bytes via
  `load_context env′` where `env′` reads the package;
  `pr := parse_transcript vcfg <retained wire bytes>` → `assess_validated ti vr
  (` `OfflineParse { result = pr ; ctx_bundle = cb }``)`.

`validate_campaign ti` is computed **exactly once** in each pipeline; `load_context`
runs once (live in `capture`, offline before `assess_validated`); the certificate's
`fuel_ledger` is `vr.fuel` (obstruction branches) or `rr.fuel` (replay branch).
`(T2)` (§7) is over `assess_validated ti (validate_campaign ti) src`.

### 6.9 `EXACT` is dead code in v0 — a theorem

`valid_completeness_certificate(ctx, c)` looks up `c.scheme` in the
completeness-scheme registry, **empty in v0**; `false` for every `c`. `decide`'s
`EXACT` branch never fires and is only reachable on `ContextResolved`.

### 6.10 What each verdict warrants

| Verdict | Warrants |
|---|---|
| `INADMISSIBLE` | `¬ FibreConstant(rc.ctx)` on `D_P` via `(A1)` — `rc.ctx = r.context.ctx` for `rr.context = ContextResolved r`, `= cb.lc.ctx` — from a within-budget stage-2 `` `ValidWitness `` under a `` `Valid `` campaign, **conditional on the listed F.3 assumptions**: `faithful_transcript tr rc.ctx` (O6 gives input-correctness + success; O4 guards non-repeatable unfaithfulness; §3.2), and the `loaded_context` well-formedness (`cb.lc.ctx` faithfully realises the committed spec bytes; F.3, §6.3). `(REP1)` holds for **every** certificate (a `` `Done `` slot required an open gate after `ContextResolved`); `(CAP1)` holds **only** when `transcript_evidence = LiveCapture` (the transcript and `context_bundle` are an unmodified `capture` output). |
| `EXACT` | `FibreConstant(rc.ctx)` via `(E1)`. **Unreachable in v0** (§6.9). |
| `UNDERDETERMINED` | "well-formed transcript, `` `Valid `` campaign, no within-budget stage-2 `` `ValidWitness ``, `rr.clo = None`, no all-obstructed, `completeness` did not yield `EXACT`." Nothing about `FibreConstant`. |
| `OBSTRUCTED` | `validate_campaign` returned `` `Invalid `` (`RecordIntegrity`) or `` `FuelObstructed ``, **or** `parse_transcript` returned `` `Malformed `` (`TranscriptMalformed`), **or** `rr.clo ≠ None` (including `InconsistentContextBundle` — `cb = CtxNotNeeded` with a completed stage 1 that produced `Pending` candidates; obligation `reconstruct_or_supply_context_bundle`; `context = ContextBundleInconsistent`, every pending stage-2 slot `` `NotRun ``, no finding; `(T2)` unaffected since no `` `ValidWitness `` can arise), **or** every checked candidate was `` `WITNESS_CHECK_OBSTRUCTED ``. The certificate names one deterministic primary cause, the repair obligation, the O1–O3 `context_findings`, and the matching `commitment_evidence` / `transcript_evidence`. |

## 7. Kernel versus campaign — `(T2)`

- `(T1)` — kernel theorem, witness level, `Policy` only.
- `(A1)` — corollary adding `ObservationBinding`, derived **conditionally** from
  O6 plus the assumed `faithful_transcript tr ctx`. O4 = repeatability only.
- `(T2)` — verified-orchestration property, not a kernel theorem, over the pure
  total `assess_validated`. Let `V := validate_campaign ti`, `src` a
  `transcript_source` carrying `(cb, tr)` (a `` `Wellformed ``/live case), and,
  when `V = ` `Valid {campaign = ac ; fuel = L0}``,
  `R := replay ac cb ti.vcfg ti.AR.policy_document ti.AR.policy L0 tr`:

      (T2)  verdict_of (assess_validated ti V src) = INADMISSIBLE
            ⟺  (∃ ac L0, V = `Valid {campaign = ac ; fuel = L0})
                ∧ (∃ {_, `Done s} ∈ R.stage2, ∃ wd, s.verdict = `ValidWitness wd)

  with the `(T2-sound)` / `(T2-complete)` split. `assess_validated` re-uses the
  **given** `V` — it does not call `validate_campaign` again — and evaluates `R`
  once. Reproduced identically in `CLAIM_AND_DEFINITIONS.md` §6.3,
  `PROJECT_CHARTER.md` §4.3, `TRUST_BOUNDARY.md` §6, `NON_CLAIMS.md` #14.
- The §5–§6 vocabulary is orchestration, not the kernel.
- The single-submission checker cannot return `UNDERDETERMINED`.
- `CANDIDATE_ACCEPTED` → `ACCEPTED_BUNDLE` (`PHASE_0_SPECIFICATION_AMENDMENTS.md` A3).

## 8. Prior-art note (terminology)

| Meaning | This project | PCOA | PCSE |
|---|---|---|---|
| pre-classification rejection of malformed / unauthenticated input | `REJECTED_BUNDLE` | `INADMISSIBLE` / `GatedInadmissible` | `¬ admissible_assessment_input` |
| validated target-divergent fibre collision | `INADMISSIBLE` | (no equivalent) | (no equivalent) |
| no realising state / factorisation obstructed | `OBSTRUCTED` | `OBSTRUCTED` | — |

PCOA's `AdmissibilityGate` is not imported; its `GatedInadmissible` constructor is
not renamed. `BundleResult`, `WitnessResult`, `CampaignVerdict` are defined from
first principles.

## 9. Artefacts by result

```ocaml
type cert_body_input =
  | InadmissibleInput of { primary : witness_data ; others : nat list ; all_findings : finding list }
  | ExactInput        of { completeness : completeness_certificate }
  | ObstructedInput   of { obstruction : campaign_obstruction ; failed_obligation : string ;
                           context_findings : finding list }

type commitment_evidence =
  | UnparsedCommitment    of manifest_commitment_wire
  | ParsedCommitment      of digest        (* parsed, NOT authenticated *)
  | AuthenticatedCommitment of digest      (* authentication passed (steps 1–3) *)

type transcript_evidence =
  | NoTranscript                                          (* validation obstruction — capture never ran *)
  | MalformedTranscript of { reason : string ; wire_digest : digest }
  | LiveCapture         of { transcript_digest : digest } (* unmodified capture output — (CAP1) applies *)
  | OfflineTranscript   of { transcript_digest : digest ; wire_digest : digest }   (* retained bytes — only (REP1) *)

type cert_body =
  | `Inadmissible of { primary : witness_data ; additional_valid_witness_indices : nat list ; all_findings : finding list }
  | `Exact        of { completeness : completeness_certificate }
  | `Obstructed   of { obstruction : campaign_obstruction ; failed_obligation : string ; context_findings : finding list }

type certificate = {
  policy_digest ; context_digests : context_descriptor ;    (* = ac.M.context_digests; binds the loaded_context bytes by O1/O2 *)
  commitment_evidence : commitment_evidence ;
  transcript_evidence : transcript_evidence ;                (* NoTranscript | MalformedTranscript | LiveCapture | OfflineTranscript *)
  verifier_config_digest ; fuel_model_digest : digest ;
  fuel_ledger : fuel_ledger ;         (* vr.fuel on an obstruction branch; rr.fuel on the replay branch *)
  verifier_digest ; kernel_digest : digest ; rocq_commit : string ;
  extraction_assumptions : string list ; execution_chain_descriptor : string ;
  configured_limits : limit_id list ; fired_limits : limit_id list ;
  assumptions : string list ;         (* incl. faithful_transcript for `Inadmissible *)
  body : cert_body ;
}

build_certificate :
  cert_body_input → trusted_inputs → replay_input → transcript_evidence → commitment_evidence → certificate
```

`verdict(cert.body)` is total. `campaign_report` and `rejection_report`:

```ocaml
type campaign_record_summary = { campaign_id ; audit_instance_id : string ;
                                 policy_hash ; manifest_digest : digest ; completeness : completeness_status }

type campaign_report = {
  manifest_digest ; policy_digest : digest ; context_digests : context_descriptor ;
  verifier_config_digest : digest ; transcript_evidence : transcript_evidence ; fuel_ledger : fuel_ledger ;
  replay : replay_result ; record : campaign_record_summary ; assumptions : string list ;
}

type rejection_report = { submission_index : nat ; submission_digest : digest ;
                          reason : b_reason ; findings : finding list }
```

| Result | Artefact |
|---|---|
| `INADMISSIBLE` | `certificate` `` `Inadmissible `` (smallest-`submission_index` `` `ValidWitness ``). |
| `EXACT` | `certificate` `` `Exact `` (not produced in v0). |
| `OBSTRUCTED` | `certificate` `` `Obstructed `` — one deterministic primary `campaign_obstruction`. |
| `UNDERDETERMINED` | `campaign_report`. |
| a single `` `REJECTED_BUNDLE `` submission | `rejection_report`. |

## 10. Machine-readable findings

One `finding` per check reached, `check_id` from §2, in the frozen order.
`CampaignVerdict` = `verdict_of (assess_validated ti (validate_campaign ti) src)`,
a total function of `(trusted_inputs, transcript_source)`.

## 11. Manual examples — specification §16

| Case | validation / parse | stage 1 | context | stage 2 | `CampaignVerdict` |
|---|---|---|---|---|---|
| Valid target-divergent operational collision (live) | `Valid` / `LiveTranscript` | `` `Pending `` | `ContextResolved` | `` `ValidWitness wd `` | `INADMISSIBLE`; `transcript_evidence = LiveCapture`; `(CAP1)` + `(REP1)` |
| Same, re-checked offline from the retained package | `Valid` / `OfflineParse `Wellformed` | `` `Pending `` | `ContextResolved` | `` `ValidWitness wd `` | `INADMISSIBLE`; `transcript_evidence = OfflineTranscript`; `(REP1)` only |
| `Q_P(o_x) ≠ Q_P(o_y)` / target agree / identical inputs / input ∉ `D_P` | `Valid` | `` `NotAWitness `` or `` `Pending ``→C4 | as needed | — / C4 | `UNDERDETERMINED` |
| `x`/`y` bad structure / bad literal / bad UTF-8 / over `max_wire_bytes` / bad schema / wrong `policy_hash` / override field | `Valid` | `` `Rejected `` (B4/B5/B1a/B6/B1b-c/B3/B2) | — | — | `recorded_failures`; not an obstruction |
| `MCW` bad hex | — | — | — | — | `OBSTRUCTED` / `RecordIntegrity (BadCommitmentEncoding …)`; `commitment_evidence = UnparsedCommitment`; `consumed = commitment_parse_fuel` |
| signer not authorised / signature invalid | — | — | — | — | `OBSTRUCTED` / `RecordIntegrity (SignerNotAuthorised / SignatureInvalid)`; `ParsedCommitment mc.digest`; `consumed = commitment_parse_fuel` (+`signature_verify_fuel` for the latter) |
| `M` ↔ `AR` / ledger / `rec` identity mismatch | — | — | — | — | `OBSTRUCTED` / `RecordIntegrity <first-failure>`; `AuthenticatedCommitment mc.digest`; `consumed = validation_fuel(reason)` |
| retained wire transcript does not parse (offline) | `Valid` / `Malformed {reason ; wire_digest}` | — | — | — | `OBSTRUCTED` / `TranscriptMalformed {reason ; wire_digest}`; `transcript_evidence = MalformedTranscript`; `consumed = validation_fuel_ok` |
| stage-1 fuel `` `Over `` at `j` (terminal) | `Valid` | `` `Done `` for `< j`, `` `NotRun `` for `≥ j` | `NoContextNeeded` (context never reached) | `` `NotRun `` | `OBSTRUCTED` `clo = CampaignFuelExhausted` |
| artifact bytes unavailable (`load_context` fails) — ≥1 `` `Pending `` | `Valid` | `` `Pending `` | `ContextUnresolved ArtifactMismatch` — **no probe call** | `` `NotRun `` | `OBSTRUCTED`, `clo = ContextObstruction ArtifactMismatch` |
| O1 / O2 digest mismatch — ≥1 `` `Pending `` | `Valid` | `` `Pending `` | `ContextUnresolved (ArtifactMismatch / SpecMismatch)` — **no probe call** | `` `NotRun `` | `OBSTRUCTED`, `clo = ContextObstruction …` |
| probe fuel over | `Valid` | `` `Pending `` | `NoContextNeeded` — **no probe call** | `` `NotRun `` | `OBSTRUCTED`, `clo = CampaignFuelExhausted` |
| probe issued, O3 fails | `Valid` | `` `Pending `` | `ContextUnresolved RepNotReproduced` — **no candidate calls** | `` `NotRun `` | `OBSTRUCTED`, `clo = ContextObstruction RepNotReproduced` |
| stage-2 event absent / duplicate key / wrong input / `` `Failed ``/`` `Exhausted `` | `Valid` | `` `Pending `` | `ContextResolved` | `` `WitnessCheckObstructed `` (O6) | per §6.7 |
| two `` `Ok `` events for one input, different values | `Valid` | `` `Pending `` | `ContextResolved` | `` `WitnessCheckObstructed NonDeterministic `` (O4) | per §6.7 |
| raw observation outside `expected_observation_range` | `Valid` | `` `Pending `` | `ContextResolved` | `` `WitnessCheckObstructed ObsOutOfRange `` (O5) | per §6.7 |
| candidate fuel covers only a prefix of pending | `Valid` | `` `Pending `` | `ContextResolved` | prefix `` `Done ``, rest `` `NotRun `` | `OBSTRUCTED` `clo = CampaignFuelExhausted` — unless an earlier within-budget `` `ValidWitness `` exists |
| `\|subs\| > max_candidates` | `Valid` | all `` `NotRun `` | `NoContextNeeded` | not run | `OBSTRUCTED` `clo = CampaignCandidateCountExceeded` (`THREAT_MODEL.md` T14) |
| every checked candidate obstructed (mixed reasons) | `Valid` | `` `Pending ``… | `ContextResolved` | all `` `WitnessCheckObstructed `` | `OBSTRUCTED` `WitnessObstruction { primary = lowest index, … }` |
| advisory `recorded_results` disagree with the replay | `Valid` | — | — | — | verdict unchanged; `campaign_record_mismatch` in `record_findings` |
| heuristic search returns no submission / `` `Complete c `` unrecognised scheme | `Valid` | — | — | — | `UNDERDETERMINED` |

Malformed policy → `load_policy` returns `` `LoadError `` and no assessment runs
(`AUDIT_POLICY_AND_EVIDENCE.md` §2.3). With the integer model NaN/infinity cannot
arise; `ExecFailure` covers a runner-reported internal failure or the F.3
wall-clock/memory watchdog.
