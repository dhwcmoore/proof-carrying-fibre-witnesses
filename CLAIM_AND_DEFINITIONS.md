# Claim and Definitions

**Deliverable:** Phase 0, Unit 0B
**Status:** Draft for Unit 0G ratification. **Revision 14** — `assessment_outcome`
carries a `certificate` in every constructor. `loaded_context` is an explicit
immutable value (one F.3 `load_context`) threaded through `capture` / `replay` /
`assess_validated`, so `preflight_O1_O2` / `eval_O3` / `resolved_context` are
constructible. Stage-1 fuel `` `Over `` is a terminal return. `transcript_source`
keeps entry-point provenance; `transcript_evidence` = `LiveCapture` (`(CAP1)`) vs
`OfflineTranscript` (`(REP1)` only). One `validate_campaign` per pipeline;
charge-before-work; `` `FuelObstructed `` dead. Authored fresh.
**Normative:** the definitions and theorem targets here govern the Rocq
development.

---

## 1. Purpose

Eliminate ambiguity in the words *observation*, *representation*, *fibre*,
*confusability*, *target*, *policy*, *witness*, *context*, and *certificate*;
state exactly what the kernel proves and what the assurance argument adds; keep
the three input types distinct; and pin every formal object's parameters and
carrier types so the Phase 1 Rocq types are determined.

## 2. Carrier types

The semantic kernel operates on **length-indexed vectors** and matrices:

    Vec T n        := Coq Vector.t T n         (a T-vector of exactly n entries)
    Mat T r c      := Vec (Vec T c) r          (r rows, each a c-vector)

The non-kernel, **system-binding** wire parser (`TRUST_BOUNDARY.md` §F.3 — it is a
trusted-for-binding component, not part of the untrusted environment) validates
every wire length against the policy and **constructs** the length-indexed value,
or fails. A wire length mismatch is a tier-B rejection; a re-execution length
mismatch is a tier-O obstruction (`AUDIT_POLICY_AND_EVIDENCE.md` §6). The kernel
therefore never receives a wrong-length object, and `Q_P`, `D_P`, `Φ_P` are
**total** at their declared types.

Matrix shape is a type-level fact: `W : Mat Z r c` *is* an `r × c` matrix. There is
no `length`-returns-a-pair operation.

## 3. Spaces and maps

A `Policy` value `P` determines three natural-number dimensions, written
`n_in P`, `n_pre P`, `n_obs P`, and the objects below. (In the Rocq development
these are projections of the `Policy` record; the dependent vector types below
depend on them explicitly.)

| Symbol | Type | Meaning |
|---|---|---|
| `X_raw P` | `Vec Z (n_in P)` | raw input: exact integers, declared per-component type and scale, after parsing and canonicalisation |
| `X_model P` | `Vec Z (n_pre P)` | the model's input after preprocessing |
| `O P` | `Vec Z (n_obs P)` | the observable representation's value |
| `Õ P` | `Vec Z (n_obs P)` | quantised observation |
| `D_P` | `Vec Z (n_in P) → Prop` | authorised domain: axis-aligned box `∀ i, lo_i ≤ x_i ≤ hi_i`; decidable |
| `Q_P` | `Vec Z (n_obs P) → Vec Z (n_obs P)` | operational-resolution map: component-wise `q_i = rounddiv(o_i, w_i, quantisation_rounding_mode)`, `w_i > 0`, **no saturation** (§7) |
| `Φ_P` | `Vec Z (n_in P) → bool` | target predicate on **raw** inputs; one constructor of the closed in-kernel registry (§8) |

`D_P`, `Q_P`, `Φ_P` are determined by `P` alone and are the only semantic objects
the kernel needs. Where the policy is clear from context this document abbreviates
`n_in P` to `n_in`, etc.

The model artifact is **not** a policy field. A policy digest binds an artifact's
*identity*; it is not the semantic function. The resolved semantics live in an
**audit context**.

### 3.1 Audit context

    AuditContext (P : Policy) := {
      preproc : Vec Z (n_in P)  → Vec Z (n_pre P) ;   (* the resolved N_P *)
      model   : Vec Z (n_pre P) → Vec Z (n_obs P) ;   (* the resolved M_A at the declared checkpoint *)
    }

so an inhabitant `C : AuditContext P` carries its policy in its type. Write
`policy C := P`, `preproc C`, `model C`.

Well-formedness of `C` (a system-binding assumption, `TRUST_BOUNDARY.md` §F.3):
`preproc` realises the committed preprocessing spec (`preprocessing_digest`);
`model` realises the committed model artifact (`model_artifact_digest`) under the
committed inference specification (`inference_spec_digest`).

Write `M̃_C : Vec Z n_in → Vec Z n_obs` for the operational observation map in
context `C`:

    M̃_C x := Q_P (model C (preproc C x))

### 3.2 The orchestration model — a trace-explicit assessment algebra

The formal `Policy` `P` is not the wire-level policy document, and the pure
`AuditContext` cannot represent a resolution or execution failure. The assessment
is a pure `validate_campaign` (**once per pipeline**), one F.3 `load_context`
fetch producing an immutable `loaded_context`, a **gated** physical capture
producing an `exec_transcript`, then the pure total `assess_validated` (which
re-uses the given `validation_result` and never re-validates). Every verdict
object is a **pure total function of `(trusted_inputs, validation_result,
transcript_source)`** (§3.2.2), where `transcript_source` carries the captured
`context_bundle` and either the live `exec_transcript` or an offline
`parse_result`.

| object | trust | role |
|---|---|---|
| `Policy P` | policy-binding assumption (F.2) | kernel-facing: `D_P`, `Q_P`, `Φ_P` |
| `AuditContext P` | — | **pure**, `= loaded_context.ctx`, used in `(A1)` |
| `loaded_context` | F.3: `ctx` realises the committed spec bytes | model/preproc bytes + the pure `ctx`; threaded as data |
| `exec_transcript` | one F.3 capture, then **data** | the record of the model calls the verifier made |
| `faithful_transcript tr ctx` | F.3 residual assumption — **never discharged** (O4 = repeatability only) | links `` `Ok `` transcript values to `model ctx` |
| `verifier_config` | **trusted input** | limits (fuel + bundle) + the `trust_anchor` |

#### 3.2.1 Policy load

    load_policy : policy_document → [ `LoadError of load_reason | `Loaded of Policy ]

Authority-side (`AUDIT_POLICY_AND_EVIDENCE.md` §2.3). A `` `Loaded P `` result
carries the **policy-binding assumption** (F.2): `n_in P`, `n_pre P`, `n_obs P`,
`D_P`, `Q_P`, `Φ_P` faithfully realise what the payload's dimensions, `domain`,
`quantisation`, `quantisation_rounding_mode`, and `predicate_id` declare.

    AuditRequest := { policy_document : policy_document ; policy : Policy }

with `context_descriptor(AR) := { model_artifact_digest ; inference_spec_digest ;
preprocessing_digest }` read from `AR.policy_document.payload`.

#### 3.2.2 Two entry points, `validate_campaign` once

**`validate_campaign : trusted_inputs → validation_result`** is pure —
`parse_commitment` + Ed25519 auth + manifest/ledger/record binding, in a frozen
first-failure precedence, **charging `vcfg.fuel_schedule` before each phase's
work** (`VERDICT_SEMANTICS.md` §5). No runner call.

    validation_result :=
      | `Invalid        of { reason : integrity_reason ; fuel : fuel_ledger ; evidence : commitment_evidence }
      | `FuelObstructed of { fuel : fuel_ledger ; evidence : commitment_evidence }
      | `Valid          of { campaign : authenticated_campaign ; fuel : fuel_ledger }

`` `FuelObstructed `` is a **totality case** — a loaded `verifier_config` requires
`max_fuel ≥ validation_fuel_ok` (`AUDIT_POLICY_AND_EVIDENCE.md` §2.3), so
`validate_campaign` never actually returns it.

**`assess_validated : trusted_inputs → validation_result → transcript_source →
assessment_outcome`** is the pure core. It **re-uses the given `validation_result`
— it never calls `validate_campaign` again.** `assessment_outcome` carries a
`certificate` in **every** obstruction *and* success constructor
(`Inadmissible | Exact | Obstructed of certificate`, `Underdetermined of
campaign_report`). Two entry points build the `transcript_source`:

- **Live** (`AUDIT_POLICY_AND_EVIDENCE.md` §2.4 step 7): `vr := validate_campaign ti`
  (once); on `` `Valid {campaign = ac ; fuel = L0}``,
  `co := capture ac … L0` (§3.2.3); `assess_validated ti vr
  (` `LiveTranscript { transcript = co.transcript ; ctx_bundle = co.ctx_bundle }``)`.
- **Offline replay** (`AUDIT_POLICY_AND_EVIDENCE.md` §9): `vr := validate_campaign ti`
  (once); `cb :=` reconstruct the `context_bundle` from the shipped artifact bytes;
  `pr := parse_transcript vcfg <retained wire bytes>` (§3.2.4); `assess_validated
  ti vr (` `OfflineParse { result = pr ; ctx_bundle = cb }``)`.

`assess_validated`'s precedence: `` `Invalid `` **>** `` `FuelObstructed `` (dead)
**>** a `` `Malformed `` transcript **>** the `replay`/`decide` verdict.

    exec_outcome  := `Ok of Vec Z (n_obs P) | `Failed of exec_fail_reason | `Exhausted
    call_key      := { phase : `ContextProbe | `Stage2 of nat ; role : `Probe | `X | `Y ; repeat : nat }
    call_request  := { key : call_key ; input : Vec Z (n_pre P) }
    exec_event    := { key : call_key ; input : Vec Z (n_pre P) ; outcome : exec_outcome }
    exec_transcript := exec_event list

    runner : environment → call_request → exec_outcome                (* F.3 — effectful, fallible *)

The capture wrapper builds each event `{ key = req.key ; input = req.input ;
outcome = runner env req }`, so `e.key` / `e.input` **equal the request by
construction** — the runner picks neither.

**Runner faithfulness** is a named F.3 assumption **never discharged**:

    faithful_transcript (tr) (ctx : AuditContext P) : Prop
      :=  ∀ e ∈ tr, ∀ v, e.outcome = `Ok v  →  v = model ctx e.input

O4 = **repeatability only** (a repeatably-wrong runner passes O4). O6 =
**input-correctness and success** (`e.input = preproc ctx x/y`, `outcome = ` `Ok ``).
`ObservationBinding(ctx, x, o_x)` follows **conditionally** from O6 plus the
assumed `faithful_transcript tr ctx`. Listed on every `INADMISSIBLE` certificate,
which binds the transcript by `transcript_evidence` (`VERDICT_SEMANTICS.md` §9).

#### 3.2.3 The loaded context, the gated capture, and the fuel model

Context resolution begins with one F.3 fetch:

    loaded_context := { descriptor : context_descriptor ; model_bytes ; preproc_spec_bytes ;
                        inference_spec_bytes : bytes ; ctx : AuditContext P }
    load_context : environment → context_descriptor → [ `Unavailable of ctx_reason | `Loaded of loaded_context ]
    context_bundle := CtxNotNeeded | CtxUnavailable of ctx_reason | CtxLoaded of loaded_context

`load_context` is the **only** effectful context step; its result is captured into
a `context_bundle` and threaded, as data, through `capture` / `replay` /
`assess_validated`. `preflight_O1_O2 : loaded_context → …` (O1/O2 = digest
comparisons of `lc.*_bytes` against `lc.descriptor` — pure) and `eval_O3 :
loaded_context → exec_event → Policy → [ `Fail … | `Ok resolved_context ]`
(checkpoint shape from `lc.inference_spec_bytes`; probe event `input = probe_input`
∧ `outcome = ` `Ok probe_observation ``; on `` `Ok `` yields
`resolved_context := { policy = P ; ctx = lc.ctx ; descriptor = lc.descriptor }`)
are the pure helpers shared by `capture` and `replay`.

Fuel is a **deterministic constant model** computable before any call:
`model_call_fuel` (fixed MLP shape; `inference_spec_digest`;
`AUDIT_POLICY_AND_EVIDENCE.md` §2.5.3); `vcfg.fuel_schedule` the
parse/auth/preflight/stage-1 constants. `charge : fuel_ledger → nat → [ `Ok |
`Over ]` is total and applied **before** each unit of work.

`capture` (`VERDICT_SEMANTICS.md` §6.4) is a staged pipeline: candidate-count
check first (no work); for each submission **charge `cost_stage1` then run
`stage1_check`** — **a stage-1 `charge` `` `Over `` is a terminal return** (`clo =
CampaignFuelExhausted`, no context, no further calls); then `load_context`; then
**charge `preflight_fuel` then run `preflight_O1_O2`**; then **charge
`model_call_fuel` then issue the probe**; then per pending candidate **charge
`cost_candidate` then issue its four calls**. Each gate opens only on the previous
one's success. `replay` (`VERDICT_SEMANTICS.md` §6.5) performs the **identical**
`charge`/gate sequence over the same `context_bundle`, reading `tr`.

    context_state :=                                   (* ONE flat sum — no nesting *)
      | NoContextNeeded
      | ContextUnresolved of { reason : ctx_reason ; findings : finding list }
      | ContextResolved   of { context : resolved_context ; findings : finding list }

`resolved_of : context_state → option resolved_context` is total.

The `` `NotRun `` theorem is scoped (`VERDICT_SEMANTICS.md` §6.6): `(CAP1)` holds
only for a certificate whose `transcript_evidence = LiveCapture` (an **unmodified
`capture` output**) — a `` `NotRun `` slot ⟺ `capture` issued no `call_request` for
that candidate, and `rr.clo = co.clo`; `(REP1)` holds for **every** certificate —
a `` `NotRun `` slot means the verified schedule does not authorise or evaluate
that candidate, and a witness never comes from a `` `NotRun `` slot.

#### 3.2.4 Stage inputs, and `parse_transcript` (offline)

- `load_policy` — `policy_document`;
- `validate_campaign` — `trusted_inputs` (no transcript, no runner);
- **stage-1 checks** — `verifier_config` + `policy_document` + `Policy` +
  `submission_index` + the raw `candidate_submission`;
- `preflight_O1_O2` — `loaded_context`;
- `eval_O3` — `loaded_context` + the probe `exec_event` + `Policy`;
- **stage-2 checks** — `resolved_context` + `verifier_config` + `exec_transcript`
  + the `pending_submission`.

Offline replay only:

    parse_result   := `Malformed  of { reason : string ; wire_digest : digest }
                     | `Wellformed of { transcript : exec_transcript ; wire_digest : digest }
    parse_transcript : verifier_config → bytes → parse_result

`wire_digest := digest_bytes_v1("pcfw.exec_transcript_wire.v1", <raw bytes>)` is
set on **both** branches. `` `Malformed `` if `|bytes| >
vcfg.bundle_limits.max_transcript_bytes`, or any wire event has a wrong-length
`input` / `` `Ok `` vector or an unrecognised outcome tag, or the wire structure
is not a list of events. Otherwise `` `Wellformed ``, every `exec_event` well-formed
by construction. The live pipeline never parses — `capture` yields a typed
`exec_transcript` directly, tagged `LiveCapture`.

    lookup_unique tr k := match [ e ∈ tr | e.key = k ] with     (* raw key matches counted FIRST *)
                          | [e] when event_schema_valid(e) → Some e
                          | _ → None                             (* 1 valid + 1 duplicate ⇒ None *)

C1/C2/C3/C5 are decided **before** context resolution; a stage-2 candidate call is
issued **only after `ContextResolved`**; O6 precedes O4 (`VERDICT_SEMANTICS.md`
§4–§6).

## 4. The factorisation question

For an observation function `g : Vec Z n_in → Vec Z n_obs`, define fibre constancy
relative to `g` (this needs only `P`):

    FibreConstantObs(P, g) :=
      ∀ u v, D_P u → D_P v → Q_P (g u) = Q_P (g v) → Φ_P u = Φ_P v.

For a context `C`:

    FibreConstant(C) := FibreConstantObs(policy C, fun x => model C (preproc C x)).

### 4.1 "Factors through" is defined by stipulation

**In version 0, "`Φ_P` factors through `M̃_C` on `D_P`" is *defined* to mean
`FibreConstant(C)`.** No stronger characterisation is claimed. In particular:

- v0 does **not** claim that `FibreConstant(C)` is equivalent to the existence of
  a total decoder `Φ̂ : Vec Z n_obs → bool` with `Φ_P x = Φ̂ (M̃_C x)` on `D_P`.
  That equivalence is false without extra assumptions (a finite or enumerable
  `D_P`, decidable membership in `Im(M̃_C|_{D_P})`, a computable section, or a
  choice principle).
- If a decoder is ever wanted it is defined first on the image subtype
  `Φ̂ : Im(M̃_C|_{D_P}) → bool`, and extended only under an explicit stated
  assumption. v0 asserts **neither** the existence **nor** the non-existence of a
  total `Φ̂`.

(The original specification §3 stated a decoder equation and an equivalence; that
is superseded — `PHASE_0_SPECIFICATION_AMENDMENTS.md` D6.)

## 5. Witness predicates — three levels

### 5.1 `CheckedWitness` — the kernel predicate (policy only, over supplied observations)

    CheckedWitness(P, x, y, o_x, o_y) :=
        D_P x
      ∧ D_P y
      ∧ x ≠ y
      ∧ Q_P o_x = Q_P o_y                (decidable equality on Vec Z n_obs)
      ∧ Φ_P x ≠ Φ_P y

`x, y : Vec Z n_in`; `o_x, o_y : Vec Z n_obs` are values **supplied to** the
kernel. `CheckedWitness` is parameterised by `P` only — no context, no model, no
preprocessing.

### 5.2 `ObservationBinding` — the system-binding premise (context)

    ObservationBinding(C, x, o) := model C (preproc C x) = o

Derived **conditionally** for a witness's `x`, `y`: O6 gives an event with
`input = preproc C x` and `outcome = ` `Ok o``; the **assumed**
`faithful_transcript tr C` (F.3, §3.2.2) then gives `o = model C (preproc C x)`.
O4 is a guard on non-repeatable unfaithfulness, not part of the derivation. Not a
kernel term (`TRUST_BOUNDARY.md` §F.3.1, `AUDIT_POLICY_AND_EVIDENCE.md` §6 tier O).

### 5.3 `ValidWitness` — the verifier's composite (context)

    ValidWitness(C, x, y) := ∃ o_x o_y,
        CheckedWitness(policy C, x, y, o_x, o_y)
      ∧ ObservationBinding(C, x, o_x)
      ∧ ObservationBinding(C, y, o_y)

## 6. Claims

### 6.1 Kernel-level theorem `(T1)` — pure, policy only

    (T1)  CheckedWitness(P, x, y, o_x, o_y) →
          ∀ g : Vec Z n_in → Vec Z n_obs,
            g x = o_x → g y = o_y → ¬ FibreConstantObs(P, g)

Proof: assume `FibreConstantObs(P, g)`; instantiate at `u := x`, `v := y`;
`g x = o_x`, `g y = o_y` give `Q_P (g x) = Q_P o_x = Q_P o_y = Q_P (g y)`, so
`Φ_P x = Φ_P y`, contradicting `Φ_P x ≠ Φ_P y`. ∎

`(T1)` mentions no context, model, or execution.

### 6.2 System-level corollary `(A1)` — adds the binding premises (context)

    (A1)  CheckedWitness(policy C, x, y, o_x, o_y)
        → ObservationBinding(C, x, o_x)
        → ObservationBinding(C, y, o_y)
        → ¬ FibreConstant(C)

Derivation: instantiate `(T1)`'s `g` with `fun x => model C (preproc C x)`; the
two `ObservationBinding` premises supply `g x = o_x`, `g y = o_y`; conclude
`¬ FibreConstantObs(policy C, …)`, which is `¬ FibreConstant(C)`.

`(A1)` is what an `INADMISSIBLE` verdict warrants, conditional on the
`ObservationBinding` premises — which, operationally, means conditional on O6
(event input = `preproc C x/y`, outcome `` `Ok ``) **and** the assumed
`faithful_transcript tr C` (system-binding, `TRUST_BOUNDARY.md` §F.3). O4/O6
passing does not *establish* `faithful_transcript`; it is a listed assumption.

### 6.3 Verdict-function soundness `(T2)` — verified orchestration, not kernel

Scoped to `validate_campaign` (`VERDICT_SEMANTICS.md` §5–§6). Let
`V := validate_campaign ti` (computed **once** per pipeline), `src` a
`transcript_source` carrying `(cb, tr)`, and, when
`V = ` `Valid {campaign = ac ; fuel = L0}``,
`R := replay ac cb ti.vcfg ti.AR.policy_document ti.AR.policy L0 tr`.
`assess_validated` re-uses the given `V` — it does **not** re-run
`validate_campaign`:

    (T2)  verdict_of (assess_validated ti V src) = INADMISSIBLE
          ⟺  (∃ ac L0, V = `Valid {campaign = ac ; fuel = L0})
              ∧ (∃ {_, `Done s} ∈ R.stage2, ∃ wd, s.verdict = `ValidWitness wd)

    (T2-sound)     INADMISSIBLE ⟹ that right-hand side
    (T2-complete)  that right-hand side ⟹ INADMISSIBLE

`(T2-sound)` plus `(A1)` — where `rc.ctx = r.context.ctx = cb.lc.ctx` for
`R.context = ContextResolved r`, O6 for the witness's `x`, `y`, and the two F.3
assumptions `faithful_transcript tr rc.ctx` and `loaded_context` well-formedness —
gives `¬ FibreConstant(rc.ctx)`. A `` `Done `` stage-2 `` `ValidWitness `` slot
exists only for a candidate whose gate opened after `ContextResolved` (`(REP1)`,
`VERDICT_SEMANTICS.md` §6.6); a witness under an `` `Invalid `` /
`` `FuelObstructed `` campaign, a `` `Malformed `` transcript, or a `` `NotRun ``
slot returns `OBSTRUCTED`. `(REP1)` holds for every certificate; `(CAP1)` holds
only when `transcript_evidence = LiveCapture`. `(T2)` is checked against the
verdict logic (`VERDICT_SEMANTICS.md` §7), not proved in the kernel.

### 6.4 `EXACT` soundness contract `(E1)` — context

    (E1)  valid_completeness_certificate(C, c)  →  FibreConstant(C)

v0 defines the type `completeness_certificate` and states `(E1)` as the obligation
any future producer must meet. No producer is implemented; the campaign never
emits `EXACT` (`VERDICT_SEMANTICS.md` §6.6, §6.7 — provably dead code).

### 6.5 Constructive asymmetry (governing rule)

    ValidWitness(C, x, y)                     ⟹  ¬FibreConstant(C)   (via (A1))
    no witness found by heuristic search      ⇏   FibreConstant(C)

## 7. Numerical semantics

### 7.1 Representation

Mathematical integers (`Z`) throughout; wire form is decimal integers with
declared component counts and shapes in declared row-major order. The kernel's `Z`
extracts to a `zarith`-backed big integer (`TRUST_BOUNDARY.md` §F.1.1).

### 7.2 `rounddiv` — fully defined

For `a : Z`, `w : Z` with `w > 0`, let `q₀`, `r` be the Euclidean quotient and
remainder: the unique pair with `a = q₀·w + r`, `0 ≤ r < w`.

| mode | `rounddiv(a, w, mode)` |
|---|---|
| `Floor` | `q₀` |
| `Ceil` | `q₀` if `r = 0`, else `q₀ + 1` |
| `TowardZero` | `q₀` if `a ≥ 0`; if `a < 0` then `q₀` if `r = 0` else `q₀ + 1` |
| `HalfEven` | compare `2·r` to `w`: `q₀` if `2r < w`; `q₀ + 1` if `2r > w`; if `2r = w` then `q₀` when `q₀` is even, else `q₀ + 1` |

Total for every `a : Z` and `w : Z, w > 0`. `w ≤ 0` is a malformed policy (§7.4).

### 7.3 Two rounding roles

- **Model rescale**, per layer `k`:
  `z^{(k+1)} = ReLU(rounddivᵥ(W^{(k)} · z^{(k)} + b^{(k)}, s_k, rescale_rounding_mode))`,
  with `W^{(k)} : Mat Z rows_k cols_k`, `z^{(k)} : Vec Z cols_k`,
  `b^{(k)} : Vec Z rows_k`, `s_k : Z, s_k > 0`, `ReLU(t) = max(0, t)`
  component-wise, `rounddivᵥ` = component-wise `rounddiv`. `W^{(k)} · z^{(k)}` is
  the exact integer matrix–vector product. `rescale_rounding_mode` is content of
  the **inference specification**, not a standalone policy field
  (`AUDIT_POLICY_AND_EVIDENCE.md` §2).
- **Observation quantisation**: `Q_P` uses `quantisation_rounding_mode`, a policy
  field.

### 7.4 Shape and validity

- `cols_k = length(z^{(k)})`; `rows_k = length(b^{(k)}) = length(z^{(k+1)})`; the
  observable checkpoint has type `Vec Z n_obs`. All are type-level in `Mat`/`Vec`.
- `Q_P`'s bin-width vector has type `Vec Z n_obs` (or a scalar with a uniform
  flag).
- A width `w_i ≤ 0`, a scale `s_k ≤ 0`, an inference-specification shape
  disagreement, or `representation_id` naming no checkpoint is a **malformed
  policy / malformed artifact**: the policy or artifact does not load and no
  assessment runs (authority-side; `AUDIT_POLICY_AND_EVIDENCE.md` §2.3).

### 7.5 Prohibited in the kernel

Host-language float comparison; float32/float64 conversion; NaN or infinity;
associative float rearrangement; a metric selected by an unconstrained string;
silent dimension truncation or broadcasting; integer overflow or wrapping.

## 8. The target predicate registry

`Φ_P` is one constructor of a closed, versioned registry of Rocq-defined decidable
Boolean functions on `Vec Z n_in`:

    predicate_id := SyntheticTargetV0 | ...

`P` names an authorised constructor and binds its version or digest. The kernel
computes `Φ_P x` and `Φ_P y` directly, so target divergence is a kernel result.
Whether the chosen predicate is *appropriate* is a specification-and-authority
assumption (`TRUST_BOUNDARY.md` §F.2).

## 9. When the term "fibre" is permitted

"Fibre witness" is used **only** because `Q_P` is a fixed quantisation map and
observations are compared by exact equality after quantisation, so `M̃_C`
partitions `D_P` into genuine fibres. A distance-threshold relation would instead
give an **observational-confusability witness**; v0 uses exact quantised equality
and the term stands.

## 10. Certificate

A **certificate** is the verifier-produced result for an assessment verdict
(`INADMISSIBLE`, `EXACT`, `OBSTRUCTED`). `build_certificate : cert_body_input →
trusted_inputs → replay_input → transcript_evidence → commitment_evidence →
certificate` assembles it — `replay_input` is `` `InvalidFuel fuel_ledger `` on an
obstruction branch and `` `ReplayDone replay_result `` on the replay branch; no
model re-run. Its verdict is `verdict(cert.body)`, not a stored field
(`VERDICT_SEMANTICS.md` §9). It binds: `policy_digest`; `context_digests`;
`commitment_evidence` — `UnparsedCommitment ti.MCW` (`BadCommitmentEncoding`),
`ParsedCommitment mc.digest` (`SignerNotAuthorised` / `SignatureInvalid`), else
`AuthenticatedCommitment mc.digest`; `transcript_evidence` — `NoTranscript` (a
validation obstruction), `MalformedTranscript {reason ; wire_digest}` (offline
parse failure), `LiveCapture {transcript_digest}` (an unmodified `capture` output;
`(CAP1)` applies), or `OfflineTranscript {transcript_digest ; wire_digest}` (a
retained transcript re-checked; `(REP1)` only); `verifier_config_digest`;
`fuel_model_digest` and the `fuel_ledger` (`vr.fuel` on an obstruction branch,
`rr.fuel` on the replay branch); for `INADMISSIBLE` the complete `witness_data`
plus `all_findings`; the verifier and extracted-kernel digests; the Rocq commit;
the extraction-assumptions list; the compiled-execution-chain descriptor;
`configured_limits` / `fired_limits` (closed `limit_id` set, ascending; `[]` if
none); the assumption list — including **`faithful_transcript`** and the
**`loaded_context` well-formedness** for `INADMISSIBLE`. The `loaded_context`
bytes are bound transitively through `context_digests` (O1/O2 check them).

`REJECTED_BUNDLE` → `rejection_report`; `UNDERDETERMINED` → `campaign_report`
(`VERDICT_SEMANTICS.md` §9 — concrete records). Neither is a certificate.

## 11. Proof decomposition (for the Rocq development)

1. domain-membership soundness — `D_P` decidable, box semantics on `Vec Z n_in`;
2. quantisation soundness — `Q_P` total, deterministic, `rounddiv` correct per §7.2;
3. operational-observation equality — decidable equality on `Vec Z n_obs`;
4. target-divergence soundness — registry predicate decidable;
5. `CheckedWitness`-implies-non-factorisation — `(T1)` (policy only);
6. corollary `(A1)` — instantiation with the context observation function;
7. verdict-function soundness — `(T2)`, verified orchestration;
8. system-binding assumptions — context well-formedness, `ObservationBinding`;
9. `EXACT` contract — `(E1)`, type and obligation only.

Items 1–5 are the kernel (parameterised by `P`). Item 6 is a one-line corollary
(parameterised by `C`). Item 7 is verified orchestration. Items 8–9 are the
assurance boundary.
