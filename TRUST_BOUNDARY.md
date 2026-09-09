# Trust Boundary

**Deliverable:** Phase 0, Unit 0C
**Status:** Draft for Unit 0G ratification. **Revision 14** — `load_context` (one
F.3 fetch) produces the immutable `loaded_context` threaded through capture /
replay; `preflight_O1_O2 lc` / `eval_O3 lc` and `resolved_context` are
constructible from it. Stage-1 fuel `` `Over `` is a terminal return.
`transcript_evidence` distinguishes `LiveCapture` (`(CAP1)`) from
`OfflineTranscript` (`(REP1)` only). `validate_campaign` once per pipeline;
charge-before-work; `faithful_transcript` never discharged.
**Normative.**

---

## 1. What the boundary is for

The generator may search, optimise, and propose freely, because it is outside the
trusted computing base. The verifier may only check. A certificate is meaningful
only relative to the components trusted to produce it, named at the right level.

## 2. The four categories

### F.1 Logical trusted computing base

Trusted to make the kernel theorem `(T1)` and the quantisation / box-membership /
decidable-equality lemmas mechanically sound:

- the Rocq/Coq kernel and accepted foundational libraries;
- the extraction mechanism and its declared extraction assumptions;
- the extracted checking kernel, as an OCaml term;
- required OCaml runtime behaviour relied on by the extracted code.

`(T2)` (verdict-function soundness) is **verified orchestration**, checked
separately; §6.

#### F.1.1 Compiled execution chain (not covered by extraction)

Rocq extraction produces an OCaml term; it does not establish that the compiled
binary implements it. A compiled checker additionally depends on: the OCaml
compiler and linker; the `zarith` implementation and its C bindings; the platform
C runtime; the build configuration and flags; executable packaging.

**Validation strategy (assurance argument, not proof):** reproducible builds
(pinned compiler and library versions, recorded flags, byte-identical rebuild)
plus differential testing of the compiled checker against an independent reference
on a fixture battery. Named in the certificate's assumption section.

The extraction realisation files (`ExtrOcamlBasic`, `ExtrOcamlZBigInt`,
`ExtrOcamlNatBigInt`) are itemised as part of the extraction TCB; `Z` / `positive`
/ `nat` extract to a `zarith`-backed big-integer representation with no runtime
conversion.

### F.2 Specification and authority assumptions

- the formal definitions (`X_raw` = `Vec Z n_in`, `X_model`, `N_P`, `M_A`, `Q_P`,
  `Φ_P`, `D_P`, `AuditContext`, `FibreConstant`, `CheckedWitness`) capture the
  intended notions;
- the audit policy expresses the question the audit authority intended;
- the selected registry predicate is appropriate to that question;
- the selected quantisation has operational meaning.

A policy may be authoritative without being scientifically or ethically correct.
Formal verification cannot close this gap; the certificate makes it visible.

### F.3 System-binding trusted computing base

Tested and reviewed, **not proved**. Each contributes a named residual-risk line
to the certificate.

- the model loader; the **policy loader** that constructs the formal
  `semantic_policy : Policy` from `policy_document.payload`
  (`CLAIM_AND_DEFINITIONS.md` §3.2);
- **`load_context`** — the one F.3 fetch (per assessment) that retrieves the
  model / preprocessing-spec / inference-spec bytes and builds the immutable
  `loaded_context` (`CLAIM_AND_DEFINITIONS.md` §3.2.3). Its residual assumption:
  `loaded_context.ctx` (the pure `preproc` / `model`) **faithfully realises the
  committed `*_spec` bytes**. The bytes are bound by `context_digests` (which O1/O2
  recompute and check). Threaded, as data, through `capture` / `replay` /
  `assess_validated`;
- the artifact-hashing, `canonicalise_v1`, `digest_v1`, and `digest_bytes_v1`
  implementations;
- **the JSON parser, the schema validator, and the canonicalisation layer** —
  `parse_candidate` and `to_cv` — that validate raw bytes, construct the
  `parsed_candidate` and the `Vec Z n_in` / `Vec Z n_obs` values, and produce the
  byte input to the `policy_hash` comparison;
- **the candidate-ingestion mechanism and the append-only campaign ledger**: each
  submitted `candidate_submission` (raw bytes) is appended, in order, to a ledger
  opened before the search (`AUDIT_POLICY_AND_EVIDENCE.md` §2.4 step 4) and
  committed at campaign close as the `campaign_manifest M`, whose digest is signed
  and published as `manifest_commitment_wire MCW` (§2.4 step 6, §2.4.1).
  **`validate_campaign` runs once per pipeline — before any model call** — over a
  typed `integrity_reason` sum with a frozen first-failure precedence, **charging
  each `fuel_schedule` phase before its work** (`VERDICT_SEMANTICS.md` §5); the
  pure core `assess_validated` re-uses its result and **never re-validates**. Two
  entry points share `assess_validated`: **live** (validate → gated capture →
  assess) and **offline replay** (validate → `parse_transcript` → assess);
- **the manifest-signing key and the immutable commitment record**: the audit
  authority's Ed25519 release key that signs `utf8(mc.digest)`, and the project's
  signed-tag history. The **`verifier_config.trust_anchor`** —
  `authorised_signers` (no repeat) and their 64-hex public keys (exactly one per
  signer) — is a **trusted input** bound by `verifier_config_digest`;
- the **`runner`** (`runner : environment → call_request → exec_outcome`) and the
  **gated capture** (`VERDICT_SEMANTICS.md` §6.4): candidate-count check first; for
  each submission *charge `cost_stage1` then run `stage1_check`* (**a stage-1
  `charge` `` `Over `` is a terminal return** — the context is never reached); then
  `load_context`; *charge `preflight_fuel` then run `preflight_O1_O2 lc`*; *charge
  `model_call_fuel` then issue the probe*; per pending candidate *charge
  `cost_candidate` then issue its four calls* — each gate opening only on the
  previous one's success. The wrapper builds each `exec_event` from its
  `call_request`, so `e.key`/`e.input` equal it by construction. `replay` walks the
  same staged `charge`/gate sequence over the same `context_bundle`. The
  `` `NotRun `` theorem is scoped: `(CAP1)` holds only for a certificate whose
  `transcript_evidence = LiveCapture` (an unmodified `capture` output) — a
  `` `NotRun `` slot ⟺ no `call_request` was issued, `rr.clo = co.clo`; `(REP1)`
  holds for **every** certificate — a `` `NotRun `` slot means the verified
  schedule does not authorise that candidate. The residual assumption
  **`faithful_transcript tr ctx`** is **never discharged**: O4 is *repeatability
  only*; O6 is *input-correctness and success* (`e.input = preproc ctx x/y`,
  `outcome = ` `Ok ``); `ObservationBinding` follows *conditionally* from O6 plus
  the assumption. Listed on every `INADMISSIBLE` certificate, which binds the
  transcript by `transcript_evidence`;
- the **deterministic fuel model** (`model_call_fuel` from the inference spec +
  `verifier_config.fuel_schedule`, `AUDIT_POLICY_AND_EVIDENCE.md` §7.2): every cost
  is a constant or a function of committed data, and every `charge` **precedes**
  the work it pays for. The wall-clock/memory watchdog is a weaker guard that can
  only add a `` `Failed ``/`` `Exhausted `` event to `tr`;
- **`parse_transcript`** (offline): bounded by `bundle_limits.max_transcript_bytes`;
  a `` `Malformed `` result carries a `wire_digest` over the raw bytes, bound into
  the obstruction certificate as `MalformedTranscript`;
- the value-passing interface between the host side and the kernel.

The **target evaluator is not here** — `Φ_P` is evaluated in-kernel from the
registry predicate on the raw parsed input (`CLAIM_AND_DEFINITIONS.md` §8).

#### F.3.1 Context resolution and the `ObservationBinding` obligation

Context resolution runs **once**, only if a submission survived stage 1 as
`` `Pending ``. It begins with `load_context` (F.3 fetch → `loaded_context lc`;
`` `Unavailable rn `` means **no probe, no candidate calls**), then two pure
helpers shared by capture and replay: `preflight_O1_O2 lc` (O1/O2 = digest
comparisons of `lc.*_bytes` against `lc.descriptor` — no runner call; a `` `Fail ``
means **the probe is never issued**) and `eval_O3 lc` (the probe event's
`input = probe_input`, `outcome = ` `Ok probe_observation ``, and the checkpoint
shape/type from `lc.inference_spec_bytes`; `AUDIT_POLICY_AND_EVIDENCE.md` §2.5.2; a
`` `Fail `` means **no candidate call is ever issued**). On `` `Ok ``,
`resolved_context := { policy = P ; ctx = lc.ctx ; descriptor = lc.descriptor }`.
Any failure → `ContextUnresolved`, no `resolved_context`, `OBSTRUCTED`,
`clo = ContextObstruction reason`, O1–O3 findings into `context_findings`, every
pending stage-2 slot `` `NotRun ``.

Per `` `Pending `` candidate, stage 2 reads the four transcript events via
`lookup_unique`: **O6** (all four `` `Some ``; each `e.input` equals the
kernel-computed `preproc ctx x` / `preproc ctx y` — `ExecInputMismatch`; none
`` `Failed ``/`` `Exhausted ``; per-candidate fuel cap), then **O4**
(repeatability — the two `X` values agree, the two `Y` values agree), then **O5**
(range). On O6/O4/O5 success, O6's input-correctness plus the assumed
`faithful_transcript tr ctx` give
`ObservationBinding(ctx, x, o_x) := model ctx (preproc ctx x) = o_x` — O4 is a
guard, not part of this derivation; a
failure is that candidate's `WITNESS_CHECK_OBSTRUCTED`
(`AUDIT_POLICY_AND_EVIDENCE.md` §6, `VERDICT_SEMANTICS.md` §4.2).

#### F.3.2 Future hardening — a proof-checked raw-byte boundary

A later version MAY move the parser, schema validator, and canonicaliser out of
the TCB by having the kernel re-derive, from the raw canonical wire bytes, both
the `Vec`/`Mat` values it uses and the policy digest it compares — so that a
parser defect cannot change a verdict without also failing an in-kernel
re-derivation check. Version 0 does **not** do this.

### F.4 Untrusted environment

- the witness generator;
- candidate claims and diagnostic hints;
- search metadata;
- the campaign record's `recorded_results` and `resource_budget` (advisory —
  cross-checked against the replay and against `verifier_config`, never
  load-bearing; the *identity/manifest* fields of `rec` are fail-closed but never
  authoritative; `VERDICT_SEMANTICS.md` §6.3–§6.4, `THREAT_MODEL.md` T26);
- the transport channel;
- any user interface or dashboard;
- external bulk storage (the *content* of stored submissions and artefacts is
  checked by digest against the committed manifest / policy; the storage medium
  itself is untrusted).

Plus the security-critical host components that must **fail closed** and that do
**not** determine semantic values or policy bindings: the CLI; the filesystem
layer. The fuel meter (`AUDIT_POLICY_AND_EVIDENCE.md` §7.2) is **in F.3**, not here
— it is deterministic and its outputs (`fired_limits`, `` `NotRun `` slots, the
discard rule) are verdict-affecting fail-closed. The wall-clock/memory watchdog is
also F.3 but strictly weaker: it can only add a `` `Failed ``/`` `Exhausted ``
event to the transcript. A fail-open defect in a genuine F.4 component can deny
service or let through an oversized bundle, but cannot by itself produce a wrong
verdict on a fixed transcript.

## 3. Bindings

### 3.1 Model-execution binding

See §F.3.1. Residual assumptions: `preproc C`, `model C`, and the model loader
faithfully realise the committed artifact and inference specification;
**`faithful_transcript tr C`** — every `` `Ok v `` event has `v = model C e.input`
— which is **never discharged** by the checks (O4 is repeatability only, O6 is
input-correctness + success; `ObservationBinding` is conditional on it, for a
witness's `x`, `y`).

### 3.2 Target-evaluation binding

`Φ_P x`, `Φ_P y` are computed by the kernel from the registry predicate bound by
the policy, on the raw parsed inputs. No external target authority in v0. Residual
assumption (F.2): the chosen registry predicate is the right question.

### 3.3 Policy binding

The candidate carries only `policy_hash`; the verifier compares it against
`digest_v1("pcfw.policy_payload.v1", to_cv(policy_payload))` (`AUDIT_POLICY_AND_EVIDENCE.md` §2.2). The
parser/canonicaliser producing those bytes is in F.3.

## 4. Actors versus authority to act

- The **audit authority** declares the policy document and is responsible for its
  well-formedness (`AUDIT_POLICY_AND_EVIDENCE.md` §2.3).
- The **candidate generator** searches; it cannot determine the verdict, alter the
  policy, authorise its own tolerance, certify its own model outputs, or convert a
  null search result into an exactness claim.
- The **verifier** checks and issues certificates. It has **no authority** to
  modify, disable, or gate the audited system.
- The **relying party** decides what a certificate does. Epistemic assessment and
  authority to act are separate; a control policy, if any, is a distinct layer.

## 5. Prior-work note

PCOA's `AdmissibilityGate` is **not** used and is **not** merely renamed: its
`GatedInadmissible` constructor denotes protocol rejection, which this project
calls `REJECTED_BUNDLE`, whereas this project's `INADMISSIBLE` is a positive
assessment verdict. The result types are defined from first principles
(`VERDICT_SEMANTICS.md`). No trust-boundary text is copied from PCE or PCSE.

## 6. Kernel versus verified orchestration

- **Kernel (F.1):** `(T1)` and the quantisation / box-membership / decidable-
  equality lemmas — pure statements about supplied data, parameterised by `P`.
- **Verified orchestration:** `(A1)` and `(T2)`, scoped to `validate_campaign`,
  over the pure total `assess_validated` / `replay`, `src` a `transcript_source`
  carrying `(cb, tr)` (`VERDICT_SEMANTICS.md` §5–§7); `V := validate_campaign ti` (once per
  pipeline), `R := replay ac cb ti.vcfg ti.AR.policy_document ti.AR.policy L0 tr` for
  `V = ` `Valid {campaign = ac ; fuel = L0}``:

      (T2)  verdict_of (assess_validated ti V src) = INADMISSIBLE
            ⟺  (∃ ac L0, V = `Valid {campaign = ac ; fuel = L0})
                ∧ (∃ {_, `Done s} ∈ R.stage2, ∃ wd, s.verdict = `ValidWitness wd)

  with the `(T2-sound)` / `(T2-complete)` split; `assess_validated` re-uses the
  **given** `V` (no re-validation) and evaluates `R` once. Reproduced identically
  in `CLAIM_AND_DEFINITIONS.md` §6.3, `PROJECT_CHARTER.md` §4.3, `NON_CLAIMS.md`
  #14, `VERDICT_SEMANTICS.md` §7. Checked against the verdict logic, not proved in
  the kernel; campaign-level.
