# Phase 1 -- concrete `op_completeness_wellformed` (VERDICT_SEMANTICS 5 step 9)

Date: 2026-09-13 (revision 1 HELD; revision 2 HELD -- blocker 1 closed,
blocker 2 persisted; this is **revision 3**)
Baseline: `PHASE_1_RECORD_CROSSCHECK.md` (r17, reviewer-concurred and promoted).
One new module, `implementation/rocq/CompletenessWellformed.v` (`Qed`,
axiom-free); a small addition to `ValidationBinding.v`
(`validate_campaign_valid_completeness`) and `ManifestPipeline.v` (wiring +
theorems). No change to `Orchestration.v`, `RecordCrosscheck.v`, or any other
promoted unit.

Status: **reviewer-concurred by source inspection and promoted** (2026-09-13;
reviewed r3 ZIP sha256
`b4298a2c4f0bdecd7d601a71830bd2e1ecbf1d8cba567f85168f9ade7df3cae3`). Not a
Phase 1 closure.

The validation step being made concrete -- the LAST guard in
`validate_campaign`, reached only after steps 1-8 (parse, signer, signature,
policy/audit/context match, ledger, record identity) have all passed:

> step 9 -- `ti.rec.completeness = Complete c => c well-formed` -> else
> `CompletenessMalformed`.

## 0. Revision 1 HOLD and the two repairs

Revision 1 defined `wellformed_scheme` by reusing
`ManifestAuthentication.printable_ascii_id` and checked
`op_completeness_wellformed_impl` against the Orchestration field
`ti_completeness ti` directly. The reviewer HELD on two grounds:

1. **Invented grammar.** `printable_ascii_id` scopes a round-trip THEOREM
   about manifest identifiers (`manifest_roundtrip_wf`) -- it is never a
   decoder-level acceptance gate anywhere in this codebase -- and it rejected
   decoded strings (a quote, a backslash, a raw high byte) that
   `scheme:<string>` (AUDIT_POLICY 2.2.5) does not forbid. Reusing
   `CampaignRecord.skip_value` for `body` is legitimate (it is the project's
   existing, reviewer-accepted canonical-value recognizer), but the doc
   overclaimed it recognises "any canonical JSON value" when it in fact
   recognises the **ASCII-wire canonical subset** `CampaignRecord.v` /
   `ManifestAuthentication.v` already scope to throughout this codebase --
   raw non-ASCII UTF-8 is out of scope, same restriction, same rationale.
   `wellformed_body_true_iff` also only connected the Boolean to
   `skip_value`'s own behaviour, not to an independent specification-level
   relation.
2. **Unbound check.** The governing step reads `ti.rec.completeness`; the
   implementation checked the separate `ti_completeness ti` field with no
   decoder or premise connecting the two.

Repairs, in full below: (1) `wellformed_scheme` now requires only
non-emptiness; `wellformed_body`'s ASCII-wire-subset scope is stated honestly
and flagged as a decision pending reviewer approval (the reviewer's other
option -- a full §2.2 canonical-value / UTF-8-tolerant recognizer -- is a
substantially larger, separate decoder unit); an independent
`completeness_status_wf` relation is added, and the top-level theorem is
restated over it. (2) `ManifestPipeline.v` gains an explicit F.3 premise
`record_completeness_load_validated`, and a new theorem states the governing
obligation over `ti.rec.completeness` (via an abstract `record_completeness_of`
denotation, pending a concrete decoder) rather than `ti_completeness` alone.

Revision 2 fixed blocker 1 in full (reviewer CONCURRED: "no further UTF-8
decoder work is required for this unit") but re-introduced blocker 2 in an
UNSATISFIABLE form: `record_completeness_load_validated` was stated as a
blanket Section `Hypothesis`

    forall ti, record_completeness_of (ti_record ti) = ti_completeness ti

quantified over **every** `trusted_inputs`. Two `trusted_inputs` values can
share `ti_record` while differing in `ti_completeness` (e.g. `Unknown` vs
`Incomplete`), so this premise forces `CompletenessUnknown =
CompletenessIncomplete` -- inconsistent, exactly the defect once found in
`ManifestMatching.ti_policy_digest_truthful`. `Print Assumptions` "Closed
under the global context" cannot detect this: a Section `Hypothesis` becomes
an ordinary universally-quantified theorem parameter on section close, and the
theorems built from it remain individually well-typed and gap-free even though
the premise itself can never be satisfied by any real `ti`, `ti_record`,
`ti_completeness` triple with more than one possible completeness value per
record.

**Revision 3** repairs this: `record_completeness_load_validated` is now a
`Definition ... (ti : trusted_inputs) : Prop`, a predicate on ONE input --
exactly `ManifestMatching.policy_digest_load_validated ti`'s shape, not a
blanket Section `Hypothesis` -- and both theorems that depend on it take
`record_completeness_load_validated ti` as an explicit premise about the one
`ti` in play, not a global fact about every `trusted_inputs`. No other
substantive change; the mismatch-demonstration harness tests are unchanged
(they illustrate exactly why the per-input premise, not a global one, is
necessary).

## 1. Scope

`Orchestration.completeness_status := CompletenessUnknown | CompletenessIncomplete
| CompletenessComplete completeness_certificate` is already a typed value.
There is **no** wire-decoding step in this unit's checker: it is a pure
structural well-formedness predicate over an already-typed value. It is
**unrelated** to `Orchestration.valid_completeness_certificate_v0` -- the
*semantic* check `decide`'s `EXACT` branch uses (a completeness-scheme
REGISTRY lookup, empty in v0, hence always `false`, VERDICT_SEMANTICS.md 6.9).
That predicate, and `EXACT`'s dead-code status, are untouched. `op_transcript_digest`
is untouched and stays OPEN.

## 2. The checker

`completeness_certificate := { scheme : string ; body : string }`
(AUDIT_POLICY_AND_EVIDENCE.md 2.2.5: `{scheme:<string>, body:<the
canonical_value verbatim>}`).

```
wellformed_scheme (s : string) : bool := negb (String.eqb s "").

wellformed_body (s : string) : bool :=
  match CampaignRecord.skip_value (String.length s) s with
  | Some EmptyString => true
  | _ => false
  end.

wellformed_certificate (c : completeness_certificate) : bool :=
  wellformed_scheme (completeness_scheme c) && wellformed_body (completeness_body c).

op_completeness_wellformed_impl (cs : completeness_status) : bool :=
  match cs with
  | CompletenessUnknown | CompletenessIncomplete => true
  | CompletenessComplete c => wellformed_certificate c
  end.
```

`scheme:<string>` carries no further wire grammar: `wellformed_scheme` requires
only that the scheme actually names something (non-empty); a quote, a
backslash, or a raw high byte in the DECODED string are legitimate data,
**accepted**. `wellformed_body` requires `body` to be exactly one value of the
**ASCII-wire canonical subset** -- the same restriction `CampaignRecord.v`
applies to `completeness` / `recorded_results` / `resource_budget` and
`ManifestAuthentication.v` applies to every decoded string -- **not** the full
§2.2 canonical-value language (which permits raw UTF-8 string content). This
narrower v0 scope is flagged for reviewer approval; the alternative is a
UTF-8-tolerant canonical-value recognizer, a separate, larger decoder unit.

## 3. Independent (specification-level) well-formedness

Stated directly against the wire fields' own contract, **not** via this unit's
own Booleans, so the correspondence theorem is a genuine characterisation:

```
scheme_wf (s : string) : Prop := s <> "".
body_wf (s : string) : Prop := CampaignRecord.skip_value (String.length s) s = Some EmptyString.
certificate_wf (c : completeness_certificate) : Prop := scheme_wf (scheme c) /\ body_wf (body c).
completeness_status_wf (cs : completeness_status) : Prop :=
  match cs with
  | CompletenessUnknown | CompletenessIncomplete => True
  | CompletenessComplete c => certificate_wf c
  end.
```

- **`op_completeness_wellformed_impl_true_iff`** -- `op_completeness_wellformed_impl
  cs = true` **iff** `completeness_status_wf cs`. (The Boolean-only version
  survives as `_true_iff_bool`.)
- **`op_completeness_wellformed_impl_false_iff`** -- `= false` iff
  `~ completeness_status_wf cs`.
- **`op_completeness_wellformed_impl_false_spec`** -- spelled out concretely
  (which field failed), for readability / harness cross-checking.
- `wellformed_scheme_true_iff` / `wellformed_body_true_iff` -- the two
  structural Booleans characterised exactly, used as supporting facts.

## 4. Normative vectors (`vm_compute`)

- Scheme: empty rejected; a quote, a backslash, a raw high byte (233), and DEL
  (127) -- all **accepted** (revision-2 fix).
- Body: empty, trailing-garbage (`"5x"`), leading-zero (`"01"`), duplicate
  object keys, non-JSON (`"not-json"`) all rejected; an object, `true`, and a
  quoted ASCII string all accepted; a quoted string wrapping a raw high byte
  rejected (still out of the ASCII-wire subset).
- A well-formed `Complete` certificate accepted; bad-scheme and bad-body
  `Complete` examples rejected; a quoted-scheme `Complete` example now
  **accepted** (revision-2 fix).

## 5. Wiring (`ValidationBinding.v`, `ManifestPipeline.v`)

`ValidationBinding.validate_campaign_valid_completeness` (general, any `ops`)
-- unchanged from revision 1: a successful `validate_campaign` implies
`op_completeness_wellformed ops (ti_completeness ti) = true`.

`ManifestPipeline.pipeline_ops` sets `op_completeness_wellformed` to
`CompletenessWellformed.op_completeness_wellformed_impl`. Theorems (all
SEPARATE; `validate_campaign_pipeline` keeps its three conclusions):

- **`validate_campaign_completeness_agrees`** -- success implies
  `op_completeness_wellformed_impl (ti_completeness ti) = true`.
- **`validate_campaign_completeness_agrees_bool`** / **`_structured`** --
  the Boolean-disjunction and independent-relation corollaries.
- **`record_completeness_of : campaign_record -> completeness_status`**
  (Section `Variable`, an abstract denotation, like `ManifestMatching.
  policy_context_of`) + **`record_completeness_load_validated (ti :
  trusted_inputs) : Prop := record_completeness_of (ti_record ti) =
  ti_completeness ti`** -- a `Definition`, a predicate on ONE input, exactly
  `ManifestMatching.policy_digest_load_validated`'s shape (revision 2 stated
  this as a blanket `forall ti, ...` Section `Hypothesis`, which is
  UNSATISFIABLE -- two `trusted_inputs` can share `ti_record` while differing
  in `ti_completeness`; fixed in revision 3, see §0). "The value a
  completeness decoder would recover from the record agrees with
  `ti_completeness`, for this input." No completeness decoder exists yet
  (`CampaignRecord.skip_value` only syntactically consumes `completeness`); a
  concrete decoder is the PREFERRED resolution and is future work (candidate
  follow-on unit, or an extension of `RecordCrosscheck`).
- **`validate_campaign_completeness_bound_to_record`** / **`_structured`** --
  each takes `record_completeness_load_validated ti` as an explicit premise
  (about the one `ti` the theorem is proved for) and states the governing
  obligation over `ti.rec.completeness` (via `record_completeness_of
  (ti_record ti)`) directly, closing the revision-1 gap.

## 6. Harness

`ocaml/test_manifest_authentication.ml`:

- `Unknown`/`Incomplete` accepted unconditionally; well-formed `Complete`
  bodies (object / boolean / string) accepted.
- Revision-2 acceptance: quoted, backslash-containing, high-byte, and DEL-byte
  schemes all **accepted**.
- Remaining failure classes: empty scheme; empty / trailing-garbage /
  leading-zero / duplicate-key / non-JSON / high-byte-string body.
- `wellformed_scheme` / `wellformed_body` exercised in isolation, matching the
  Coq vectors.
- **Blocker-2 demonstration**: two campaign records differing ONLY in their
  `completeness` payload (`"unknown"` vs a `Complete` certificate) decode via
  `parse_record_full_impl` to the **identical** typed view -- `completeness`
  never reaches it -- while `op_completeness_wellformed_impl` is shown
  accepting or rejecting `ti_completeness`-shaped values with no reference to
  what either record's bytes actually say, concretely exhibiting the gap
  `record_completeness_load_validated` now states as an explicit premise.

## Effect on the status ledger

`op_completeness_wellformed`: **concrete, standalone AND integrated**
(`pipeline_ops`), with positive/negative characterisations over the
independent `completeness_status_wf` relation, and (conditional on an
explicit PER-INPUT F.3 premise) a theorem binding the checked value to
`ti.rec.completeness`. **Reviewer-concurred by source inspection and
promoted** (2026-09-13; revision 1 HELD; revision 2 HELD -- blocker 1
concurred closed, blocker 2 persisted in an unsatisfiable global form;
**revision 3 PASS and CONCUR** -- both blockers closed, promotion authorised;
reviewed ZIP sha256 `b4298a2c4f0bdecd7d601a71830bd2e1ecbf1d8cba567f85168f9ade7df3cae3`).
Residuals: the ASCII-wire-subset scope of `wellformed_body` is a
reviewer-concurred decision, not yet folded into a governing document; a
concrete completeness-status decoder from `ti_record ti` remains future work
(`record_completeness_of` / `record_completeness_load_validated` stand in as
an explicit per-input premise until then).

Still OPEN: `op_transcript_digest`.

`make check` exits 0: `coqchk` covers **19** modules; across `make check`,
**133** `Print Assumptions` "Closed under the global context" (121 + 12);
**seven** `make test` harnesses PASS.

Phase 1 remains **open**; Phase 2 is not authorised; this unit is promoted but
that is **not** a Phase 1 closure. The r5-r13 and r17 promotions are
unaffected. Next authorised validation unit: `op_transcript_digest`.
