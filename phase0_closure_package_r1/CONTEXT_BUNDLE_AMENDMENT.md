# Proposed amendment: `context_state` and `campaign_obstruction` gain a bundle-inconsistency case

**Status: PROPOSAL, part of a pre-closure candidate. Not applied to the frozen
Revision 14 governing set. Phase 0 remains open; this requires the reviewer
role's concurrence before it enters the frozen documents.**

## Why

`replay` is total over an arbitrary `context_bundle` (`VERDICT_SEMANTICS.md`
§6.6 scopes `(REP1)` that way). The type system permits
`Stage1Complete ∧ pending ≠ [] ∧ cb = CtxNotNeeded`. `capture` never produces
this pairing, but `replay` must still return a truthful result. The first
skeleton borrowed `ContextObstruction ArtifactMismatch` plus a synthetic failed
`O1` finding, which is untruthful — no digest comparison and no probe ran.

This is distinct from **terminal stage-1 fuel exhaustion**, where `capture`
legitimately emits `CtxNotNeeded` after an earlier `Pending`; that path returns
in the `Stage1Stopped` branch (`NoContextNeeded`, `clo = CampaignFuelExhausted`)
and never consults the bundle. The constructor comment "no submission reached
`Pending`" in `VERDICT_SEMANTICS.md` §2 is therefore too strong.

## Design choice: NOT a `ctx_reason`

`ctx_reason` (`ArtifactMismatch | SpecMismatch | RepNotReproduced`) is the O1/O2/O3
outcome type. It is **shared** by `CtxUnavailable`, `preflight_O1_O2`'s `Fail`,
and `eval_O3`. Adding a bundle-inconsistency constructor to it would make
`CtxUnavailable <that reason>` and `PreflightFail <that reason> …` constructible,
and the existing `CtxUnavailable` / `PreflightFail` branches would then emit the
new reason with a fabricated `O1` finding — reintroducing the very untruthfulness
this amendment removes.

So `ctx_reason` is left unchanged. The bundle-inconsistency case is represented
where it actually occurs:

- **`context_state`** gains `ContextBundleInconsistent` — nullary, no reason, no
  findings.
- **`campaign_obstruction`** gains `InconsistentContextBundle` — nullary, sibling
  of `CampaignFuelExhausted`. `ContextObstruction of ctx_reason` continues to
  carry only genuine O1/O2/O3 reasons.

## Amendment 1 — frozen constructor sets

`VERDICT_SEMANTICS.md` §2:

```
type ctx_reason =                  (* O1–O3, once — UNCHANGED *)
  | ArtifactMismatch | SpecMismatch | RepNotReproduced

type campaign_obstruction =
  | RecordIntegrity      of integrity_reason
  | ValidationFuelExhausted
  | TranscriptMalformed  of { reason : string ; wire_digest : digest }
  | ContextObstruction   of ctx_reason
  | CampaignFuelExhausted
  | CampaignCandidateCountExceeded
  | InconsistentContextBundle       (* NEW — cb = CtxNotNeeded supplied with a
                                       completed stage 1 that produced Pending
                                       candidates.  Not producible by `capture`;
                                       no O1/O2/O3 check ran. *)
  | WitnessObstruction   of { primary_index : nat ; primary_reason : o_reason ; other_indices : nat list }
```

`context_state` (§6.7) gains `| ContextBundleInconsistent` (nullary).

## Amendment 2 — canonical encoding

`AUDIT_POLICY_AND_EVIDENCE.md` §2.2 sum-type constructor rule already covers
nullary constructors (`lower_snake_case` name). Two new encodings:

- `campaign_obstruction`: `"inconsistent_context_bundle"`
- `context_state`: `"context_bundle_inconsistent"`

No new encoding *shape* is introduced. The `context_state` table row (§2.2, line
~170) and the `campaign_obstruction` row (line ~175) each gain one alternative.

## Amendment 3 — `VERDICT_SEMANTICS.md` §6.5 replay slot table

Add one row (and correct the §6.4 `CtxNotNeeded` constructor comment):

| §6.4 outcome | `stage1` | `context` | `stage2` (per `pending`) | `clo` |
|---|---|---|---|---|
| `Stage1Complete`, `pending ≠ []`, `cb = CtxNotNeeded` | all `Done` | `ContextBundleInconsistent` | `NotRun` | `InconsistentContextBundle` |

Reporting contract for this row:

- verdict **OBSTRUCTED**;
- every pending stage-2 slot `NotRun`;
- **no** finding of any kind (the `context` carries none);
- `decide` obligation string `"reconstruct_or_supply_context_bundle"`;
- `(T2)` unaffected — no `ValidWitness` can arise (`context` unresolved, every
  stage-2 slot `NotRun`), so the pairing can never yield `INADMISSIBLE`.

## Amendment 4 — `THREAT_MODEL.md`

Add T30 (bundle/stage-1 inconsistency): a hand-assembled offline package pairs
`ctx_not_needed` with a campaign whose stage 1 yields candidates requiring
context. Mitigation: `replay` fail-closes to
`OBSTRUCTED / InconsistentContextBundle`; offline reconstruction normally derives
the bundle via `load_context` and never selects `CtxNotNeeded` for such a
campaign.

## Alternative (Phase 1 may prefer)

Make the pairing unconstructible: index `replay`'s bundle argument on whether
stage 1 produced pending candidates (dependent input type), so `CtxNotNeeded` is
not typeable alongside a non-empty pending list. Removes the constructor at the
cost of a heavier input type.

## Implementation state

Applied in `implementation/` (Rocq + OCaml mirror + `make test`), built clean
with `make check`. `ctx_reason` is unchanged, so `CtxUnavailable
InconsistentContextBundle` is a type error — `ocaml/test_context_bundle.ml`
records this and checks the real `CtxUnavailable ArtifactMismatch` path is
unaffected. See `README.md` § "Totality case" and § "Follow-up build".
