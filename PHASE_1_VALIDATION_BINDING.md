# Phase 1 -- `validate_campaign` success bound to the committed policy and descriptor

Date: 2026-09-06
Baseline: `PHASE_1_CONTEXT_RESOLUTION.md`. One new module,
`implementation/rocq/ValidationBinding.v`, `Qed` and axiom-free.

Discharges two assumptions the earlier units supplied separately:
- the actual `replay` path supplies `p_committed` to `op_eval_o3`;
- the authenticated commitment `commits` the committed descriptor.

## `validate_campaign_valid_guards`

`validate_campaign ops ti = ValidCampaign ac l0` implies there is a parsed
commitment `mc` with `op_parse_commitment … = CommitmentParsed mc`,
`op_signature_valid ops mc (ti_manifest ti) = true`,
`op_manifest_policy_matches ops (ti_manifest ti) ti = true`,
`op_manifest_context_matches ops (ti_manifest ti) ti = true`, and
`ac = authenticated_of ti mc` -- every manifest / commitment guard passed.
(Proof: walk the nested `validate_campaign` match; `ValidCampaign` is the single
terminal branch.)

## The two F.3 contracts -- scoped to ONE `ops`

`Variable ops : primitive_ops` is fixed before the hypotheses, so each contract
constrains **that** implementation, not `forall ops`:

- **`policy_match_sound`**: `forall ti, op_manifest_policy_matches ops
  (ti_manifest ti) ti = true -> ti_policy ti = p_committed`.
- **`context_match_sound`**: `forall ti mc, <mc parsed> -> <mc signature-verified>
  -> op_manifest_context_matches ops (ti_manifest ti) ti = true ->
  commits mc committed_descriptor`.

After section discharge these are ordinary premises about a given `ops`
(`forall ti …`, not `forall ops …`) -- satisfiable when that `ops`'s
manifest-matching primitives are implemented against the frozen manifest schema
(`AUDIT_POLICY_AND_EVIDENCE.md` 2.4 -- PureEdDSA/Ed25519, `M.context_digests`).
The discharged signatures confirm the scoping.

## Dependency split (verified by `Check`)

`validate_campaign_valid_guards` is proved first, for **any** `ops`, before the
section fixes one. Then:

| lemma | contract used | `Check @…` premises |
|---|---|---|
| `validate_campaign_binds_policy` | `policy_match_sound` only | `p_committed`, `ops`, `policy_match_sound`, the `validate_campaign` hyp -- **no** `context_match_sound` / `commits` / `committed_descriptor` |
| `validate_campaign_binds_descriptor` | `context_match_sound` only | adds `committed_descriptor`, `commits`, `context_match_sound` |
| `validate_campaign_binds` | both | union of the two |
| `assess_validated_{live,offline}_uses_committed_policy` | `policy_match_sound` only (via `validate_campaign_binds_policy`) | same as `binds_policy` |

So the report's "the replay path supplies `p_committed` **modulo
`policy_match_sound` only**" claim is now literally what the proof term says.

## Proved

- **`validate_campaign_binds`**: `validate_campaign ops ti = ValidCampaign ac l0`
  ⇒ `ti_policy ti = p_committed` **and**
  `commits (authenticated_commitment ac) committed_descriptor`.
- **`assess_validated_live_uses_committed_policy`** /
  **`assess_validated_offline_uses_committed_policy`**: for a validated campaign,
  `assess_validated ops ti (ValidCampaign ac l0) (LiveTranscript tr cb)` (resp.
  `OfflineParse (WellformedParse tr wd) cb`) equals
  `decide ops (replay ops ac cb (ti_config ti) (ti_policy_document ti)
  p_committed l0 tr) …` -- the `replay` call runs with `p = p_committed`, so
  `replay`'s internal `op_eval_o3 ops lc event p_committed` matches
  `ContextResolution.resolve` / `PipelineWiring.wired_resolve` (which hardcode
  `p_committed`).

## Effect on the status ledger

- "the actual replay path supplies `p_committed` to `op_eval_o3`" -- **now
  discharged** modulo `policy_match_sound` (F.3, explicit).
- "descriptor ↔ manifest-commitment binding" -- the `commits` link is now a
  consequence of `validate_campaign` success modulo `context_match_sound` (F.3,
  explicit).

Still open: `context_match_sound` / `policy_match_sound` themselves (the concrete
manifest-matching primitives); that the *loaded* descriptor equals
`committed_descriptor` (the retrieval store / `load_context`); `parse_descriptor`
/ `probe_of_spec` correctness; a definition for `realises_C`; `transcript_stage2_wf`;
the remaining validation-tier primitives (`op_parse_commitment`,
`op_signer_authorised`, `op_signature_valid`, `op_ledger_mismatch`,
`op_record_identity_mismatch`, `op_completeness_wellformed`); arbitrary-precision
extraction; capture/replay correspondence; canonical encoding; cross-language
battery.

`make check` exits 0: `coqchk` covers `PCFW.ValidationBinding` (ten modules);
across `make check`, **45** `Print Assumptions` "Closed under the global
context"; five `make test` harnesses PASS.
