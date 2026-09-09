# Phase 1 -- O1 / O2 / O3 bound to the descriptor and inference spec; shared-`C` wiring

Date: 2026-09-06
Baseline: `PHASE_1_STAGE1_WRAPPER.md` (reviewer-concurred). Two modules,
`implementation/rocq/ContextResolution.v` and `PipelineWiring.v`, `Qed` and
axiom-free. This revision addresses the reviewer's "descriptor binding
incomplete" and "probe/specification binding external" findings.

## Descriptor is structured and checked

```
descriptor := { d_model_digest ; d_preproc_digest ; d_inference_digest : digest }

preflight_check lc :=
  match parse_descriptor (loaded_descriptor lc) with
  | None   => PreflightFail ArtifactMismatch [O1 "descriptor_unparseable"]
  | Some d =>
      if   model_digest_of   (loaded_model_bytes lc)     = d_model_digest d      (* O1 *)
      then if preproc_digest_of (loaded_preproc_bytes lc) = d_preproc_digest d
           && inference_digest_of (loaded_inference_bytes lc) = d_inference_digest d  (* O2 *)
           then PreflightOk … else PreflightFail SpecMismatch …
      else PreflightFail ArtifactMismatch …
  end
```

- **`preflight_ok_binds`**: `PreflightOk` ⇒ `∃ d, parse_descriptor
  (loaded_descriptor lc) = Some d ∧ byte_digest_consistent lc d`. The loaded
  byte-digests equal the fields of the descriptor **parsed from
  `loaded_descriptor lc`**. Sensitivity is to the *decoded* descriptor:
  `parse_descriptor` may map distinct encodings to the same `descriptor`, so not
  every byte change to `loaded_descriptor lc` alters acceptance (the test shows
  one change that does).
- **`preflight_ok_artifact_bound`**: `PreflightOk` **and the hypothesis**
  `parse_descriptor (loaded_descriptor lc) = Some committed_descriptor` ⇒
  `byte_digest_consistent lc committed_descriptor`,
  `commits committed_authcommitment committed_descriptor` (hypothesis
  `committed_authentic`), and `realises_C lc`. This is a **conditional**
  connection -- it does not establish that an *accepted* execution's loaded
  descriptor is the authenticated one; that requires connecting
  `validate_campaign` success to the descriptor equality (see "Next").
- **`preflight_fail_reason`**: `ArtifactMismatch` (descriptor / O1) or
  `SpecMismatch` (O2) only.

`realises_C : loaded_context -> Prop` **remains an uninterpreted predicate** --
its meaning is supplied entirely by the `committed_bytes_realise` hypothesis.
The only change from the previous revision is the *shape* of that hypothesis: it
is now conditioned on `byte_digest_consistent lc committed_descriptor` rather
than unconditional. Whether `realises_C` should be *defined* as "the model /
preproc bytes implement `C`" (rather than assumed) is open.

## O3 probe is derived from the inference bytes

```
eval_o3_check lc ev p :=
  match probe_of_spec (loaded_inference_bytes lc) with
  | None                => O3Fail [O3 "inference_spec_probe_unavailable"]
  | Some (pin, pobs)    =>
      if event_input ev = pin && event_outcome ev = ExecOk pobs
      then O3Ok (resolved_context policy=p, descriptor=loaded_descriptor lc) …
      else O3Fail …
  end
```

- **`eval_o3_ok_binds`**: `O3Ok rc _` ⇒ `∃ pin pobs,
  probe_of_spec (loaded_inference_bytes lc) = Some (pin, pobs)` and the event
  equals `(pin, ExecOk pobs)`, `resolved_policy rc = p`,
  `resolved_descriptor rc = loaded_descriptor lc`.

The probe comes from `loaded_inference_bytes lc`, whose digest O2 checked equals
`d_inference_digest` of the committed descriptor -- so the **provenance** of the
decoder's input is established. This is *not* decoder correctness: the probe
equals the inference spec's checkpoint probe (and its checkpoint shape/type)
only under `probe_of_spec` conformance, which is F.3. `pin` / `pobs` carry the
kernel dimensions `n_pre` / `n_obs` (dimensions relative to those).

## `resolve` and the shared-`C` wiring (`PipelineWiring.v`)

`resolve lc ev` = preflight then O3, returning `Some (C, rc)` on success.

- **`resolve_some_is_committed`** (given `parse_descriptor (loaded_descriptor lc)
  = Some committed_descriptor`): `Cr = C`, `resolved_policy rc = p_committed`,
  `resolved_descriptor rc = loaded_descriptor lc`, `byte_digest_consistent lc
  committed_descriptor`, `commits committed_authcommitment committed_descriptor`,
  `realises_C lc`, and `∃ pin pobs, probe_of_spec (loaded_inference_bytes lc) =
  Some (pin, pobs) ∧ event = (pin, ExecOk pobs)`.
- **`stage1_stage2_use_resolved_context`**: `stage1_semantic_check Cr …` and
  `adapter_stage2_check Cr …` are those with `C`; `context_policy Cr =
  context_policy C`.
- **`PipelineWiring.wired_ops base`** replaces `op_stage1_check` /
  `op_preflight` / `op_eval_o3` / `op_stage2_check` with the `C`-closed
  functions, keeping eleven from `base`.
  `wired_ops_op_stage1_sound`, `wired_ops_stage2_index_contract`,
  `wiring_resolution_consistent` (wired preflight+O3 succeed ⇒
  `resolve = Some (C, rc)` and both checkers are `C`-closed),
  `wired_run_stage1_pending_invariant` (about the `run_stage1` pending list
  `replay` threads unchanged), `wired_c_recheck_redundant`.

## Still F.3-external

- `parse_descriptor` / `probe_of_spec` correctness (wire decoding);
- `digest_eqb` / `model_digest_of` / `preproc_digest_of` / `inference_digest_of`
  truthfulness;
- `commits committed_authcommitment committed_descriptor` (the manifest
  authentication chain -- Ed25519 / commitment digest, `AUDIT_POLICY` 2.4);
- that the *loaded* descriptor is the committed one
  (`parse_descriptor (loaded_descriptor lc) = Some committed_descriptor` -- the
  retrieval store returned the right descriptor);
- the kernel-`Policy` ↔ policy-string correspondence;
- the actual `replay` path supplying `p_committed` to `op_eval_o3`
  (`ManifestPolicyMismatch` / manifest binding);
- `transcript_stage2_wf`; capture/replay correspondence; canonical encoding;
  arbitrary-precision extraction; cross-language battery; the eleven inherited
  `base` `primitive_ops` members.

## Executable exercise

`preflight_check` / `eval_o3_check` / `resolve` extracted via `ExtractStage2.v`;
`ocaml/test_context_resolution.ml` (`make test`, `Z -> int` harness) exercises
descriptor-unparseable / O1 / O2 fail, both pass, "changing only the descriptor
changes acceptance", probe-spec-unavailable / O3 mismatch / O3 pass, and
`resolve` None/Some.

`make check` exits 0: `coqchk` nine modules; **42** `Print Assumptions` "Closed
under the global context" across `make check`; five `make test` harnesses PASS.
