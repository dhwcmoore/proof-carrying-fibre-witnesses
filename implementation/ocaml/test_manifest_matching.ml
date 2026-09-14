(* Exercises the extracted concrete manifest matchers (ManifestMatching):
   committed manifest accepted; tampered policy_hash / context digest rejected;
   unparseable manifest rejected.

   digest = string here (see ExtractStage2.v): test harness only.

   Closure-report obligation 3: Z / nat now extract to Big_int_Z.big_int, so
   `verifier_config`'s numeric fields below are Big_int_Z literals for type
   correctness -- but `manifest_policy_matches_impl` / `_context_matches_impl`
   never inspect `trusted_inputs.ti_config` at all (they match on
   `ti_manifest`/`ti_policy`/`ti_policy_digest`, all strings), so there is no
   arithmetic or numeric comparison in this file for a beyond-63-bit case to
   exercise. The genuine numeric-boundary coverage for this Extract*.v lives
   in test_stage1.ml / test_stage1_wrapper.ml / test_stage2.ml /
   test_context_resolution.ml. *)

module S = Extracted_stage2

let bi = Big_int_Z.big_int_of_int

let deqb (a : string) (b : string) : bool = a = b

let committed_ctx : S.context_descriptor =
  { S.cd_model_artifact_digest = "M"; S.cd_preprocessing_digest = "PP"; S.cd_inference_spec_digest = "INF" }

(* the campaign-manifest view the F.3 decoder would yield *)
let view ~phash ~ctx : S.campaign_manifest_view =
  { S.cm_audit_instance_id = "ai-0001"; S.cm_campaign_id = "cmp-1"; S.cm_policy_hash = phash;
    S.cm_context_digests = ctx; S.cm_submission_digests = ["d1"; "d2"] }

(* manifest wire token -> view *)
let parse_manifest (m : S.manifest) : S.campaign_manifest_view option =
  match (m : string) with
  | "good"      -> Some (view ~phash:"pd-committed" ~ctx:committed_ctx)
  | "bad-phash" -> Some (view ~phash:"pd-other" ~ctx:committed_ctx)
  | "bad-ctx"   -> Some (view ~phash:"pd-committed"
                           ~ctx:{ committed_ctx with S.cd_inference_spec_digest = "X" })
  | _           -> None

(* policy payload digest embedded in the committed policy document *)
let policy_context_of (_p : S.policy0) : S.context_descriptor = committed_ctx

let sched : S.fuel_schedule =
  { S.commitment_parse_fuel = bi 0; S.signature_verify_fuel = bi 0;
    S.manifest_bind_fuel = bi 0; S.record_bind_fuel = bi 0; S.preflight_fuel = bi 0;
    S.stage1_base_fuel = bi 0; S.stage1_per_byte_fuel = bi 0 }
let cfg : S.verifier_config =
  { S.max_candidates = bi 0; S.max_wire_bytes = bi 0; S.max_transcript_bytes = bi 0;
    S.max_fuel = bi 0; S.model_call_fuel = bi 0; S.max_fuel_per_candidate = bi 0;
    S.schedule = sched; S.config_trust_anchor = { S.ta_authorised_signers = []; S.ta_keys = [] } }

let ti ~pdigest : S.trusted_inputs =
  { S.ti_commitment_wire = { S.cw_digest=""; S.cw_signer=""; S.cw_signature="" }; S.ti_manifest = "good"; S.ti_submissions = [];
    S.ti_record = ""; S.ti_completeness = S.CompletenessUnknown;
    S.ti_config = cfg; S.ti_policy_document = ""; S.ti_policy = "p-committed";
    S.ti_policy_digest = pdigest }

let pol m t = S.manifest_policy_matches_impl deqb parse_manifest m t
let ctxm m t = S.manifest_context_matches_impl deqb parse_manifest policy_context_of m t

let () =
  let t = ti ~pdigest:"pd-committed" in
  assert (pol "good" t = true);
  assert (ctxm "good" t = true);
  (* manifest carrying the wrong committed policy hash *)
  assert (pol "bad-phash" t = false);
  (* manifest carrying the wrong context digests *)
  assert (ctxm "bad-ctx" t = false);
  (* verifier's policy digest disagrees with the manifest's *)
  assert (pol "good" (ti ~pdigest:"pd-other") = false);
  (* unparseable manifest *)
  assert (pol "junk" t = false);
  assert (ctxm "junk" t = false);
  (* descriptor_eqb sanity *)
  assert (S.descriptor_eqb deqb committed_ctx committed_ctx = true);
  assert (S.descriptor_eqb deqb committed_ctx
            { committed_ctx with S.cd_model_artifact_digest = "Z" } = false);
  print_endline
    "PASS: manifest matching -- committed accepted; wrong policy-hash / \
     context-digest / verifier-digest / unparseable rejected"
