(* Existing context-bundle/terminal-fuel regressions, now against the bigint
   extraction. This ports test coverage; it implements no capture/replay code. *)
module S = Extracted_orchestration
open S

let n value =
  if value < 0 then invalid_arg "negative nat fixture";
  Big_int_Z.big_int_of_int value
let eq = Big_int_Z.eq_big_int
let fail message = failwith message

let fs = {
  commitment_parse_fuel = n 0; signature_verify_fuel = n 0; manifest_bind_fuel = n 0;
  record_bind_fuel = n 0; preflight_fuel = n 0; stage1_base_fuel = n 1;
  stage1_per_byte_fuel = n 0;
}
let cfg = {
  max_candidates = n 10; max_wire_bytes = n 100; max_transcript_bytes = n 100;
  max_fuel = n 1000; model_call_fuel = n 1; max_fuel_per_candidate = n 100;
  schedule = fs; config_trust_anchor = { ta_authorised_signers = ["s"]; ta_keys = [("s", "k")] };
}
let sub i = { submission_wire = "w"; submission_wire_length = n 1;
              submission_digest = Printf.sprintf "d%d" i }
let pending_of i = {
  pending_index = n i; pending_submission_digest = "sd"; pending_semantic_digest = "cd";
  pending_candidate = { pc_candidate_id = "c"; candidate_x = [n 1]; candidate_y = [n 2] };
  pending_findings = [];
}
let mc = { commitment_digest = "mcd"; commitment_signer = "s"; commitment_signature = "sig" }
let ac subs = {
  authenticated_commitment = mc; authenticated_manifest = "m";
  authenticated_submissions = subs; authenticated_record = "r";
  authenticated_completeness = CompletenessUnknown;
}
let unused _ = failwith "unexpected validation hook in supplied-valid-campaign regression"
let ops = {
  op_parse_commitment = unused; op_signer_authorised = unused; op_signature_valid = unused;
  op_manifest_policy_matches = unused; op_manifest_audit_matches = unused;
  op_manifest_context_matches = unused; op_ledger_mismatch = unused;
  op_record_identity_mismatch = unused; op_completeness_wellformed = unused;
  op_stage1_check = (fun _ _ _ i submission ->
    { s1_index = i; s1_submission_digest = submission.submission_digest;
      s1_candidate_id = Some "c"; s1_semantic_digest = Some "cd";
      s1_verdict = (if eq i (n 0) then S1Pending (pending_of 99) else S1NotAWitness InputsEqual);
      s1_findings = [] });
  op_preflight = (fun _ -> PreflightOk []);
  op_eval_o3 = (fun _ _ _ -> O3Fail []);
  op_stage2_check = (fun _ _ _ ps ->
    { s2_index = ps.pending_index; s2_verdict = S2NotAWitness InputsEqual; s2_findings = [] });
  op_record_crosscheck = (fun _ _ _ _ -> []);
  op_transcript_digest = (fun _ -> "td");
}
let ledger = { fuel_budget = n 1000; fuel_consumed = n 0 }
let () =
  let campaign = ac [sub 0; sub 1] in
  let rr = replay ops campaign CtxNotNeeded cfg "pd" "p" ledger [] in
  assert (rr.replay_context = ContextBundleInconsistent);
  assert (rr.replay_clo = Some InconsistentContextBundle);
  assert (rr.replay_stage2 <> []);
  List.iter (fun slot ->
    assert (slot.stage2_slot_result = NotRun);
    assert (eq slot.stage2_slot_index (n 0))) rr.replay_stage2;
  let ti = {
    ti_commitment_wire = { cw_digest = "d"; cw_signer = "s"; cw_signature = "x" };
    ti_manifest = "m"; ti_submissions = [sub 0; sub 1]; ti_record = "r";
    ti_completeness = CompletenessUnknown; ti_config = cfg;
    ti_policy_document = "pd"; ti_policy = "p"; ti_policy_digest = "pdg" } in
  let outcome = assess_validated ops ti (ValidCampaign (campaign, ledger))
    (LiveTranscript ([], CtxNotNeeded)) in
  assert (verdict_of outcome = OBSTRUCTED);
  (match outcome with
   | Obstructed { certificate_body = ObstructedBody
       (InconsistentContextBundle, "reconstruct_or_supply_context_bundle", []); _ } -> ()
   | _ -> fail "incorrect bundle obstruction certificate");
  let unavailable = replay ops campaign (CtxUnavailable ArtifactMismatch) cfg "pd" "p" ledger [] in
  assert (unavailable.replay_clo = Some (ContextObstruction ArtifactMismatch));
  (match unavailable.replay_context with
   | ContextUnresolved (ArtifactMismatch, _ :: _) -> ()
   | _ -> fail "CtxUnavailable path lost its O1 finding");
  let exhausted = replay ops campaign CtxNotNeeded cfg "pd" "p"
    { fuel_budget = n 1; fuel_consumed = n 0 } [] in
  assert (exhausted.replay_clo = Some CampaignFuelExhausted);
  assert (exhausted.replay_context = NoContextNeeded);
  print_endline "PASS: extracted context-bundle regression -- truthful obstruction, orchestration-owned index, unavailable-context finding and terminal stage-1 fuel exhaustion"
