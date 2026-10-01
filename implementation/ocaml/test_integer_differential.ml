(* Finite-case comparator client; oracle and case inventory are in differential.py. *)
module S = Extracted_phase1_integration
module T = Extracted_transcript_digest
module M = Extracted_manifest_auth
module W = Extracted_stage2
open S
let big = Big_int_Z.big_int_of_string
let show = Big_int_Z.string_of_big_int
let natural s = let v=big s in if Big_int_Z.sign_big_int v<0 then invalid_arg "negative nat";v
let zero=natural "0"
let unused _ = failwith "differential verdict fixture called an unused hook"
let ops = {op_parse_commitment=unused;op_signer_authorised=(fun _ -> unused);op_signature_valid=(fun _ _ -> unused);op_manifest_policy_matches=(fun _ -> unused);op_manifest_audit_matches=(fun _ -> unused);op_manifest_context_matches=(fun _ -> unused);op_ledger_mismatch=(fun _ -> unused);op_record_identity_mismatch=(fun _ _ _ -> unused);op_completeness_wellformed=unused;op_stage1_check=(fun _ _ _ _ -> unused);op_preflight=unused;op_eval_o3=(fun _ _ -> unused);op_stage2_check=(fun _ _ _ -> unused);op_record_crosscheck=(fun _ _ _ -> unused);op_transcript_digest=unused}
let cfg={max_candidates=zero;max_wire_bytes=zero;max_transcript_bytes=zero;max_fuel=zero;model_call_fuel=zero;max_fuel_per_candidate=zero;schedule={commitment_parse_fuel=zero;signature_verify_fuel=zero;manifest_bind_fuel=zero;record_bind_fuel=zero;preflight_fuel=zero;stage1_base_fuel=zero;stage1_per_byte_fuel=zero};config_trust_anchor={ta_authorised_signers=[];ta_keys=[]}}
let mc={commitment_digest="d";commitment_signer="s";commitment_signature="sig"}
let ac={authenticated_commitment=mc;authenticated_manifest="m";authenticated_submissions=[];authenticated_record="r";authenticated_completeness=CompletenessUnknown}
let ti={ti_commitment_wire={cw_digest="d";cw_signer="s";cw_signature="sig"};ti_manifest="m";ti_submissions=[];ti_record="r";ti_completeness=CompletenessUnknown;ti_config=cfg;ti_policy_document="p";ti_policy="p";ti_policy_digest="d"}
let wd={witness_index=zero;witness_submission_digest="sd";witness_semantic_digest="cd";witness_x=[big "4611686018427387904"];witness_y=[big "-40000000000000000000000000001"];witness_o_x=[];witness_o_y=[];witness_findings=[]}
let verdict kind =
  let slots=if kind="witness" then [{stage2_slot_index=zero;stage2_slot_result=Done {s2_index=zero;s2_verdict=ValidWitness wd;s2_findings=[]}}] else [] in
  let rc={resolved_policy="p";resolved_context_token="c";resolved_descriptor="d"} in
  let ctx=if kind="exact-disabled" then ContextResolved(rc,[]) else NoContextNeeded in
  let campaign=if kind="exact-disabled" then {ac with authenticated_completeness=CompletenessComplete {completeness_scheme="registry-v0";completeness_body="b"}} else ac in
  let rr={replay_stage1=[];replay_context=ctx;replay_stage2=slots;replay_fuel={fuel_budget=natural "100";fuel_consumed=zero};replay_clo=(if kind="fuel" then Some CampaignFuelExhausted else None);replay_record_findings=[]} in
  match verdict_of (decide ops rr campaign ti [] NoTranscript (ParsedCommitment "d")) with
  | INADMISSIBLE->"INADMISSIBLE" | OBSTRUCTED->"OBSTRUCTED" | UNDERDETERMINED->"UNDERDETERMINED" | EXACT->"EXACT"
let run = function
  | ["add";a;b] -> show (M.add (natural a) (natural b))
  | ["mul";a;b] -> show (T.mul (natural a) (natural b))
  | ["zeq";a;b] -> string_of_bool (W.Z.eqb (big a) (big b))
  | ["charge";budget;used;cost] -> (match T.charge {T.fuel_budget=natural budget;T.fuel_consumed=natural used} (natural cost) with None->"reject" | Some fl->show fl.T.fuel_consumed)
  | ["parse";s] -> (match M.parse_nat s with Some(v,"")->show v | _->"reject")
  | ["nat-input";s] -> (try ignore(natural s);"accept" with Invalid_argument _->"reject")
  | ["event";s] -> let v=big s in let event={T.event_key={T.key_phase=T.ContextProbe;T.key_role=T.Probe;T.key_repeat=zero};T.event_input=[v];T.event_outcome=T.ExecOk [v]} in (match event.T.event_input with [x]->show x | _->assert false)
  | ["verdict";kind] -> verdict kind
  | _ -> failwith "unknown differential case"
let () =
  if Array.length Sys.argv=2 && Sys.argv.(1)="--cases" then
    (try while true do print_endline(run(String.split_on_char '\t' (read_line()))) done with End_of_file->())
  else if Array.length Sys.argv=1 then (
    assert(run ["charge";"4611686018427387903";"4611686018427387903";"1"]="reject");
    assert(run ["nat-input";"-1"]="reject");
    assert(verdict "witness"="INADMISSIBLE");
    print_endline "integer differential client: PASS (oracle comparisons run by differential.py)")
  else failwith "expected --cases or no arguments"
