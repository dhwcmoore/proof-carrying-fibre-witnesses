(* Path-verification for the InconsistentContextBundle repair.

   Scenario: a Valid campaign whose stage 1 completes with one Pending
   candidate, assessed with context_bundle = CtxNotNeeded.  This pairing is
   never produced by `capture`; `replay` must return it truthfully.

   Checks:
     - verdict is OBSTRUCTED
     - obstruction is ContextObstruction InconsistentContextBundle
     - obligation string is "reconstruct_or_supply_context_bundle"
     - context_state is ContextUnresolved (InconsistentContextBundle, [])
       with NO fabricated O1 finding
     - every pending stage-2 slot is NotRun
   Also: the legitimate terminal stage-1 fuel-exhaustion path still yields
   CampaignFuelExhausted (not InconsistentContextBundle) even when an earlier
   submission reached Pending. *)

open Orchestration

let fs = {
  commitment_parse_fuel = 0; signature_verify_fuel = 0; manifest_bind_fuel = 0;
  record_bind_fuel = 0; preflight_fuel = 0; stage1_base_fuel = 1;
  stage1_per_byte_fuel = 0;
}

let cfg = {
  max_candidates = 10; max_wire_bytes = 100; max_transcript_bytes = 100;
  max_fuel = 1000; model_call_fuel = 1; max_fuel_per_candidate = 100;
  schedule = fs; config_trust_anchor = { authorised_signers = ["s"]; keys = [("s", "k")] };
}

let sub i = { wire = "w"; wire_length = 1; digest = Printf.sprintf "d%d" i }

let pending_of trusted_index = {
  index = trusted_index;              (* deliberately wrong; orchestration overwrites *)
  submission_digest = "sd"; semantic_digest = "cd";
  candidate = { x = [1]; y = [2] }; stage1_findings = [];
}

let mc = { commitment_digest = "mcd"; signer = "s"; commitment_signature = "sig" }

let ac subs = {
  commitment = mc; manifest = "m"; submissions = subs; record = "r";
  completeness = Unknown;
}

(* op_stage1_check: submission 0 -> Pending, others -> NotAWitness1.
   It reports a bogus pending index (99) to prove orchestration ignores it. *)
let ops = {
  parse_commitment = (fun _ -> Parsed mc);
  signer_authorised = (fun _ _ -> true);
  signature_valid = (fun _ _ _ -> true);
  manifest_policy_matches = (fun _ _ -> true);
  manifest_audit_matches = (fun _ _ -> true);
  manifest_context_matches = (fun _ _ -> true);
  ledger_mismatch = (fun _ _ -> None);
  record_identity_mismatch = (fun _ _ _ _ -> None);
  completeness_wellformed = (fun _ -> true);
  stage1_check = (fun _ _ _ i _ ->
    if i = 0 then { index = i; verdict = Pending (pending_of 99); findings = [] }
    else { index = i; verdict = NotAWitness1 InputsEqual; findings = [] });
  preflight = (fun _ -> PreflightOk []);
  eval_o3 = (fun _ _ _ -> O3Fail []);
  stage2_check = (fun _ _ _ ps ->
    { index = ps.index; verdict = NotAWitness2 InputsEqual; findings = [] });
  record_crosscheck = (fun _ _ _ _ -> []);
  transcript_digest = (fun _ -> "td");
}

let fail msg = Printf.printf "FAIL: %s\n" msg; exit 1

let () =
  (* ---- Case 1: CtxNotNeeded + completed stage 1 with a Pending candidate ---- *)
  let rr = replay ops (ac [sub 0; sub 1]) CtxNotNeeded cfg "pd" "p"
             { budget = 1000; consumed = 0 } [] in
  (match rr.context with
   | ContextBundleInconsistent -> ()   (* no reason, no findings, by type *)
   | _ -> fail "context_state is not ContextBundleInconsistent");
  (match rr.clo with
   | Some InconsistentContextBundle -> ()
   | _ -> fail "clo is not InconsistentContextBundle");
  List.iter (fun s -> match s.s2_result with
    | NotRun -> () | Done _ -> fail "a pending stage-2 slot ran") rr.stage2;
  if rr.stage2 = [] then fail "expected one pending stage-2 slot";
  (* pending index is orchestration-assigned (0), not the bogus 99 *)
  List.iter (fun s -> if s.s2_index <> 0 then fail "pending index not orchestration-assigned")
    rr.stage2;

  let src = LiveTranscript ([], CtxNotNeeded) in
  let outcome = assess_validated ops (
    { commitment_wire = { cw_digest = "d"; cw_signer = "s"; cw_signature = "x" }; manifest = "m"; submissions = [sub 0; sub 1];
      record = "r"; completeness = Unknown; config = cfg;
      policy_document = "pd"; policy = "p"; policy_digest = "pdg" })
    (Valid (ac [sub 0; sub 1], { budget = 1000; consumed = 0 })) src in
  (match verdict_of outcome with
   | OBSTRUCTED -> () | _ -> fail "verdict is not OBSTRUCTED");
  (match outcome with
   | Obstructed { body = ObstructedBody (InconsistentContextBundle,
                                         "reconstruct_or_supply_context_bundle", []); _ } -> ()
   | Obstructed { body = ObstructedBody (_, ob, _); _ } ->
       fail (Printf.sprintf "obligation string is %S" ob)
   | _ -> fail "not an Obstructed certificate");

  (* ---- Case 1b: CtxUnavailable cannot carry the bundle-inconsistency reason.
     `ctx_reason` has only ArtifactMismatch | SpecMismatch | RepNotReproduced, so
     `CtxUnavailable InconsistentContextBundle` is a type error — the leak the
     shared-type version had is now unconstructible.  A real unavailable reason
     still flows through unchanged: *)
  let rr_unavail = replay ops (ac [sub 0; sub 1]) (CtxUnavailable ArtifactMismatch)
                     cfg "pd" "p" { budget = 1000; consumed = 0 } [] in
  (match rr_unavail.clo with
   | Some (ContextObstruction ArtifactMismatch) -> ()
   | _ -> fail "CtxUnavailable ArtifactMismatch path changed");
  (match rr_unavail.context with
   | ContextUnresolved (ArtifactMismatch, _ :: _) -> ()
   | _ -> fail "CtxUnavailable path lost its O1 finding");

  (* ---- Case 2: terminal stage-1 fuel exhaustion after an earlier Pending ---- *)
  (* budget covers submission 0 (which becomes Pending) then runs out at 1 *)
  let tight = { budget = 1; consumed = 0 } in
  let rr2 = replay ops (ac [sub 0; sub 1]) CtxNotNeeded cfg "pd" "p" tight [] in
  (match rr2.clo with
   | Some CampaignFuelExhausted -> ()
   | _ -> fail "terminal stage-1 exhaustion should be CampaignFuelExhausted");
  (match rr2.context with
   | NoContextNeeded -> ()
   | _ -> fail "terminal stage-1 exhaustion should leave NoContextNeeded");

  print_string "PASS: InconsistentContextBundle reported truthfully; \
                terminal stage-1 exhaustion unaffected\n"
