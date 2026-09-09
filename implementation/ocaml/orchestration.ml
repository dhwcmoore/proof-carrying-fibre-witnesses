include struct
  type digest = string
  type bytes = string
  type policy_document = string
  type policy = string
  type integrity_reason = BadCommitmentEncoding of string | SignerNotAuthorised | SignatureInvalid | ManifestPolicyMismatch | ManifestAuditInstanceMismatch | ManifestContextMismatch | LedgerMismatch of int | RecordIdentityMismatch of string | CompletenessMalformed
  type ctx_reason = ArtifactMismatch | SpecMismatch | RepNotReproduced
  type o_reason = ExecMissing | ExecInputMismatch | ExecFailure | ExecFuelExhausted | NonDeterministic | ObsOutOfRange
  type c_reason = InputsEqual | XNotInDomain | YNotInDomain | QuantisedObservationsDiffer | TargetsAgree
  type b_reason = BundleLimitExceeded | InvalidUtf8 | MalformedStructure | DuplicateKeys | SchemaUnrecognised | SchemaVersionMismatch | UnknownCriticalField | OverrideField | PolicyHashMismatch | InputStructureError | MalformedIntegerLiteral
  type finding = { check_id : string; passed : bool; reason : string option }
  type fuel_ledger = { budget : int; consumed : int }
  type fuel_schedule = { commitment_parse_fuel : int; signature_verify_fuel : int; manifest_bind_fuel : int; record_bind_fuel : int; preflight_fuel : int; stage1_base_fuel : int; stage1_per_byte_fuel : int }
  type trust_anchor = { authorised_signers : string list; keys : (string * bytes) list }
  type verifier_config = { max_candidates : int; max_wire_bytes : int; max_transcript_bytes : int; max_fuel : int; model_call_fuel : int; max_fuel_per_candidate : int; schedule : fuel_schedule; config_trust_anchor : trust_anchor }
  type candidate_submission = { wire : bytes; wire_length : int; digest : digest }
  type parsed_candidate = { x : int list; y : int list }
  type pending_submission = { index : int; submission_digest : digest; semantic_digest : digest; candidate : parsed_candidate; stage1_findings : finding list }
  type stage1_verdict = Rejected of b_reason | NotAWitness1 of c_reason | Pending of pending_submission
  type stage1_result = { index : int; verdict : stage1_verdict; findings : finding list }
  type witness_data = { witness_index : int; witness_findings : finding list }
  type stage2_verdict = WitnessCheckObstructed of o_reason | NotAWitness2 of c_reason | ValidWitness of witness_data
  type stage2_result = { index : int; verdict : stage2_verdict; findings : finding list }
  type call_phase = ContextProbe | Stage2 of int
  type call_role = Probe | X | Y
  type call_key = { phase : call_phase; role : call_role; repeat : int }
  type exec_outcome = Ok of int list | Failed of string | Exhausted
  type exec_event = { key : call_key; input : int list; outcome : exec_outcome }
  type exec_transcript = exec_event list
  type manifest_commitment_wire = { cw_digest : string; cw_signer : string; cw_signature : string }
  type manifest_commitment = { commitment_digest : digest; signer : string; commitment_signature : bytes }
  type manifest = string
  type campaign_record = string
  type completeness_certificate = { scheme : string; body : string }
  type completeness_status = Unknown | Incomplete | Complete of completeness_certificate
  type authenticated_campaign = { commitment : manifest_commitment; manifest : manifest; submissions : candidate_submission list; record : campaign_record; completeness : completeness_status }
  type loaded_context = { descriptor : digest; context_token : string }
  type resolved_context = { policy : policy; context_token : string; descriptor : digest }
  type context_bundle = CtxNotNeeded | CtxUnavailable of ctx_reason | CtxLoaded of loaded_context
  type context_state = NoContextNeeded | ContextUnresolved of ctx_reason * finding list | ContextResolved of resolved_context * finding list | ContextBundleInconsistent
  type campaign_obstruction = RecordIntegrity of integrity_reason | ValidationFuelExhausted | TranscriptMalformed of string * digest | ContextObstruction of ctx_reason | CampaignFuelExhausted | CampaignCandidateCountExceeded | InconsistentContextBundle | WitnessObstruction of int * o_reason * int list
  type commitment_evidence = UnparsedCommitment of manifest_commitment_wire | ParsedCommitment of digest | AuthenticatedCommitment of digest
  type transcript_evidence = NoTranscript | MalformedTranscript of string * digest | LiveCapture of digest | OfflineTranscript of digest * digest
  type 'a slot = Done of 'a | NotRun
  type stage1_slot = { s1_index : int; s1_result : stage1_result slot }
  type stage2_slot = { s2_index : int; s2_result : stage2_result slot }
  type replay_result = { stage1 : stage1_slot list; context : context_state; stage2 : stage2_slot list; fuel : fuel_ledger; clo : campaign_obstruction option; record_findings : finding list }
  type parse_result = Malformed of string * digest | Wellformed of exec_transcript * digest
  type transcript_source = LiveTranscript of exec_transcript * context_bundle | OfflineParse of parse_result * context_bundle
  type validation_result = Invalid of integrity_reason * fuel_ledger * commitment_evidence | FuelObstructed of fuel_ledger * commitment_evidence | Valid of authenticated_campaign * fuel_ledger
  type trusted_inputs = { commitment_wire : manifest_commitment_wire; manifest : manifest; submissions : candidate_submission list; record : campaign_record; completeness : completeness_status; config : verifier_config; policy_document : policy_document; policy : policy; policy_digest : digest }
  type preflight_result = PreflightFail of ctx_reason * finding list | PreflightOk of finding list
  type o3_result = O3Fail of finding list | O3Ok of resolved_context * finding list
  type cert_body = InadmissibleBody of witness_data * int list * finding list | ExactBody of completeness_certificate | ObstructedBody of campaign_obstruction * string * finding list
  type replay_input = InvalidFuel of fuel_ledger | ReplayDone of replay_result
  type certificate = { body : cert_body; replay : replay_input; transcript : transcript_evidence; commitment_evidence : commitment_evidence }
  type campaign_report = { replay_result : replay_result; transcript_evidence : transcript_evidence }
  type assessment_outcome = Inadmissible of certificate | Exact of certificate | Obstructed of certificate | Underdetermined of campaign_report
  type campaign_verdict = INADMISSIBLE | EXACT | UNDERDETERMINED | OBSTRUCTED
  type parse_commitment_result = ParseError of string | Parsed of manifest_commitment
  type primitive_ops = { parse_commitment : manifest_commitment_wire -> parse_commitment_result; signer_authorised : verifier_config -> manifest_commitment -> bool; signature_valid : verifier_config -> manifest_commitment -> manifest -> bool; manifest_policy_matches : manifest -> trusted_inputs -> bool; manifest_audit_matches : manifest -> trusted_inputs -> bool; manifest_context_matches : manifest -> trusted_inputs -> bool; ledger_mismatch : manifest -> candidate_submission list -> int option; record_identity_mismatch : campaign_record -> manifest_commitment -> manifest -> trusted_inputs -> string option; completeness_wellformed : completeness_status -> bool; stage1_check : verifier_config -> policy_document -> policy -> int -> candidate_submission -> stage1_result; preflight : loaded_context -> preflight_result; eval_o3 : loaded_context -> exec_event -> policy -> o3_result; stage2_check : resolved_context -> verifier_config -> exec_transcript -> pending_submission -> stage2_result; record_crosscheck : authenticated_campaign -> stage1_slot list -> stage2_slot list -> verifier_config -> finding list; transcript_digest : exec_transcript -> digest }

  let charge ledger cost =
    let used = ledger.consumed + cost in
    if used <= ledger.budget then Some { ledger with consumed = used } else None

  let lookup_unique transcript key =
    match List.filter (fun event -> event.key = key) transcript with
    | [event] -> Some event | _ -> None

  let authenticate ti mc = { commitment = mc; manifest = ti.manifest; submissions = ti.submissions; record = ti.record; completeness = ti.completeness }

  let validate_campaign ops ti =
    let l0 = { budget = ti.config.max_fuel; consumed = 0 } in
    let fs = ti.config.schedule in
    match charge l0 fs.commitment_parse_fuel with
    | None -> FuelObstructed (l0, UnparsedCommitment ti.commitment_wire)
    | Some l1 ->
      match ops.parse_commitment ti.commitment_wire with
      | ParseError message -> Invalid (BadCommitmentEncoding message, l1, UnparsedCommitment ti.commitment_wire)
      | Parsed mc ->
        let parsed = ParsedCommitment mc.commitment_digest in
        if not (ops.signer_authorised ti.config mc) then Invalid (SignerNotAuthorised, l1, parsed) else
        match charge l1 fs.signature_verify_fuel with
        | None -> FuelObstructed (l1, parsed)
        | Some l2 ->
          if not (ops.signature_valid ti.config mc ti.manifest) then Invalid (SignatureInvalid, l2, parsed) else
          let auth = AuthenticatedCommitment mc.commitment_digest in
          match charge l2 fs.manifest_bind_fuel with
          | None -> FuelObstructed (l2, auth)
          | Some l3 ->
            if not (ops.manifest_policy_matches ti.manifest ti) then Invalid (ManifestPolicyMismatch, l3, auth)
            else if not (ops.manifest_audit_matches ti.manifest ti) then Invalid (ManifestAuditInstanceMismatch, l3, auth)
            else if not (ops.manifest_context_matches ti.manifest ti) then Invalid (ManifestContextMismatch, l3, auth)
            else match charge l3 fs.record_bind_fuel with
              | None -> FuelObstructed (l3, auth)
              | Some l4 ->
                match ops.ledger_mismatch ti.manifest ti.submissions with
                | Some i -> Invalid (LedgerMismatch i, l4, auth)
                | None ->
                  match ops.record_identity_mismatch ti.record mc ti.manifest ti with
                  | Some field -> Invalid (RecordIdentityMismatch field, l4, auth)
                  | None -> if not (ops.completeness_wellformed ti.completeness)
                    then Invalid (CompletenessMalformed, l4, auth)
                    else Valid (authenticate ti mc, l4)

  let stage1_cost cfg sub = cfg.schedule.stage1_base_fuel + cfg.schedule.stage1_per_byte_fuel * min sub.wire_length (cfg.max_wire_bytes + 1)
  let rec stage1_not_run i = function [] -> [] | _ :: rest -> { s1_index=i; s1_result=NotRun } :: stage1_not_run (i+1) rest
  let stage2_not_run (pending : pending_submission list) = List.map (fun (p : pending_submission) -> { s2_index=p.index; s2_result=NotRun }) pending

  type stage1_run = S1Complete of fuel_ledger * stage1_slot list * pending_submission list | S1Stopped of fuel_ledger * stage1_slot list * pending_submission list
  let rec run_stage1 ops cfg pd policy subs i fuel slots_rev pending_rev = match subs with
    | [] -> S1Complete (fuel, List.rev slots_rev, List.rev pending_rev)
    | sub :: rest -> match charge fuel (stage1_cost cfg sub) with
      | None -> S1Stopped (fuel, List.rev slots_rev @ stage1_not_run i subs, List.rev pending_rev)
      | Some fuel' ->
        let result = ops.stage1_check cfg pd policy i sub in
        (* orchestration owns the pending index: position i, not a trusted value *)
        let pending_rev' = match result.verdict with Pending p -> { p with index = i } :: pending_rev | _ -> pending_rev in
        run_stage1 ops cfg pd policy rest (i+1) fuel' ({s1_index=i; s1_result=Done result}::slots_rev) pending_rev'

  let rec run_stage2 ops rc cfg tr pending fuel slots_rev = match pending with
    | [] -> (List.rev slots_rev, fuel, None)
    | ps :: rest -> match charge fuel (4 * cfg.model_call_fuel) with
      | None -> (List.rev slots_rev @ stage2_not_run pending, fuel, Some CampaignFuelExhausted)
      | Some fuel' -> let result = ops.stage2_check rc cfg tr ps in
        run_stage2 ops rc cfg tr rest fuel' ({s2_index=ps.index; s2_result=Done result}::slots_rev)

  let failed check_id reason = { check_id; passed=false; reason=Some reason }
  let finish ops ac cfg stage1 context stage2 fuel clo = { stage1; context; stage2; fuel; clo; record_findings=ops.record_crosscheck ac stage1 stage2 cfg }

  let replay ops (ac : authenticated_campaign) cb cfg pd policy l0 tr =
    if List.length ac.submissions > cfg.max_candidates then
      finish ops ac cfg (stage1_not_run 0 ac.submissions) NoContextNeeded [] l0 (Some CampaignCandidateCountExceeded)
    else match run_stage1 ops cfg pd policy ac.submissions 0 l0 [] [] with
    | S1Stopped (fuel,s1,pending) -> finish ops ac cfg s1 NoContextNeeded (stage2_not_run pending) fuel (Some CampaignFuelExhausted)
    | S1Complete (fuel,s1,[]) -> finish ops ac cfg s1 NoContextNeeded [] fuel None
    | S1Complete (fuel,s1,pending) ->
      match cb with
      (* CtxNotNeeded with completed stage 1 and Pending candidates: not
         constructible from `capture`; report truthfully, no fabricated O1.
         Contrast S1Stopped above (terminal stage-1 fuel exhaustion). *)
      | CtxNotNeeded -> finish ops ac cfg s1 ContextBundleInconsistent (stage2_not_run pending) fuel (Some InconsistentContextBundle)
      | CtxUnavailable reason -> finish ops ac cfg s1 (ContextUnresolved (reason,[failed "O1" "context_unavailable"])) (stage2_not_run pending) fuel (Some (ContextObstruction reason))
      | CtxLoaded lc -> match charge fuel cfg.schedule.preflight_fuel with
        | None -> finish ops ac cfg s1 NoContextNeeded (stage2_not_run pending) fuel (Some CampaignFuelExhausted)
        | Some fuel1 -> match ops.preflight lc with
          | PreflightFail (reason,findings) -> finish ops ac cfg s1 (ContextUnresolved (reason,findings)) (stage2_not_run pending) fuel1 (Some (ContextObstruction reason))
          | PreflightOk preflight_findings -> match charge fuel1 cfg.model_call_fuel with
            | None -> finish ops ac cfg s1 NoContextNeeded (stage2_not_run pending) fuel1 (Some CampaignFuelExhausted)
            | Some fuel2 -> match lookup_unique tr {phase=ContextProbe; role=Probe; repeat=0} with
              | None -> finish ops ac cfg s1 (ContextUnresolved (RepNotReproduced,[failed "O3" "probe_missing_or_duplicate"])) (stage2_not_run pending) fuel2 (Some (ContextObstruction RepNotReproduced))
              | Some event -> match ops.eval_o3 lc event policy with
                | O3Fail findings -> finish ops ac cfg s1 (ContextUnresolved (RepNotReproduced,findings)) (stage2_not_run pending) fuel2 (Some (ContextObstruction RepNotReproduced))
                | O3Ok (rc,o3_findings) -> let (s2,fuel3,clo) = run_stage2 ops rc cfg tr pending fuel2 [] in finish ops ac cfg s1 (ContextResolved (rc,preflight_findings @ o3_findings)) s2 fuel3 clo

  let valid_witnesses slots = List.filter_map (fun slot -> match slot.s2_result with Done {verdict=ValidWitness w;_} -> Some w | _ -> None) slots
  let rec all_checked_obstructions = function
    | [] -> None
    | [{s2_index; s2_result=Done {verdict=WitnessCheckObstructed reason;_}}] -> Some (s2_index,reason,[])
    | {s2_index; s2_result=Done {verdict=WitnessCheckObstructed reason;_}} :: rest ->
      Option.map (fun (next,_,others) -> (s2_index,reason,next::others)) (all_checked_obstructions rest)
    | _ -> None
  let build body replay transcript commitment_evidence = {body; replay; transcript; commitment_evidence}
  let obligation = function RecordIntegrity _ -> "repair_record_integrity" | ValidationFuelExhausted -> "raise_campaign_validation_fuel" | TranscriptMalformed _ -> "supply_well_formed_transcript" | ContextObstruction _ -> "repair_context" | CampaignFuelExhausted -> "raise_campaign_fuel" | CampaignCandidateCountExceeded -> "reduce_candidate_count" | InconsistentContextBundle -> "reconstruct_or_supply_context_bundle" | WitnessObstruction _ -> "repair_witness_execution"
  let obstruct rr tev cev cause = Obstructed (build (ObstructedBody (cause,obligation cause,[])) (ReplayDone rr) tev cev)

  let decide _ops rr (ac : authenticated_campaign) _ti _tr tev cev = match valid_witnesses rr.stage2 with
    | primary :: others -> Inadmissible (build (InadmissibleBody (primary,List.map (fun w->w.witness_index) others,[])) (ReplayDone rr) tev cev)
    | [] -> match rr.clo with Some cause -> obstruct rr tev cev cause | None ->
      match all_checked_obstructions rr.stage2 with
      | Some (i,reason,others) -> obstruct rr tev cev (WitnessObstruction (i,reason,others))
      | None -> (match rr.context, ac.completeness with
        | ContextResolved _, Complete _ -> Underdetermined {replay_result=rr; transcript_evidence=tev}
        | _ -> Underdetermined {replay_result=rr; transcript_evidence=tev})

  let assess_validated ops ti vr src = match vr with
    | Invalid (reason,fuel,evidence) -> let cause=RecordIntegrity reason in Obstructed (build (ObstructedBody (cause,obligation cause,[])) (InvalidFuel fuel) NoTranscript evidence)
    | FuelObstructed (fuel,evidence) -> Obstructed (build (ObstructedBody (ValidationFuelExhausted,obligation ValidationFuelExhausted,[])) (InvalidFuel fuel) NoTranscript evidence)
    | Valid (ac,l0) -> let cev=AuthenticatedCommitment ac.commitment.commitment_digest in
      match src with
      | OfflineParse (Malformed (reason,wire_digest),_) -> let cause=TranscriptMalformed (reason,wire_digest) in Obstructed (build (ObstructedBody (cause,obligation cause,[])) (InvalidFuel l0) (MalformedTranscript (reason,wire_digest)) cev)
      | LiveTranscript (tr,cb) -> let rr=replay ops ac cb ti.config ti.policy_document ti.policy l0 tr in decide ops rr ac ti tr (LiveCapture (ops.transcript_digest tr)) cev
      | OfflineParse (Wellformed (tr,wire_digest),cb) -> let rr=replay ops ac cb ti.config ti.policy_document ti.policy l0 tr in decide ops rr ac ti tr (OfflineTranscript (ops.transcript_digest tr,wire_digest)) cev

  let verdict_of = function Inadmissible _ -> INADMISSIBLE | Exact _ -> EXACT | Obstructed _ -> OBSTRUCTED | Underdetermined _ -> UNDERDETERMINED
end

