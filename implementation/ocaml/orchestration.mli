(* Historical NON-NORMATIVE demo interface; excluded from make check/release.
   Its machine integers and reduced records have no correspondence proof. *)
type digest = string
type bytes = string
type policy_document = string
type policy = string

type integrity_reason =
  | BadCommitmentEncoding of string | SignerNotAuthorised | SignatureInvalid
  | ManifestPolicyMismatch | ManifestAuditInstanceMismatch
  | ManifestContextMismatch | LedgerMismatch of int
  | RecordIdentityMismatch of string | CompletenessMalformed

type ctx_reason = ArtifactMismatch | SpecMismatch | RepNotReproduced
  (* O1/O2/O3 outcomes only; shared by CtxUnavailable / PreflightFail / O3 *)
type o_reason = ExecMissing | ExecInputMismatch | ExecFailure
              | ExecFuelExhausted | NonDeterministic | ObsOutOfRange
type c_reason = InputsEqual | XNotInDomain | YNotInDomain
              | QuantisedObservationsDiffer | TargetsAgree
type b_reason = BundleLimitExceeded | InvalidUtf8 | MalformedStructure
              | DuplicateKeys | SchemaUnrecognised | SchemaVersionMismatch
              | UnknownCriticalField | OverrideField | PolicyHashMismatch
              | InputStructureError | MalformedIntegerLiteral

type finding = { check_id : string; passed : bool; reason : string option }
type fuel_ledger = { budget : int; consumed : int }
type fuel_schedule = {
  commitment_parse_fuel : int; signature_verify_fuel : int;
  manifest_bind_fuel : int; record_bind_fuel : int; preflight_fuel : int;
  stage1_base_fuel : int; stage1_per_byte_fuel : int
}
type trust_anchor = { authorised_signers : string list; keys : (string * bytes) list }
type verifier_config = {
  max_candidates : int; max_wire_bytes : int; max_transcript_bytes : int;
  max_fuel : int; model_call_fuel : int; max_fuel_per_candidate : int;
  schedule : fuel_schedule; config_trust_anchor : trust_anchor
}
type candidate_submission = { wire : bytes; wire_length : int; digest : digest }
type parsed_candidate = { x : int list; y : int list }
type pending_submission = {
  index : int; submission_digest : digest; semantic_digest : digest;
  candidate : parsed_candidate; stage1_findings : finding list
}
type stage1_verdict = Rejected of b_reason | NotAWitness1 of c_reason
                    | Pending of pending_submission
type stage1_result = { index : int; verdict : stage1_verdict; findings : finding list }
type witness_data = { witness_index : int; witness_findings : finding list }
type stage2_verdict = WitnessCheckObstructed of o_reason
                    | NotAWitness2 of c_reason | ValidWitness of witness_data
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
type authenticated_campaign = {
  commitment : manifest_commitment; manifest : manifest;
  submissions : candidate_submission list; record : campaign_record;
  completeness : completeness_status
}
type loaded_context = { descriptor : digest; context_token : string }
type resolved_context = { policy : policy; context_token : string; descriptor : digest }
type context_bundle = CtxNotNeeded | CtxUnavailable of ctx_reason
                    | CtxLoaded of loaded_context
type context_state = NoContextNeeded
                   | ContextUnresolved of ctx_reason * finding list
                   | ContextResolved of resolved_context * finding list
                   | ContextBundleInconsistent
type campaign_obstruction = RecordIntegrity of integrity_reason
  | ValidationFuelExhausted | TranscriptMalformed of string * digest
  | ContextObstruction of ctx_reason | CampaignFuelExhausted
  | CampaignCandidateCountExceeded
  | InconsistentContextBundle
  | WitnessObstruction of int * o_reason * int list
type commitment_evidence = UnparsedCommitment of manifest_commitment_wire
                         | ParsedCommitment of digest
                         | AuthenticatedCommitment of digest
type transcript_evidence = NoTranscript | MalformedTranscript of string * digest
                         | LiveCapture of digest | OfflineTranscript of digest * digest
type 'a slot = Done of 'a | NotRun
type stage1_slot = { s1_index : int; s1_result : stage1_result slot }
type stage2_slot = { s2_index : int; s2_result : stage2_result slot }
type replay_result = {
  stage1 : stage1_slot list; context : context_state; stage2 : stage2_slot list;
  fuel : fuel_ledger; clo : campaign_obstruction option;
  record_findings : finding list
}
type parse_result = Malformed of string * digest | Wellformed of exec_transcript * digest
type transcript_source = LiveTranscript of exec_transcript * context_bundle
                       | OfflineParse of parse_result * context_bundle
type validation_result = Invalid of integrity_reason * fuel_ledger * commitment_evidence
                       | FuelObstructed of fuel_ledger * commitment_evidence
                       | Valid of authenticated_campaign * fuel_ledger
type trusted_inputs = {
  commitment_wire : manifest_commitment_wire; manifest : manifest;
  submissions : candidate_submission list; record : campaign_record;
  completeness : completeness_status; config : verifier_config;
  policy_document : policy_document; policy : policy; policy_digest : digest
}
type preflight_result = PreflightFail of ctx_reason * finding list
                      | PreflightOk of finding list
type o3_result = O3Fail of finding list | O3Ok of resolved_context * finding list
type cert_body = InadmissibleBody of witness_data * int list * finding list
               | ExactBody of completeness_certificate
               | ObstructedBody of campaign_obstruction * string * finding list
type replay_input = InvalidFuel of fuel_ledger | ReplayDone of replay_result
type certificate = {
  body : cert_body; replay : replay_input; transcript : transcript_evidence;
  commitment_evidence : commitment_evidence
}
type campaign_report = { replay_result : replay_result; transcript_evidence : transcript_evidence }
type assessment_outcome = Inadmissible of certificate | Exact of certificate
                        | Obstructed of certificate | Underdetermined of campaign_report
type campaign_verdict = INADMISSIBLE | EXACT | UNDERDETERMINED | OBSTRUCTED
type parse_commitment_result = ParseError of string | Parsed of manifest_commitment
type primitive_ops = {
  parse_commitment : manifest_commitment_wire -> parse_commitment_result;
  signer_authorised : verifier_config -> manifest_commitment -> bool;
  signature_valid : verifier_config -> manifest_commitment -> manifest -> bool;
  manifest_policy_matches : manifest -> trusted_inputs -> bool;
  manifest_audit_matches : manifest -> trusted_inputs -> bool;
  manifest_context_matches : manifest -> trusted_inputs -> bool;
  ledger_mismatch : manifest -> candidate_submission list -> int option;
  record_identity_mismatch : campaign_record -> manifest_commitment -> manifest -> trusted_inputs -> string option;
  completeness_wellformed : completeness_status -> bool;
  stage1_check : verifier_config -> policy_document -> policy -> int -> candidate_submission -> stage1_result;
  preflight : loaded_context -> preflight_result;
  eval_o3 : loaded_context -> exec_event -> policy -> o3_result;
  stage2_check : resolved_context -> verifier_config -> exec_transcript -> pending_submission -> stage2_result;
  record_crosscheck : authenticated_campaign -> stage1_slot list -> stage2_slot list -> verifier_config -> finding list;
  transcript_digest : exec_transcript -> digest
}

val charge : fuel_ledger -> int -> fuel_ledger option
val lookup_unique : exec_transcript -> call_key -> exec_event option
val validate_campaign : primitive_ops -> trusted_inputs -> validation_result
val replay : primitive_ops -> authenticated_campaign -> context_bundle -> verifier_config -> policy_document -> policy -> fuel_ledger -> exec_transcript -> replay_result
val decide : primitive_ops -> replay_result -> authenticated_campaign -> trusted_inputs -> exec_transcript -> transcript_evidence -> commitment_evidence -> assessment_outcome
val assess_validated : primitive_ops -> trusted_inputs -> validation_result -> transcript_source -> assessment_outcome
val verdict_of : assessment_outcome -> campaign_verdict
