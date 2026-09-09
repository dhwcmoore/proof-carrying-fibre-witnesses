From Coq Require Import List Bool Arith PeanoNat String ZArith Lia.
Import ListNotations.
Open Scope string_scope.

Definition digest := string.
Definition bytes := string.
Definition policy_document := string.
Definition policy := string.

Inductive integrity_reason : Type :=
| BadCommitmentEncoding (message : string)
| SignerNotAuthorised
| SignatureInvalid
| ManifestPolicyMismatch
| ManifestAuditInstanceMismatch
| ManifestContextMismatch
| LedgerMismatch (index : nat)
| RecordIdentityMismatch (field : string)
| CompletenessMalformed.

Inductive ctx_reason : Type :=
| ArtifactMismatch | SpecMismatch | RepNotReproduced.
(* ctx_reason is the O1/O2/O3 outcome type ONLY.  It is shared by CtxUnavailable,
   PreflightFail and O3, so it must NOT gain any constructor that those steps
   cannot legitimately produce.  The CtxNotNeeded/pending inconsistency is a
   bundle-wellformedness failure, not a resolution outcome: it lives in
   context_state (ContextBundleInconsistent) and campaign_obstruction
   (InconsistentContextBundle) instead — see below and
   implementation/CONTEXT_BUNDLE_AMENDMENT.md. *)

Inductive o_reason : Type :=
| ExecMissing | ExecInputMismatch | ExecFailure | ExecFuelExhausted
| NonDeterministic | ObsOutOfRange.

Inductive c_reason : Type :=
| InputsEqual | XNotInDomain | YNotInDomain
| QuantisedObservationsDiffer | TargetsAgree.

Inductive b_reason : Type :=
| BundleLimitExceeded | InvalidUtf8 | MalformedStructure | DuplicateKeys
| SchemaUnrecognised | SchemaVersionMismatch | UnknownCriticalField
| OverrideField | PolicyHashMismatch | InputStructureError
| MalformedIntegerLiteral.

Inductive check_outcome := Pass | Fail | NotEvaluated.
Record finding := mkFinding {
  finding_check_id : string;
  finding_outcome : check_outcome;
  finding_reason : option string
}.

Record fuel_ledger := mkFuelLedger {
  fuel_budget : nat;
  fuel_consumed : nat
}.

Definition charge (l : fuel_ledger) (cost : nat) : option fuel_ledger :=
  let used := fuel_consumed l + cost in
  if Nat.leb used (fuel_budget l)
  then Some (mkFuelLedger (fuel_budget l) used)
  else None.

Record fuel_schedule := mkFuelSchedule {
  commitment_parse_fuel : nat;
  signature_verify_fuel : nat;
  manifest_bind_fuel : nat;
  record_bind_fuel : nat;
  preflight_fuel : nat;
  stage1_base_fuel : nat;
  stage1_per_byte_fuel : nat
}.

(* AUDIT_POLICY 2.4.1: the verifier's trust anchor -- a trusted input (F.3).
   Unique-key rule (2.3): [ta_authorised_signers] has no repeat and every listed
   signer has exactly one key, so [ta_key_of] is unambiguous. *)
Record trust_anchor := mkTrustAnchor {
  ta_authorised_signers : list string;
  ta_keys : list (string * bytes)   (* (signer, 32-byte Ed25519 public key) *)
}.

Fixpoint ta_key_of (keys : list (string * bytes)) (s : string) : option bytes :=
  match keys with
  | [] => None
  | (k, v) :: rest => if String.eqb k s then Some v else ta_key_of rest s
  end.

Definition signer_in (ta : trust_anchor) (s : string) : bool :=
  existsb (String.eqb s) (ta_authorised_signers ta).

Record verifier_config := mkVerifierConfig {
  max_candidates : nat;
  max_wire_bytes : nat;
  max_transcript_bytes : nat;
  max_fuel : nat;
  model_call_fuel : nat;
  max_fuel_per_candidate : nat;   (* per_candidate_limits, AUDIT_POLICY 2.2.5 / O6d *)
  schedule : fuel_schedule;
  config_trust_anchor : trust_anchor
}.

Record candidate_submission := mkCandidateSubmission {
  submission_wire : bytes;
  submission_wire_length : nat;
  submission_digest : digest
}.

Record parsed_candidate := mkParsedCandidate {
  candidate_x : list Z;
  candidate_y : list Z
}.

Record pending_submission := mkPendingSubmission {
  pending_index : nat;
  pending_submission_digest : digest;
  pending_semantic_digest : digest;
  pending_candidate : parsed_candidate;
  pending_findings : list finding
}.

Inductive stage1_verdict :=
| S1Rejected (reason : b_reason)
| S1NotAWitness (reason : c_reason)
| S1Pending (pending : pending_submission).

Record stage1_result := mkStage1Result {
  s1_index : nat;
  s1_submission_digest : digest;
  s1_verdict : stage1_verdict;
  s1_findings : list finding
}.

Record witness_data := mkWitnessData {
  witness_index : nat;
  witness_submission_digest : digest;
  witness_semantic_digest : digest;
  witness_x : list Z;
  witness_y : list Z;
  witness_o_x : list Z;
  witness_o_y : list Z;
  witness_findings : list finding
}.

Inductive stage2_verdict :=
| WitnessCheckObstructed (reason : o_reason)
| S2NotAWitness (reason : c_reason)
| ValidWitness (witness : witness_data).

Record stage2_result := mkStage2Result {
  s2_index : nat;
  s2_verdict : stage2_verdict;
  s2_findings : list finding
}.

Inductive call_phase := ContextProbe | Stage2Phase (index : nat).
Inductive call_role := Probe | XRole | YRole.
Record call_key := mkCallKey {
  key_phase : call_phase;
  key_role : call_role;
  key_repeat : nat
}.
Inductive exec_outcome :=
| ExecOk (observation : list Z)
| ExecFailed (reason : string)
| ExecExhausted.
Record exec_event := mkExecEvent {
  event_key : call_key;
  event_input : list Z;
  event_outcome : exec_outcome
}.
Definition exec_transcript := list exec_event.

Definition call_phase_eqb (x y : call_phase) : bool :=
  match x, y with
  | ContextProbe, ContextProbe => true
  | Stage2Phase i, Stage2Phase j => Nat.eqb i j
  | _, _ => false
  end.
Definition call_role_eqb (x y : call_role) : bool :=
  match x, y with
  | Probe, Probe | XRole, XRole | YRole, YRole => true
  | _, _ => false
  end.
Definition call_key_eqb (x y : call_key) : bool :=
  call_phase_eqb (key_phase x) (key_phase y) &&
  call_role_eqb (key_role x) (key_role y) &&
  Nat.eqb (key_repeat x) (key_repeat y).

Fixpoint matching_events (tr : exec_transcript) (key : call_key)
  : list exec_event :=
  match tr with
  | [] => []
  | e :: rest =>
      if call_key_eqb (event_key e) key
      then e :: matching_events rest key
      else matching_events rest key
  end.

Definition lookup_unique (tr : exec_transcript) (key : call_key)
  : option exec_event :=
  match matching_events tr key with
  | [e] => Some e
  | _ => None
  end.

Record manifest_commitment_wire := mkManifestCommitmentWire {
  cw_digest : string;      (* AUDIT_POLICY 2.4.1: 64 lowercase-hex chars *)
  cw_signer : string;
  cw_signature : string    (* 128 lowercase-hex chars *)
}.
Record manifest_commitment := mkManifestCommitment {
  commitment_digest : digest;
  commitment_signer : string;
  commitment_signature : bytes   (* AUDIT_POLICY 2.4.1: the 64 decoded signature bytes *)
}.
Record manifest := mkManifest { manifest_token : string }.
Record campaign_record := mkCampaignRecord { record_token : string }.
Record completeness_certificate := mkCompletenessCertificate {
  completeness_scheme : string;
  completeness_body : string
}.
Inductive completeness_status :=
| CompletenessUnknown
| CompletenessIncomplete
| CompletenessComplete (certificate : completeness_certificate).

Record authenticated_campaign := mkAuthenticatedCampaign {
  authenticated_commitment : manifest_commitment;
  authenticated_manifest : manifest;
  authenticated_submissions : list candidate_submission;
  authenticated_record : campaign_record;
  authenticated_completeness : completeness_status
}.

Record loaded_context := mkLoadedContext {
  loaded_descriptor : digest;
  loaded_model_bytes : bytes;
  loaded_preproc_bytes : bytes;
  loaded_inference_bytes : bytes;
  loaded_context_token : string
}.
Record resolved_context := mkResolvedContext {
  resolved_policy : policy;
  resolved_context_token : string;
  resolved_descriptor : digest
}.
Inductive context_bundle :=
| CtxNotNeeded
| CtxUnavailable (reason : ctx_reason)
| CtxLoaded (context : loaded_context).
Inductive context_state :=
| NoContextNeeded
| ContextUnresolved (reason : ctx_reason) (findings : list finding)
| ContextResolved (context : resolved_context) (findings : list finding)
| ContextBundleInconsistent.
(* ContextBundleInconsistent: cb = CtxNotNeeded supplied with a completed stage 1
   that produced Pending candidates.  Carries no reason and no findings — no
   O1/O2/O3 check ran.  Not producible by `capture`. *)

Inductive campaign_obstruction :=
| RecordIntegrity (reason : integrity_reason)
| ValidationFuelExhausted
| TranscriptMalformed (reason : string) (wire_digest : digest)
| ContextObstruction (reason : ctx_reason)
| CampaignFuelExhausted
| CampaignCandidateCountExceeded
| InconsistentContextBundle
| WitnessObstruction
    (primary_index : nat) (primary_reason : o_reason)
    (other_indices : list nat).
(* InconsistentContextBundle: nullary, parallel to CampaignFuelExhausted.  The
   CtxNotNeeded-with-pending case; distinct from ContextObstruction, which only
   carries genuine O1/O2/O3 ctx_reasons. *)

Inductive commitment_evidence :=
| UnparsedCommitment (wire : manifest_commitment_wire)
| ParsedCommitment (commitment_digest : digest)
| AuthenticatedCommitment (commitment_digest : digest).

Inductive transcript_evidence :=
| NoTranscript
| MalformedTranscript (reason : string) (wire_digest : digest)
| LiveCapture (transcript_digest : digest)
| OfflineTranscript (transcript_digest : digest) (wire_digest : digest).

Inductive slot (A : Type) := Done (value : A) | NotRun.
Arguments Done {A} _.
Arguments NotRun {A}.
Record stage1_slot := mkStage1Slot {
  stage1_slot_index : nat;
  stage1_slot_result : slot stage1_result
}.
Record stage2_slot := mkStage2Slot {
  stage2_slot_index : nat;
  stage2_slot_result : slot stage2_result
}.
Record replay_result := mkReplayResult {
  replay_stage1 : list stage1_slot;
  replay_context : context_state;
  replay_stage2 : list stage2_slot;
  replay_fuel : fuel_ledger;
  replay_clo : option campaign_obstruction;
  replay_record_findings : list finding
}.

Inductive parse_result :=
| MalformedParse (reason : string) (wire_digest : digest)
| WellformedParse (transcript : exec_transcript) (wire_digest : digest).
Inductive transcript_source :=
| LiveTranscript (transcript : exec_transcript) (bundle : context_bundle)
| OfflineParse (result : parse_result) (bundle : context_bundle).

Inductive validation_result :=
| InvalidCampaign
    (reason : integrity_reason) (fuel : fuel_ledger)
    (evidence : commitment_evidence)
| FuelObstructed
    (fuel : fuel_ledger) (evidence : commitment_evidence)
| ValidCampaign
    (campaign : authenticated_campaign) (fuel : fuel_ledger).

Record trusted_inputs := mkTrustedInputs {
  ti_commitment_wire : manifest_commitment_wire;
  ti_manifest : manifest;
  ti_submissions : list candidate_submission;
  ti_record : campaign_record;
  ti_completeness : completeness_status;
  ti_config : verifier_config;
  ti_policy_document : policy_document;
  ti_policy : policy;
  ti_policy_digest : digest
}.

Inductive parse_commitment_result :=
| CommitmentParseError (message : string)
| CommitmentParsed (commitment : manifest_commitment).
Inductive preflight_result :=
| PreflightFail (reason : ctx_reason) (findings : list finding)
| PreflightOk (findings : list finding).
Inductive o3_result :=
| O3Fail (findings : list finding)
| O3Ok (context : resolved_context) (findings : list finding).

Inductive cert_body :=
| InadmissibleBody
    (primary : witness_data) (others : list nat) (all_findings : list finding)
| ExactBody (completeness : completeness_certificate)
| ObstructedBody
    (obstruction : campaign_obstruction) (failed_obligation : string)
    (context_findings : list finding).
Inductive replay_input :=
| InvalidFuel (fuel : fuel_ledger)
| ReplayDone (replay : replay_result).
Record certificate := mkCertificate {
  certificate_body : cert_body;
  certificate_replay : replay_input;
  certificate_transcript : transcript_evidence;
  certificate_commitment : commitment_evidence
}.
Record campaign_report := mkCampaignReport {
  report_replay : replay_result;
  report_transcript : transcript_evidence
}.
Inductive assessment_outcome :=
| Inadmissible (certificate : certificate)
| Exact (certificate : certificate)
| Obstructed (certificate : certificate)
| Underdetermined (report : campaign_report).
Inductive campaign_verdict :=
| INADMISSIBLE | EXACT | UNDERDETERMINED | OBSTRUCTED.
Definition verdict_of (outcome : assessment_outcome) : campaign_verdict :=
  match outcome with
  | Inadmissible _ => INADMISSIBLE
  | Exact _ => EXACT
  | Obstructed _ => OBSTRUCTED
  | Underdetermined _ => UNDERDETERMINED
  end.

Record primitive_ops := mkPrimitiveOps {
  op_parse_commitment : manifest_commitment_wire -> parse_commitment_result;
  op_signer_authorised : verifier_config -> manifest_commitment -> bool;
  op_signature_valid : verifier_config -> manifest_commitment -> manifest -> bool;
  op_manifest_policy_matches : manifest -> trusted_inputs -> bool;
  op_manifest_audit_matches : manifest -> trusted_inputs -> bool;
  op_manifest_context_matches : manifest -> trusted_inputs -> bool;
  op_ledger_mismatch : manifest -> list candidate_submission -> option nat;
  op_record_identity_mismatch : campaign_record -> manifest_commitment ->
                                manifest -> trusted_inputs -> option string;
  op_completeness_wellformed : completeness_status -> bool;
  op_stage1_check : verifier_config -> policy_document -> policy -> nat ->
                    candidate_submission -> stage1_result;
  op_preflight : loaded_context -> preflight_result;
  op_eval_o3 : loaded_context -> exec_event -> policy -> o3_result;
  op_stage2_check : resolved_context -> verifier_config -> exec_transcript ->
                    pending_submission -> stage2_result;
  op_record_crosscheck : authenticated_campaign -> list stage1_slot ->
                         list stage2_slot -> verifier_config -> list finding;
  op_transcript_digest : exec_transcript -> digest
}.

Definition validation_seed (ti : trusted_inputs) : fuel_ledger :=
  mkFuelLedger (max_fuel (ti_config ti)) 0.

Definition authenticated_of
  (ti : trusted_inputs) (mc : manifest_commitment) : authenticated_campaign :=
  mkAuthenticatedCampaign mc (ti_manifest ti) (ti_submissions ti)
    (ti_record ti) (ti_completeness ti).

Definition validate_campaign (ops : primitive_ops) (ti : trusted_inputs)
  : validation_result :=
  let l0 := validation_seed ti in
  let fs := schedule (ti_config ti) in
  match charge l0 (commitment_parse_fuel fs) with
  | None => FuelObstructed l0 (UnparsedCommitment (ti_commitment_wire ti))
  | Some l1 =>
      match op_parse_commitment ops (ti_commitment_wire ti) with
      | CommitmentParseError msg =>
          InvalidCampaign (BadCommitmentEncoding msg) l1
            (UnparsedCommitment (ti_commitment_wire ti))
      | CommitmentParsed mc =>
          let parsed := ParsedCommitment (commitment_digest mc) in
          if negb (op_signer_authorised ops (ti_config ti) mc) then
            InvalidCampaign SignerNotAuthorised l1 parsed
          else
            match charge l1 (signature_verify_fuel fs) with
            | None => FuelObstructed l1 parsed
            | Some l2 =>
                if negb (op_signature_valid ops (ti_config ti) mc (ti_manifest ti)) then
                  InvalidCampaign SignatureInvalid l2 parsed
                else
                  let auth := AuthenticatedCommitment (commitment_digest mc) in
                  match charge l2 (manifest_bind_fuel fs) with
                  | None => FuelObstructed l2 auth
                  | Some l3 =>
                      if negb (op_manifest_policy_matches ops (ti_manifest ti) ti) then
                        InvalidCampaign ManifestPolicyMismatch l3 auth
                      else if negb (op_manifest_audit_matches ops (ti_manifest ti) ti) then
                        InvalidCampaign ManifestAuditInstanceMismatch l3 auth
                      else if negb (op_manifest_context_matches ops (ti_manifest ti) ti) then
                        InvalidCampaign ManifestContextMismatch l3 auth
                      else
                        match charge l3 (record_bind_fuel fs) with
                        | None => FuelObstructed l3 auth
                        | Some l4 =>
                            match op_ledger_mismatch ops (ti_manifest ti)
                                    (ti_submissions ti) with
                            | Some i => InvalidCampaign (LedgerMismatch i) l4 auth
                            | None =>
                                match op_record_identity_mismatch ops (ti_record ti)
                                        mc (ti_manifest ti) ti with
                                | Some field =>
                                    InvalidCampaign (RecordIdentityMismatch field) l4 auth
                                | None =>
                                    if negb (op_completeness_wellformed ops
                                              (ti_completeness ti)) then
                                      InvalidCampaign CompletenessMalformed l4 auth
                                    else
                                      ValidCampaign (authenticated_of ti mc) l4
                                end
                            end
                        end
                  end
            end
      end
  end.

Definition stage1_cost (cfg : verifier_config) (sub : candidate_submission) : nat :=
  let fs := schedule cfg in
  stage1_base_fuel fs +
  stage1_per_byte_fuel fs * Nat.min (submission_wire_length sub)
                                      (S (max_wire_bytes cfg)).

Fixpoint indexed_stage1_not_run (i : nat) (subs : list candidate_submission)
  : list stage1_slot :=
  match subs with
  | [] => []
  | _ :: rest => mkStage1Slot i NotRun :: indexed_stage1_not_run (S i) rest
  end.

Definition pending_of_stage1 (r : stage1_result) : option pending_submission :=
  match s1_verdict r with S1Pending p => Some p | _ => None end.

(* Orchestration owns the pending index: it is the position `i` at which the
   submission was checked, not a value trusted from `op_stage1_check`.  This
   makes index correctness a property of construction (see
   run_stage1_pending_nodup). *)
Definition with_pending_index (i : nat) (ps : pending_submission)
  : pending_submission :=
  mkPendingSubmission i (pending_submission_digest ps) (pending_semantic_digest ps)
    (pending_candidate ps) (pending_findings ps).

Inductive stage1_run :=
| Stage1Complete
    (fuel : fuel_ledger) (slots : list stage1_slot)
    (pending : list pending_submission)
| Stage1Stopped
    (fuel : fuel_ledger) (slots : list stage1_slot)
    (pending : list pending_submission).

Definition stage1_run_pending (r : stage1_run) : list pending_submission :=
  match r with
  | Stage1Complete _ _ pending => pending
  | Stage1Stopped _ _ pending => pending
  end.

Fixpoint run_stage1
  (ops : primitive_ops) (cfg : verifier_config) (pd : policy_document)
  (p : policy) (subs : list candidate_submission) (i : nat)
  (fuel : fuel_ledger) (slots_rev : list stage1_slot)
  (pending_rev : list pending_submission) : stage1_run :=
  match subs with
  | [] => Stage1Complete fuel (rev slots_rev) (rev pending_rev)
  | sub :: rest =>
      match charge fuel (stage1_cost cfg sub) with
      | None => Stage1Stopped fuel
          (rev slots_rev ++ indexed_stage1_not_run i subs) (rev pending_rev)
      | Some fuel' =>
          let r := op_stage1_check ops cfg pd p i sub in
          let pending_rev' :=
            match pending_of_stage1 r with
            | Some candidate => with_pending_index i candidate :: pending_rev
            | None => pending_rev
            end in
          run_stage1 ops cfg pd p rest (S i) fuel'
            (mkStage1Slot i (Done r) :: slots_rev) pending_rev'
      end
  end.

Definition stage2_not_run (pending : list pending_submission)
  : list stage2_slot :=
  map (fun p => mkStage2Slot (pending_index p) NotRun) pending.

Fixpoint run_stage2
  (ops : primitive_ops) (rc : resolved_context) (cfg : verifier_config)
  (tr : exec_transcript) (pending : list pending_submission)
  (fuel : fuel_ledger) (slots_rev : list stage2_slot)
  : list stage2_slot * fuel_ledger * option campaign_obstruction :=
  match pending with
  | [] => (rev slots_rev, fuel, None)
  | ps :: rest =>
      match charge fuel (4 * model_call_fuel cfg) with
      | None =>
          ((rev slots_rev ++ stage2_not_run pending)%list, fuel,
           Some CampaignFuelExhausted)
      | Some fuel' =>
          let result := op_stage2_check ops rc cfg tr ps in
          run_stage2 ops rc cfg tr rest fuel'
            (mkStage2Slot (pending_index ps) (Done result) :: slots_rev)
      end
  end.

Definition failed_finding (id reason : string) : finding :=
  mkFinding id Fail (Some reason).

Definition finish_replay
  (ops : primitive_ops) (ac : authenticated_campaign) (cfg : verifier_config)
  (s1 : list stage1_slot) (ctx : context_state) (s2 : list stage2_slot)
  (fuel : fuel_ledger) (clo : option campaign_obstruction) : replay_result :=
  mkReplayResult s1 ctx s2 fuel clo
    (op_record_crosscheck ops ac s1 s2 cfg).

Definition replay
  (ops : primitive_ops) (ac : authenticated_campaign) (cb : context_bundle)
  (cfg : verifier_config) (pd : policy_document) (p : policy)
  (l0 : fuel_ledger) (tr : exec_transcript) : replay_result :=
  if Nat.ltb (max_candidates cfg) (List.length (authenticated_submissions ac)) then
    finish_replay ops ac cfg
      (indexed_stage1_not_run 0 (authenticated_submissions ac))
      NoContextNeeded [] l0 (Some CampaignCandidateCountExceeded)
  else
    match run_stage1 ops cfg pd p (authenticated_submissions ac) 0 l0 [] [] with
    | Stage1Stopped fuel s1 pending =>
        finish_replay ops ac cfg s1 NoContextNeeded (stage2_not_run pending)
          fuel (Some CampaignFuelExhausted)
    | Stage1Complete fuel s1 pending =>
        match pending with
        | [] => finish_replay ops ac cfg s1 NoContextNeeded [] fuel None
        | _ :: _ =>
            match cb with
            | CtxNotNeeded =>
                (* Stage 1 completed with Pending candidates but the bundle says
                   no context is needed.  Not constructible from `capture`; report
                   it truthfully — OBSTRUCTED, every pending stage-2 slot NotRun,
                   NO fabricated O1 finding, repair = supply/reconstruct the
                   bundle.  Contrast Stage1Stopped above (terminal stage-1 fuel
                   exhaustion), where CtxNotNeeded is legitimate even with earlier
                   Pending results. *)
                finish_replay ops ac cfg s1
                  ContextBundleInconsistent
                  (stage2_not_run pending) fuel
                  (Some InconsistentContextBundle)
            | CtxUnavailable reason =>
                finish_replay ops ac cfg s1
                  (ContextUnresolved reason [failed_finding "O1" "context_unavailable"])
                  (stage2_not_run pending) fuel
                  (Some (ContextObstruction reason))
            | CtxLoaded lc =>
                match charge fuel (preflight_fuel (schedule cfg)) with
                | None =>
                    finish_replay ops ac cfg s1 NoContextNeeded
                      (stage2_not_run pending) fuel (Some CampaignFuelExhausted)
                | Some fuel1 =>
                    match op_preflight ops lc with
                    | PreflightFail reason findings =>
                        finish_replay ops ac cfg s1
                          (ContextUnresolved reason findings)
                          (stage2_not_run pending) fuel1
                          (Some (ContextObstruction reason))
                    | PreflightOk preflight_findings =>
                        match charge fuel1 (model_call_fuel cfg) with
                        | None =>
                            finish_replay ops ac cfg s1 NoContextNeeded
                              (stage2_not_run pending) fuel1
                              (Some CampaignFuelExhausted)
                        | Some fuel2 =>
                            let probe := mkCallKey ContextProbe Probe 0 in
                            match lookup_unique tr probe with
                            | None =>
                                finish_replay ops ac cfg s1
                                  (ContextUnresolved RepNotReproduced
                                    [failed_finding "O3" "probe_missing_or_duplicate"])
                                  (stage2_not_run pending) fuel2
                                  (Some (ContextObstruction RepNotReproduced))
                            | Some event =>
                                match op_eval_o3 ops lc event p with
                                | O3Fail findings =>
                                    finish_replay ops ac cfg s1
                                      (ContextUnresolved RepNotReproduced findings)
                                      (stage2_not_run pending) fuel2
                                      (Some (ContextObstruction RepNotReproduced))
                                | O3Ok rc o3_findings =>
                                    let '(s2, fuel3, clo) :=
                                      run_stage2 ops rc cfg tr pending fuel2 [] in
                                    finish_replay ops ac cfg s1
                                      (ContextResolved rc
                                        (preflight_findings ++ o3_findings))
                                      s2 fuel3 clo
                                end
                            end
                        end
                    end
                end
            end
        end
    end.

Fixpoint valid_witnesses (slots : list stage2_slot) : list witness_data :=
  match slots with
  | [] => []
  | slot0 :: rest =>
      match stage2_slot_result slot0 with
      | Done result =>
          match s2_verdict result with
          | ValidWitness witness => witness :: valid_witnesses rest
          | _ => valid_witnesses rest
          end
      | NotRun => valid_witnesses rest
      end
  end.

Fixpoint all_checked_obstructions (slots : list stage2_slot)
  : option (nat * o_reason * list nat) :=
  match slots with
  | [] => None
  | slot0 :: rest =>
      match stage2_slot_result slot0 with
      | Done result =>
          match s2_verdict result with
          | WitnessCheckObstructed reason =>
              match rest with
              | [] => Some (stage2_slot_index slot0, reason, [])
              | _ =>
                  match all_checked_obstructions rest with
                  | Some (primary, primary_reason, others) =>
                      Some (stage2_slot_index slot0, reason, primary :: others)
                  | None => None
                  end
              end
          | _ => None
          end
      | NotRun => None
      end
  end.

Definition valid_completeness_certificate_v0
  (_ : resolved_context) (_ : completeness_certificate) : bool := false.

Definition build_certificate
  (body : cert_body) (input : replay_input) (tev : transcript_evidence)
  (cev : commitment_evidence) : certificate :=
  mkCertificate body input tev cev.

Definition obstruction_obligation (obstruction : campaign_obstruction) : string :=
  match obstruction with
  | RecordIntegrity _ => "repair_record_integrity"
  | ValidationFuelExhausted => "raise_campaign_validation_fuel"
  | TranscriptMalformed _ _ => "supply_well_formed_transcript"
  | ContextObstruction _ => "repair_context"
  | CampaignFuelExhausted => "raise_campaign_fuel"
  | CampaignCandidateCountExceeded => "reduce_candidate_count"
  | InconsistentContextBundle => "reconstruct_or_supply_context_bundle"
  | WitnessObstruction _ _ _ => "repair_witness_execution"
  end.

Definition decide
  (_ops : primitive_ops) (rr : replay_result) (ac : authenticated_campaign)
  (_ti : trusted_inputs) (_tr : exec_transcript) (tev : transcript_evidence)
  (cev : commitment_evidence) : assessment_outcome :=
  match valid_witnesses (replay_stage2 rr) with
  | primary :: others =>
      Inadmissible (build_certificate
        (InadmissibleBody primary (map witness_index others) [])
        (ReplayDone rr) tev cev)
  | [] =>
      match replay_clo rr with
      | Some obstruction =>
          Obstructed (build_certificate
            (ObstructedBody obstruction (obstruction_obligation obstruction) [])
            (ReplayDone rr) tev cev)
      | None =>
          match all_checked_obstructions (replay_stage2 rr) with
          | Some (primary, reason, others) =>
              let obstruction := WitnessObstruction primary reason others in
              Obstructed (build_certificate
                (ObstructedBody obstruction
                  (obstruction_obligation obstruction) [])
                (ReplayDone rr) tev cev)
          | None =>
              match replay_context rr, authenticated_completeness ac with
              | ContextResolved rc _, CompletenessComplete cert =>
                  if valid_completeness_certificate_v0 rc cert then
                    Exact (build_certificate (ExactBody cert)
                      (ReplayDone rr) tev cev)
                  else Underdetermined (mkCampaignReport rr tev)
              | _, _ => Underdetermined (mkCampaignReport rr tev)
              end
          end
      end
  end.

Definition assess_validated
  (ops : primitive_ops) (ti : trusted_inputs) (vr : validation_result)
  (src : transcript_source) : assessment_outcome :=
  match vr with
  | InvalidCampaign reason fuel evidence =>
      let obstruction := RecordIntegrity reason in
      Obstructed (build_certificate
        (ObstructedBody obstruction (obstruction_obligation obstruction) [])
        (InvalidFuel fuel) NoTranscript evidence)
  | FuelObstructed fuel evidence =>
      Obstructed (build_certificate
        (ObstructedBody ValidationFuelExhausted
          (obstruction_obligation ValidationFuelExhausted) [])
        (InvalidFuel fuel) NoTranscript evidence)
  | ValidCampaign ac l0 =>
      let cev := AuthenticatedCommitment
                   (commitment_digest (authenticated_commitment ac)) in
      match src with
      | OfflineParse (MalformedParse reason wire_digest) _ =>
          let obstruction := TranscriptMalformed reason wire_digest in
          Obstructed (build_certificate
            (ObstructedBody obstruction (obstruction_obligation obstruction) [])
            (InvalidFuel l0) (MalformedTranscript reason wire_digest) cev)
      | LiveTranscript tr cb =>
          let rr := replay ops ac cb (ti_config ti) (ti_policy_document ti)
                           (ti_policy ti) l0 tr in
          decide ops rr ac ti tr
            (LiveCapture (op_transcript_digest ops tr)) cev
      | OfflineParse (WellformedParse tr wire_digest) cb =>
          let rr := replay ops ac cb (ti_config ti) (ti_policy_document ti)
                           (ti_policy ti) l0 tr in
          decide ops rr ac ti tr
            (OfflineTranscript (op_transcript_digest ops tr) wire_digest) cev
      end
  end.

(* Named Phase 1 proof obligations. *)
Definition source_ready (src : transcript_source)
  : option (exec_transcript * context_bundle) :=
  match src with
  | LiveTranscript tr cb => Some (tr, cb)
  | OfflineParse (WellformedParse tr _) cb => Some (tr, cb)
  | OfflineParse (MalformedParse _ _) _ => None
  end.

Lemma decide_inadmissible_iff_witness :
  forall ops rr ac ti tr tev cev,
    verdict_of (decide ops rr ac ti tr tev cev) = INADMISSIBLE <->
    exists w, In w (valid_witnesses (replay_stage2 rr)).
Proof.
  intros ops rr ac ti tr tev cev. unfold decide.
  destruct (valid_witnesses (replay_stage2 rr)) as [|w ws] eqn:Hws.
  - split.
    + intros H.
      repeat match type of H with
      | context [match ?x with _ => _ end] => destruct x eqn:?; simpl in H
      end; discriminate.
    + intros [w H]. inversion H.
  - simpl. split.
    + intros _. exists w. left. reflexivity.
    + intros _. reflexivity.
Qed.

Theorem T2_sound :
  forall ops ti vr src,
    verdict_of (assess_validated ops ti vr src) = INADMISSIBLE ->
    exists ac l0 tr cb witness,
      vr = ValidCampaign ac l0 /\
      source_ready src = Some (tr, cb) /\
      In witness
        (valid_witnesses
          (replay_stage2
            (replay ops ac cb (ti_config ti) (ti_policy_document ti)
              (ti_policy ti) l0 tr))).
Proof.
  intros ops ti vr src H.
  destruct vr as [reason fuel evidence | fuel evidence | ac l0];
    cbn [assess_validated verdict_of] in H; try discriminate.
  destruct src as [tr cb | pr cb].
  - cbn [assess_validated] in H.
    apply decide_inadmissible_iff_witness in H.
    destruct H as [w Hw]. exists ac, l0, tr, cb, w.
    repeat split; assumption || reflexivity.
  - destruct pr as [reason wire_digest | tr wire_digest];
      cbn [assess_validated verdict_of] in H; try discriminate.
    apply decide_inadmissible_iff_witness in H.
    destruct H as [w Hw]. exists ac, l0, tr, cb, w.
    repeat split; assumption || reflexivity.
Qed.

Theorem T2_complete :
  forall ops ti vr src ac l0 tr cb witness,
    vr = ValidCampaign ac l0 ->
    source_ready src = Some (tr, cb) ->
    In witness
      (valid_witnesses
        (replay_stage2
          (replay ops ac cb (ti_config ti) (ti_policy_document ti)
             (ti_policy ti) l0 tr))) ->
    verdict_of
      (assess_validated ops ti vr src) = INADMISSIBLE.
Proof.
  intros ops ti vr src ac l0 tr cb witness Hvr Hsrc Hw. subst vr.
  destruct src as [tr' cb' | pr cb'];
    [| destruct pr as [reason wire_digest | tr' wire_digest]];
    cbn [source_ready] in Hsrc; try discriminate;
    inversion Hsrc; subst;
    cbn [assess_validated];
    apply decide_inadmissible_iff_witness; exists witness; exact Hw.
Qed.

Theorem stage1_over_is_terminal :
  forall ops ac cb cfg pd p l0 tr fuel' out_slots out_pending,
    List.length (authenticated_submissions ac) <= max_candidates cfg ->
    run_stage1 ops cfg pd p (authenticated_submissions ac) 0 l0 [] [] =
      Stage1Stopped fuel' out_slots out_pending ->
    replay_context (replay ops ac cb cfg pd p l0 tr) = NoContextNeeded /\
    replay_clo (replay ops ac cb cfg pd p l0 tr) =
      Some CampaignFuelExhausted.
Proof.
  intros ops ac cb cfg pd p l0 tr fuel' out_slots out_pending Hcount Hrun.
  unfold replay.
  assert (Hlimit : Nat.ltb (max_candidates cfg)
      (List.length (authenticated_submissions ac)) = false).
  { apply Nat.ltb_ge. exact Hcount. }
  rewrite Hlimit, Hrun. split; reflexivity.
Qed.

(* ---- Repaired (REP1): the original statement quantified over an arbitrary
   [list stage2_slot] and was FALSE (e.g. [mkStage2Slot 0 NotRun; mkStage2Slot 0
   (Done r)] with r a ValidWitness of index 0).  It is restated for slot lists
   that are well formed in the sense a genuine `replay` output is: distinct slot
   indices, and every ValidWitness slot carrying a witness whose index is its
   own slot index.  `replay_stage2_wf` discharges that predicate for every
   `replay` output, given the stage-2 witness-index contract on the primitive. *)

Definition stage2_witness_index_contract (ops : primitive_ops) : Prop :=
  forall rc cfg tr ps w,
    s2_verdict (op_stage2_check ops rc cfg tr ps) = ValidWitness w ->
    witness_index w = pending_index ps.

Definition stage2_index_consistent (slots : list stage2_slot) : Prop :=
  forall s result w,
    In s slots ->
    stage2_slot_result s = Done result ->
    s2_verdict result = ValidWitness w ->
    witness_index w = stage2_slot_index s.

Definition stage2_slots_wf (slots : list stage2_slot) : Prop :=
  NoDup (map stage2_slot_index slots) /\ stage2_index_consistent slots.

Lemma nodup_map_inj :
  forall {A B} (f : A -> B) (l : list A) x y,
    NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  intros A B f l x y Hnd Hx Hy Hfxy.
  induction l as [| a rest IH]; simpl in *.
  - contradiction.
  - inversion Hnd as [| ? ? Hnotin Hnd']; subst.
    destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
    + reflexivity.
    + exfalso. apply Hnotin. rewrite Hfxy. apply in_map. exact Hy.
    + exfalso. apply Hnotin. rewrite <- Hfxy. apply in_map. exact Hx.
    + apply IH; assumption.
Qed.

Fixpoint strict_inc (l : list nat) : Prop :=
  match l with
  | [] => True
  | x :: rest => (forall y, In y rest -> x < y) /\ strict_inc rest
  end.

Lemma map_rev_cons :
  forall {A B} (f : A -> B) (x : A) (l : list A),
    map f (rev (x :: l)) = (map f (rev l) ++ [f x])%list.
Proof. intros. simpl. rewrite map_app. reflexivity. Qed.

Lemma strict_inc_NoDup : forall l, strict_inc l -> NoDup l.
Proof.
  induction l as [| x rest IH]; simpl; intros H.
  - constructor.
  - destruct H as [Hlt Hrest]. constructor.
    + intros Hin. specialize (Hlt x Hin). lia.
    + apply IH. exact Hrest.
Qed.

Lemma strict_inc_snoc :
  forall l v, strict_inc l -> (forall y, In y l -> y < v) ->
    strict_inc (l ++ [v])%list.
Proof.
  induction l as [| x rest IH]; simpl; intros v H Hlt.
  - split; [intros y Hy; destruct Hy | exact I].
  - destruct H as [Hx Hrest]. split.
    + intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy | Hy].
      * apply Hx. exact Hy.
      * simpl in Hy. destruct Hy as [<- | []]. apply Hlt. left. reflexivity.
    + apply IH. exact Hrest. intros y Hy. apply Hlt. right. exact Hy.
Qed.

Lemma run_stage1_strict_inc :
  forall subs ops cfg pd p i fuel slots_rev pending_rev,
    strict_inc (map pending_index (rev pending_rev)) ->
    (forall q, In q pending_rev -> pending_index q < i) ->
    strict_inc (map pending_index
      (stage1_run_pending
        (run_stage1 ops cfg pd p subs i fuel slots_rev pending_rev))).
Proof.
  induction subs as [| sub rest IH];
    intros ops cfg pd p i fuel slots_rev pending_rev Hsi Hlt.
  - simpl. exact Hsi.
  - simpl. destruct (charge fuel (stage1_cost cfg sub)) as [fuel' |] eqn:Hc.
    + destruct (pending_of_stage1 (op_stage1_check ops cfg pd p i sub))
        as [cand |] eqn:Hp.
      * apply IH.
        -- rewrite map_rev_cons. simpl.
           apply strict_inc_snoc.
           ++ exact Hsi.
           ++ intros y Hy. apply in_map_iff in Hy.
              destruct Hy as [q [<- Hq]]. apply Hlt.
              apply in_rev in Hq. exact Hq.
        -- intros q Hq. simpl in Hq. destruct Hq as [<- | Hq].
           ++ simpl. lia.
           ++ specialize (Hlt q Hq). lia.
      * apply IH.
        -- exact Hsi.
        -- intros q Hq. specialize (Hlt q Hq). lia.
    + simpl. exact Hsi.
Qed.

Lemma run_stage1_pending_nodup :
  forall ops cfg pd p subs l0,
    NoDup (map pending_index
      (stage1_run_pending (run_stage1 ops cfg pd p subs 0 l0 [] []))).
Proof.
  intros. apply strict_inc_NoDup. apply run_stage1_strict_inc.
  - simpl. exact I.
  - intros q Hq. destruct Hq.
Qed.

Lemma map_index_stage2_not_run :
  forall pending,
    map stage2_slot_index (stage2_not_run pending) = map pending_index pending.
Proof.
  intros. unfold stage2_not_run. rewrite map_map. reflexivity.
Qed.

Lemma stage2_not_run_all_notrun :
  forall pending s, In s (stage2_not_run pending) -> stage2_slot_result s = NotRun.
Proof.
  intros pending s Hin. unfold stage2_not_run in Hin.
  apply in_map_iff in Hin. destruct Hin as [q [<- _]]. reflexivity.
Qed.

Lemma nil_wf : stage2_slots_wf [].
Proof.
  split.
  - constructor.
  - intros s result w Hin _ _. destruct Hin.
Qed.

Lemma stage2_not_run_wf :
  forall pending,
    NoDup (map pending_index pending) -> stage2_slots_wf (stage2_not_run pending).
Proof.
  intros pending H. split.
  - rewrite map_index_stage2_not_run. exact H.
  - intros s result w Hin Hres _.
    apply stage2_not_run_all_notrun in Hin. rewrite Hin in Hres. discriminate.
Qed.

Lemma run_stage2_index_map :
  forall pending ops rc cfg tr fuel slots_rev s2 f c,
    run_stage2 ops rc cfg tr pending fuel slots_rev = (s2, f, c) ->
    map stage2_slot_index s2
    = (map stage2_slot_index (rev slots_rev) ++ map pending_index pending)%list.
Proof.
  induction pending as [| ps rest IH];
    intros ops rc cfg tr fuel slots_rev s2 f c Hrun.
  - cbn [run_stage2] in Hrun. inversion Hrun; subst. rewrite app_nil_r. reflexivity.
  - cbn [run_stage2] in Hrun.
    destruct (charge fuel (4 * model_call_fuel cfg)) as [fuel' |] eqn:Hc.
    + apply IH in Hrun. rewrite Hrun. rewrite map_rev_cons. simpl.
      rewrite <- app_assoc. reflexivity.
    + inversion Hrun; subst. rewrite map_app. simpl.
      rewrite map_index_stage2_not_run. reflexivity.
Qed.

Lemma run_stage2_done_slots :
  forall pending ops rc cfg tr fuel slots_rev s2 f c s result,
    run_stage2 ops rc cfg tr pending fuel slots_rev = (s2, f, c) ->
    In s s2 ->
    stage2_slot_result s = Done result ->
    In s (rev slots_rev) \/
    exists ps, stage2_slot_index s = pending_index ps
               /\ result = op_stage2_check ops rc cfg tr ps.
Proof.
  induction pending as [| ps0 rest IH];
    intros ops rc cfg tr fuel slots_rev s2 f c s result Hrun Hin Hres.
  - cbn [run_stage2] in Hrun. inversion Hrun; subst. left. exact Hin.
  - cbn [run_stage2] in Hrun.
    destruct (charge fuel (4 * model_call_fuel cfg)) as [fuel' |] eqn:Hc.
    + specialize (IH ops rc cfg tr fuel'
        (mkStage2Slot (pending_index ps0)
          (Done (op_stage2_check ops rc cfg tr ps0)) :: slots_rev)
        s2 f c s result Hrun Hin Hres).
      destruct IH as [Hleft | Hright].
      * simpl in Hleft. rewrite in_app_iff in Hleft. simpl in Hleft.
        destruct Hleft as [Hleft | [Heq | []]].
        -- left. exact Hleft.
        -- right. exists ps0. subst s. simpl in Hres. simpl.
           split; [reflexivity |]. injection Hres. intros Hr. symmetry. exact Hr.
      * right. exact Hright.
    + inversion Hrun; subst.
      rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
      * left. exact Hin.
      * simpl in Hin. destruct Hin as [Heq | Hin].
        -- subst s. simpl in Hres. discriminate.
        -- apply stage2_not_run_all_notrun in Hin. rewrite Hin in Hres. discriminate.
Qed.

Lemma run_stage2_wf :
  forall pending ops rc cfg tr fuel s2 f c,
    stage2_witness_index_contract ops ->
    NoDup (map pending_index pending) ->
    run_stage2 ops rc cfg tr pending fuel [] = (s2, f, c) ->
    stage2_slots_wf s2.
Proof.
  intros pending ops rc cfg tr fuel s2 f c Hcontract Hnd Hrun. split.
  - pose proof (run_stage2_index_map pending ops rc cfg tr fuel [] s2 f c Hrun)
      as Hmap.
    simpl in Hmap. rewrite Hmap. exact Hnd.
  - intros s result w Hin Hres Hverd.
    pose proof (run_stage2_done_slots pending ops rc cfg tr fuel [] s2 f c s result
      Hrun Hin Hres) as Hds.
    simpl in Hds. destruct Hds as [Hnil | [ps [Hidx Hresq]]].
    + destruct Hnil.
    + rewrite Hresq in Hverd.
      specialize (Hcontract rc cfg tr ps w Hverd).
      rewrite Hidx. exact Hcontract.
Qed.

Lemma replay_stage2_finish :
  forall ops ac cfg s1 ctx s2 fuel clo,
    replay_stage2 (finish_replay ops ac cfg s1 ctx s2 fuel clo) = s2.
Proof. reflexivity. Qed.

Theorem replay_stage2_wf :
  forall ops ac cb cfg pd p l0 tr,
    stage2_witness_index_contract ops ->
    stage2_slots_wf (replay_stage2 (replay ops ac cb cfg pd p l0 tr)).
Proof.
  intros ops ac cb cfg pd p l0 tr Hcontract. unfold replay.
  destruct (Nat.ltb (max_candidates cfg)
             (List.length (authenticated_submissions ac))) eqn:Hlt.
  - rewrite replay_stage2_finish. apply nil_wf.
  - pose proof (run_stage1_pending_nodup ops cfg pd p
      (authenticated_submissions ac) l0) as HN.
    destruct (run_stage1 ops cfg pd p (authenticated_submissions ac) 0 l0 [] [])
      as [fuel s1 pending | fuel s1 pending] eqn:Hrun;
      cbn [stage1_run_pending] in HN.
    + (* Stage1Complete *)
      destruct pending as [| ps0 pend'].
      * rewrite replay_stage2_finish. apply nil_wf.
      * destruct cb as [| rn | lc].
        -- rewrite replay_stage2_finish. apply stage2_not_run_wf. exact HN.
        -- rewrite replay_stage2_finish. apply stage2_not_run_wf. exact HN.
        -- destruct (charge fuel (preflight_fuel (schedule cfg))) as [fuel1 |] eqn:Hpf.
           ++ destruct (op_preflight ops lc) as [rn fs | pf] eqn:Hpre.
              ** rewrite replay_stage2_finish. apply stage2_not_run_wf. exact HN.
              ** destruct (charge fuel1 (model_call_fuel cfg)) as [fuel2 |] eqn:Hmc.
                 --- destruct (lookup_unique tr (mkCallKey ContextProbe Probe 0))
                       as [ev |] eqn:Hlu.
                     +++ destruct (op_eval_o3 ops lc ev p) as [fs | rc o3f] eqn:Ho3.
                         *** rewrite replay_stage2_finish.
                             apply stage2_not_run_wf. exact HN.
                         *** destruct (run_stage2 ops rc cfg tr (ps0 :: pend') fuel2 [])
                               as [[s2 f2] c2] eqn:Hs2.
                             rewrite replay_stage2_finish.
                             eapply run_stage2_wf;
                               [ exact Hcontract | exact HN | exact Hs2 ].
                     +++ rewrite replay_stage2_finish.
                         apply stage2_not_run_wf. exact HN.
                 --- rewrite replay_stage2_finish. apply stage2_not_run_wf. exact HN.
           ++ rewrite replay_stage2_finish. apply stage2_not_run_wf. exact HN.
    + (* Stage1Stopped *)
      rewrite replay_stage2_finish. apply stage2_not_run_wf. exact HN.
Qed.

Lemma valid_witnesses_source :
  forall slots w,
    In w (valid_witnesses slots) ->
    exists s, In s slots /\ exists result,
      stage2_slot_result s = Done result /\ s2_verdict result = ValidWitness w.
Proof.
  induction slots as [| s0 rest IH]; simpl; intros w H.
  - destruct H.
  - destruct (stage2_slot_result s0) as [result |] eqn:Hr.
    + destruct (s2_verdict result) eqn:Hv.
      * destruct (IH w H) as [s [Hs Hex]]. exists s. split; [right; exact Hs | exact Hex].
      * destruct (IH w H) as [s [Hs Hex]]. exists s. split; [right; exact Hs | exact Hex].
      * simpl in H. destruct H as [Heq | H].
        -- exists s0. split; [left; reflexivity |].
           exists result. split; [exact Hr |]. rewrite Hv, Heq. reflexivity.
        -- destruct (IH w H) as [s [Hs Hex]].
           exists s. split; [right; exact Hs | exact Hex].
    + destruct (IH w H) as [s [Hs Hex]]. exists s. split; [right; exact Hs | exact Hex].
Qed.

Theorem REP1_not_run_has_no_witness :
  forall slots i,
    stage2_slots_wf slots ->
    In (mkStage2Slot i NotRun) slots ->
    ~ exists witness,
        In witness (valid_witnesses slots) /\ witness_index witness = i.
Proof.
  intros slots i [Hnd Hcons] Hin [w [Hinw Hidx]].
  apply valid_witnesses_source in Hinw.
  destruct Hinw as [s [Hs_in [result [Hs_res Hs_verd]]]].
  specialize (Hcons s result w Hs_in Hs_res Hs_verd).
  assert (Hidxs : stage2_slot_index s = i) by (rewrite <- Hcons; exact Hidx).
  assert (Heq : stage2_slot_index (mkStage2Slot i NotRun) = stage2_slot_index s)
    by (simpl; rewrite Hidxs; reflexivity).
  pose proof (nodup_map_inj stage2_slot_index slots (mkStage2Slot i NotRun) s
                Hnd Hin Hs_in Heq) as Hss.
  rewrite <- Hss in Hs_res. simpl in Hs_res. discriminate.
Qed.

Corollary REP1_replay_not_run_has_no_witness :
  forall ops ac cb cfg pd p l0 tr i,
    stage2_witness_index_contract ops ->
    In (mkStage2Slot i NotRun)
       (replay_stage2 (replay ops ac cb cfg pd p l0 tr)) ->
    ~ exists witness,
        In witness (valid_witnesses
                     (replay_stage2 (replay ops ac cb cfg pd p l0 tr)))
        /\ witness_index witness = i.
Proof.
  intros ops ac cb cfg pd p l0 tr i Hcontract Hin.
  apply REP1_not_run_has_no_witness; [| exact Hin ].
  apply replay_stage2_wf. exact Hcontract.
Qed.

Theorem exact_unreachable_v0 :
  forall ops rr ac ti tr tev cev cert,
    decide ops rr ac ti tr tev cev <> Exact cert.
Proof.
  intros ops rr ac ti tr tev cev cert. unfold decide.
  repeat match goal with
  | |- context [match ?x with _ => _ end] => destruct x eqn:?
  end; cbn [valid_completeness_certificate_v0]; discriminate.
Qed.

Lemma charge_some_ledger : forall M k c,
  k + c <= M ->
  charge (mkFuelLedger M k) c = Some (mkFuelLedger M (k + c)).
Proof.
  intros M k c H. unfold charge. cbn [fuel_consumed fuel_budget].
  apply Nat.leb_le in H. rewrite H. reflexivity.
Qed.

Theorem validation_fuel_obstructed_unreachable_when_sufficient :
  forall ops ti fuel evidence,
    max_fuel (ti_config ti) >=
      commitment_parse_fuel (schedule (ti_config ti)) +
      signature_verify_fuel (schedule (ti_config ti)) +
      manifest_bind_fuel (schedule (ti_config ti)) +
      record_bind_fuel (schedule (ti_config ti)) ->
    validate_campaign ops ti <> FuelObstructed fuel evidence.
Proof.
  intros ops ti fuel evidence Hbudget.
  set (fs := schedule (ti_config ti)) in *.
  set (M := max_fuel (ti_config ti)) in *.
  unfold validate_campaign, validation_seed. fold fs M.
  rewrite (charge_some_ledger M 0 (commitment_parse_fuel fs)) by lia; cbn match.
  destruct (op_parse_commitment ops (ti_commitment_wire ti)) as [msg | mc];
    [discriminate |].
  destruct (op_signer_authorised ops (ti_config ti) mc); cbn [negb] in *; [| discriminate].
  rewrite (charge_some_ledger M (0 + commitment_parse_fuel fs)
             (signature_verify_fuel fs)) by lia; cbn match.
  destruct (op_signature_valid ops (ti_config ti) mc (ti_manifest ti)); cbn [negb] in *;
    [| discriminate].
  rewrite (charge_some_ledger M (0 + commitment_parse_fuel fs
             + signature_verify_fuel fs) (manifest_bind_fuel fs)) by lia; cbn match.
  destruct (op_manifest_policy_matches ops (ti_manifest ti) ti); cbn [negb] in *;
    [| discriminate].
  destruct (op_manifest_audit_matches ops (ti_manifest ti) ti); cbn [negb] in *;
    [| discriminate].
  destruct (op_manifest_context_matches ops (ti_manifest ti) ti); cbn [negb] in *;
    [| discriminate].
  rewrite (charge_some_ledger M (0 + commitment_parse_fuel fs
             + signature_verify_fuel fs + manifest_bind_fuel fs)
             (record_bind_fuel fs)) by lia; cbn match.
  destruct (op_ledger_mismatch ops (ti_manifest ti) (ti_submissions ti));
    [discriminate |].
  destruct (op_record_identity_mismatch ops (ti_record ti) mc (ti_manifest ti) ti);
    [discriminate |].
  destruct (op_completeness_wellformed ops (ti_completeness ti)); cbn [negb] in *;
    discriminate.
Qed.
