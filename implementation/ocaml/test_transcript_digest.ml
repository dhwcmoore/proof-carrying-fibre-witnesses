(* Exercises the extracted op_transcript_digest interface (TranscriptDigest.v):
   set_transcript_digest, assess_validated's evidence binding, and
   outcome_transcript_evidence / typed_digest_of.

   A DETERMINISTIC MOCK digest is used throughout -- it is NOT SHA-256 and NOT
   the production digest_v1 realisation; it exists only to exercise the
   control flow this unit specifies (determinism, evidence binding,
   verdict non-interference).  No test here asserts, or relies on, different
   transcripts producing different digests. *)

module S = Extracted_transcript_digest

let sched : S.fuel_schedule =
  { S.commitment_parse_fuel = 0; S.signature_verify_fuel = 0;
    S.manifest_bind_fuel = 0; S.record_bind_fuel = 0; S.preflight_fuel = 0;
    S.stage1_base_fuel = 0; S.stage1_per_byte_fuel = 0 }

let ta : S.trust_anchor = { S.ta_authorised_signers = []; S.ta_keys = [] }

let cfg : S.verifier_config =
  { S.max_candidates = 10; S.max_wire_bytes = 100; S.max_transcript_bytes = 100;
    S.max_fuel = 1000; S.model_call_fuel = 1; S.max_fuel_per_candidate = 100;
    S.schedule = sched; S.config_trust_anchor = ta }

let mc : S.manifest_commitment =
  { S.commitment_digest = "mcd"; S.commitment_signer = "s";
    S.commitment_signature = "sig" }

(* a campaign with NO submissions: run_stage1 completes immediately with
   pending = [], so replay reaches finish_replay directly -- op_stage1_check /
   op_preflight / op_eval_o3 / op_stage2_check are never invoked, which is all
   this unit's tests need (they exercise transcript-digest EVIDENCE binding,
   not stage1/stage2 semantics). *)
let ac : S.authenticated_campaign =
  { S.authenticated_commitment = mc; S.authenticated_manifest = "m";
    S.authenticated_submissions = []; S.authenticated_record = "r";
    S.authenticated_completeness = S.CompletenessUnknown }

let ti : S.trusted_inputs =
  { S.ti_commitment_wire = { S.cw_digest = ""; S.cw_signer = ""; S.cw_signature = "" };
    S.ti_manifest = "m"; S.ti_submissions = []; S.ti_record = "r";
    S.ti_completeness = S.CompletenessUnknown; S.ti_config = cfg;
    S.ti_policy_document = "pd"; S.ti_policy = "p"; S.ti_policy_digest = "" }

let l0 : S.fuel_ledger = { S.fuel_budget = 1000; S.fuel_consumed = 0 }

let never_called _ = failwith "op not expected to be called with 0 submissions"

(* the mock: deterministic, but makes NO collision-freedom claim -- it is
   free to (and does) collide on transcripts of equal length. *)
let mock_digest (tr : S.exec_transcript) : S.digest =
  "mock:" ^ string_of_int (List.length tr)

let ops : S.primitive_ops =
  { S.op_parse_commitment = never_called;
    S.op_signer_authorised = never_called;
    S.op_signature_valid = never_called;
    S.op_manifest_policy_matches = never_called;
    S.op_manifest_audit_matches = never_called;
    S.op_manifest_context_matches = never_called;
    S.op_ledger_mismatch = never_called;
    S.op_record_identity_mismatch = never_called;
    S.op_completeness_wellformed = never_called;
    S.op_stage1_check = never_called;
    S.op_preflight = never_called;
    S.op_eval_o3 = never_called;
    S.op_stage2_check = never_called;
    S.op_record_crosscheck = (fun _ _ _ _ -> []);
    S.op_transcript_digest = mock_digest }

let vr : S.validation_result = S.ValidCampaign (ac, l0)
let cb : S.context_bundle = S.CtxNotNeeded

let ev1 : S.exec_event =
  { S.event_key = { S.key_phase = S.ContextProbe; S.key_role = S.Probe; S.key_repeat = 0 };
    S.event_input = [1; 2]; S.event_outcome = S.ExecOk [3; 4] }
let ev2 : S.exec_event =
  { S.event_key = { S.key_phase = S.Stage2Phase 0; S.key_role = S.XRole; S.key_repeat = 0 };
    S.event_input = [5]; S.event_outcome = S.ExecExhausted }

let fail msg = Printf.printf "FAIL: %s\n" msg; exit 1

let () =
  (* 1. empty transcript, evaluated twice: same digest (pure determinism) *)
  if S.op_transcript_digest ops [] <> S.op_transcript_digest ops []
  then fail "empty transcript digest not deterministic";

  (* 2. one-event transcript, evaluated twice: same digest *)
  let tr1 = [ev1] in
  if S.op_transcript_digest ops tr1 <> S.op_transcript_digest ops tr1
  then fail "one-event transcript digest not deterministic";

  (* 3. identical multi-event transcripts: same digest *)
  let tr2 = [ev1; ev2] and tr2' = [ev1; ev2] in
  if S.op_transcript_digest ops tr2 <> S.op_transcript_digest ops tr2'
  then fail "identical multi-event transcripts disagree";

  (* op_transcript_digest_deterministic operationally: equal Coq inputs give
     equal outputs -- already exercised above; this restates it via a
     structurally-rebuilt (not just re-evaluated) equal list. *)
  if S.op_transcript_digest ops tr2 <> S.op_transcript_digest ops [ev1; ev2]
  then fail "op_transcript_digest_deterministic";

  (* 4. live and (well-formed) offline evidence over the SAME typed
     transcript: same typed digest *)
  let out_live = S.assess_validated ops ti vr (S.LiveTranscript (tr1, cb)) in
  let out_offline =
    S.assess_validated ops ti vr
      (S.OfflineParse (S.WellformedParse (tr1, "wire-a"), cb)) in
  if S.typed_digest_of (S.outcome_transcript_evidence out_live)
     <> S.typed_digest_of (S.outcome_transcript_evidence out_offline)
  then fail "live/offline typed digest disagree";
  (match S.outcome_transcript_evidence out_live with
   | S.LiveCapture d when d = mock_digest tr1 -> ()
   | _ -> fail "live evidence does not carry the typed transcript digest");
  (match S.outcome_transcript_evidence out_offline with
   | S.OfflineTranscript (d, w) when d = mock_digest tr1 && w = "wire-a" -> ()
   | _ -> fail "offline evidence does not carry both digests");

  (* 5. a DIFFERENT offline wire_digest does not alter the typed digest, but
     the evidence VALUES differ (offline properly carries the wire digest
     too -- this is not claiming the two evidence values are identical) *)
  let out_offline2 =
    S.assess_validated ops ti vr
      (S.OfflineParse (S.WellformedParse (tr1, "wire-b"), cb)) in
  if S.typed_digest_of (S.outcome_transcript_evidence out_offline)
     <> S.typed_digest_of (S.outcome_transcript_evidence out_offline2)
  then fail "offline typed digest depends on the wire digest";
  if S.outcome_transcript_evidence out_offline
     = S.outcome_transcript_evidence out_offline2
  then fail "offline evidence values should differ (different wire digest)";

  (* 6. malformed offline input carries ONLY the raw-wire digest -- no typed
     digest, and (per malformed_assess_indep_of_transcript_digest) no
     dependence on op_transcript_digest at all *)
  let out_malformed =
    S.assess_validated ops ti vr
      (S.OfflineParse (S.MalformedParse ("bad_wire", "wire-mal"), cb)) in
  if S.outcome_transcript_evidence out_malformed
     <> S.MalformedTranscript ("bad_wire", "wire-mal")
  then fail "malformed evidence not as expected";
  if S.typed_digest_of (S.outcome_transcript_evidence out_malformed) <> None
  then fail "malformed evidence carries a typed digest";

  (* 7. replacing op_transcript_digest changes evidence as expected, but
     leaves the verdict (the outer assessment_outcome constructor) unchanged *)
  let ops' = S.set_transcript_digest ops (fun _ -> "replacement-digest") in
  if S.op_transcript_digest ops' [] <> "replacement-digest"
  then fail "set_transcript_digest did not install the new function";
  let out_live' = S.assess_validated ops' ti vr (S.LiveTranscript (tr1, cb)) in
  if S.outcome_transcript_evidence out_live
     = S.outcome_transcript_evidence out_live'
  then fail "evidence should change when the digest hook is replaced";
  let verdict_tag (out : S.assessment_outcome) =
    match out with
    | S.Inadmissible _ -> 0 | S.Exact _ -> 1
    | S.Obstructed _ -> 2 | S.Underdetermined _ -> 3 in
  if verdict_tag out_live <> verdict_tag out_live'
  then fail "verdict changed when only the digest hook was replaced";
  let out_malformed' =
    S.assess_validated ops' ti vr
      (S.OfflineParse (S.MalformedParse ("bad_wire", "wire-mal"), cb)) in
  if out_malformed <> out_malformed'
  then fail "malformed evidence must not depend on op_transcript_digest";

  (* 8. event reordering / a modified event is simply a DIFFERENT typed input
     to the hook -- no claim (and no reliance on a claim) that the resulting
     digests must differ. *)
  let tr2_reordered = [ev2; ev1] in
  ignore (S.op_transcript_digest ops tr2_reordered : S.digest);
  let ev1_modified = { ev1 with S.event_input = [1; 3] } in
  ignore (S.op_transcript_digest ops [ev1_modified] : S.digest);

  print_string
    "PASS: op_transcript_digest -- deterministic on identical typed inputs \
     (empty / one-event / multi-event transcripts); live and well-formed-\
     offline evidence agree on the typed digest, independent of the offline \
     wire digest; malformed evidence carries only the raw-wire digest and is \
     independent of op_transcript_digest; replacing the digest hook changes \
     evidence but leaves the verdict unchanged; no claim of digest \
     distinctness across different transcripts\n"
