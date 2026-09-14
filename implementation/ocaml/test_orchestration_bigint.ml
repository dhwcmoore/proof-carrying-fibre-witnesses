(* Closure-report obligation 3 -- extracted-OCaml build against arbitrary
   precision.  Every pre-existing validation-tier harness in this project
   (test_stage2.ml, test_stage1.ml, test_stage1_wrapper.ml,
   test_context_resolution.ml, test_manifest_matching.ml,
   test_transcript_digest.ml, test_manifest_authentication.ml,
   test_context_bundle.ml) links against extractions that map Z/nat to
   native OCaml [int] (ExtractStage2.v / ExtractManifestAuthentication.v /
   ExtractTranscriptDigest.v / the hand-written orchestration.ml mirror --
   explicitly NOT the exact-integer verifier, see each header).  This
   harness instead links against ocaml/extracted_orchestration.ml, produced
   by ExtractOrchestration.v using ExtrOcamlZBigInt/ExtrOcamlNatBigInt, so
   every nat/Z field of Orchestration.v (fuel, budgets, indices,
   candidate/witness coordinates) extracts to Big_int_Z.big_int -- true
   arbitrary precision, not merely a wider fixed-width int.  Its companion
   is test_fibre_witness_kernel_bigint.ml, against the other arbitrary-
   precision extraction, ExtractFibreWitnessKernel.v.

   It exercises the REAL exported entry points (validate_campaign,
   assess_validated) with values that exceed the range of a native 63-bit
   OCaml int (max_int = 4611686018427387903 on a 64-bit system) at points
   where the underlying Coq definitions (Orchestration.charge; the Z-typed
   candidate/witness coordinate lists) perform genuine arithmetic or
   structural equality, not just pass a number through unexamined:

     1. Orchestration.charge (fuel_consumed + cost <=? fuel_budget), driven
        indirectly through validate_campaign's authentication-fuel charges,
        at and one unit past a ~10^29 boundary.
     2. Z-valued candidate/witness coordinates (parsed_candidate.candidate_x
        / witness_data.witness_x etc.) carried, unmodified, through
        run_stage1 -> run_stage2 -> decide -> assess_validated, at
        magnitudes (~10^40, both positive and negative) a native int could
        not even represent as a literal.

   This is NOT a replacement for the machine-int harnesses' stage-1/stage-2
   boundary-condition coverage (O6a-O6d, C1-C4, etc.) -- that coverage
   already exists against extracted_stage2.ml and is unaffected by this
   file. This harness's sole job is arbitrary-precision fidelity of the
   extraction itself, exercised through genuine calls to the real
   Orchestration entry points, compiled and linked against zarith and
   actually executed (not merely coqc'd, per the closure-report wording). *)

module S = Extracted_orchestration

let big = Big_int_Z.big_int_of_string
let bi = Big_int_Z.big_int_of_int
let eqbi = Big_int_Z.eq_big_int
let fail msg = Printf.printf "FAIL: %s\n" msg; exit 1

(* well beyond max_int (2^62 - 1 on a 64-bit system) *)
let huge_budget = big "100000000000000000000000000000" (* 10^29 *)
let huge_pos = big "40000000000000000000000000000000000000000" (* 4*10^40 *)
let huge_neg = big "-40000000000000000000000000000000000000001"
let huge_pos2 = big "50000000000000000000000000000000000000002"
let huge_neg2 = big "-50000000000000000000000000000000000000003"

let ta : S.trust_anchor = { S.ta_authorised_signers = []; S.ta_keys = [] }

let mc : S.manifest_commitment =
  { S.commitment_digest = "mcd"; S.commitment_signer = "s";
    S.commitment_signature = "sig" }

let cw : S.manifest_commitment_wire =
  { S.cw_digest = "mcd"; S.cw_signer = "s"; S.cw_signature = "sig" }

let unused name = fun _ -> failwith ("op not expected to be called: " ^ name)

(* ---- Scenario 1: validate_campaign's authentication-fuel charging at a
   ~10^29 boundary. Every non-fuel guard trivially accepts, so the only
   thing that can turn ValidCampaign into FuelObstructed is `charge`. Stage
   1/2 ops are never invoked by validate_campaign itself. ---- *)

let accepting_ops : S.primitive_ops =
  { S.op_parse_commitment = (fun _ -> S.CommitmentParsed mc);
    S.op_signer_authorised = (fun _ _ -> true);
    S.op_signature_valid = (fun _ _ _ -> true);
    S.op_manifest_policy_matches = (fun _ _ -> true);
    S.op_manifest_audit_matches = (fun _ _ -> true);
    S.op_manifest_context_matches = (fun _ _ -> true);
    S.op_ledger_mismatch = (fun _ _ -> None);
    S.op_record_identity_mismatch = (fun _ _ _ _ -> None);
    S.op_completeness_wellformed = (fun _ -> true);
    S.op_stage1_check = unused "op_stage1_check (scenario 1)";
    S.op_preflight = unused "op_preflight (scenario 1)";
    S.op_eval_o3 = unused "op_eval_o3 (scenario 1)";
    S.op_stage2_check = unused "op_stage2_check (scenario 1)";
    S.op_record_crosscheck = (fun _ _ _ _ -> []);
    S.op_transcript_digest = (fun _ -> "digest") }

let zero_sched : S.fuel_schedule =
  { S.commitment_parse_fuel = bi 0; S.signature_verify_fuel = bi 0;
    S.manifest_bind_fuel = bi 0; S.record_bind_fuel = bi 0;
    S.preflight_fuel = bi 0; S.stage1_base_fuel = bi 0;
    S.stage1_per_byte_fuel = bi 0 }

let mk_cfg1 ~commitment_parse_fuel : S.verifier_config =
  { S.max_candidates = bi 10; S.max_wire_bytes = bi 100;
    S.max_transcript_bytes = bi 100; S.max_fuel = huge_budget;
    S.model_call_fuel = bi 1; S.max_fuel_per_candidate = bi 100;
    S.schedule = { zero_sched with S.commitment_parse_fuel };
    S.config_trust_anchor = ta }

let mk_ti1 ~cfg : S.trusted_inputs =
  { S.ti_commitment_wire = cw; S.ti_manifest = "m"; S.ti_submissions = [];
    S.ti_record = "r"; S.ti_completeness = S.CompletenessUnknown;
    S.ti_config = cfg; S.ti_policy_document = "pd"; S.ti_policy = "p";
    S.ti_policy_digest = "" }

let () =
  (* 1a. commitment_parse_fuel exactly equal to a ~10^29 max_fuel budget:
     charge's `used <=? budget` must accept at exact equality, at a
     magnitude no native int arithmetic could reproduce without wraparound. *)
  let cfg_ok = mk_cfg1 ~commitment_parse_fuel:huge_budget in
  (match S.validate_campaign accepting_ops (mk_ti1 ~cfg:cfg_ok) with
   | S.ValidCampaign (_, l4) ->
       if not (eqbi l4.S.fuel_consumed huge_budget)
       then fail "scenario 1a: fuel_consumed not exactly the huge budget"
   | S.FuelObstructed _ -> fail "scenario 1a: exact-boundary charge rejected"
   | S.InvalidCampaign _ -> fail "scenario 1a: unexpected InvalidCampaign");

  (* 1b. one unit past that same ~10^29 budget: charge must reject. Under
     silent native-int wraparound this class of comparison is exactly what
     can go wrong (a too-large sum wrapping negative and comparing as
     spuriously small). *)
  let cfg_over =
    mk_cfg1 ~commitment_parse_fuel:(Big_int_Z.succ_big_int huge_budget) in
  (match S.validate_campaign accepting_ops (mk_ti1 ~cfg:cfg_over) with
   | S.FuelObstructed (l0, _) ->
       if not (eqbi l0.S.fuel_consumed (bi 0)) || not (eqbi l0.S.fuel_budget huge_budget)
       then fail "scenario 1b: unexpected fuel_ledger on rejection"
   | S.ValidCampaign _ -> fail "scenario 1b: one-past-boundary charge wrongly accepted"
   | S.InvalidCampaign _ -> fail "scenario 1b: unexpected InvalidCampaign");

  (* ---- Scenario 2: Z-valued candidate/witness coordinates, magnitudes no
     native int could even represent as a literal, carried unmodified
     through run_stage1 -> run_stage2 -> decide -> assess_validated. ---- *)
  let sub : S.candidate_submission =
    { S.submission_wire = "wire"; S.submission_wire_length = bi 4;
      S.submission_digest = "sd" } in
  let ac : S.authenticated_campaign =
    { S.authenticated_commitment = mc; S.authenticated_manifest = "m";
      S.authenticated_submissions = [sub]; S.authenticated_record = "r";
      S.authenticated_completeness = S.CompletenessUnknown } in
  let ti2 : S.trusted_inputs =
    { S.ti_commitment_wire = cw; S.ti_manifest = "m"; S.ti_submissions = [sub];
      S.ti_record = "r"; S.ti_completeness = S.CompletenessUnknown;
      S.ti_config =
        { S.max_candidates = bi 10; S.max_wire_bytes = bi 100;
          S.max_transcript_bytes = bi 100; S.max_fuel = bi 1000;
          S.model_call_fuel = bi 1; S.max_fuel_per_candidate = bi 100;
          S.schedule = { zero_sched with S.stage1_base_fuel = bi 1 };
          S.config_trust_anchor = ta };
      S.ti_policy_document = "pd"; S.ti_policy = "p"; S.ti_policy_digest = "" } in
  let l0 : S.fuel_ledger = { S.fuel_budget = bi 1000; S.fuel_consumed = bi 0 } in
  let vr : S.validation_result = S.ValidCampaign (ac, l0) in
  let lc : S.loaded_context =
    { S.loaded_descriptor = "d"; S.loaded_model_bytes = "mb";
      S.loaded_preproc_bytes = "pb"; S.loaded_inference_bytes = "ib";
      S.loaded_context_token = "tok" } in
  let cb : S.context_bundle = S.CtxLoaded lc in
  let rc : S.resolved_context =
    { S.resolved_policy = "p"; S.resolved_context_token = "tok";
      S.resolved_descriptor = "d" } in
  let probe_key : S.call_key =
    { S.key_phase = S.ContextProbe; S.key_role = S.Probe; S.key_repeat = bi 0 } in
  let probe_event : S.exec_event =
    { S.event_key = probe_key; S.event_input = []; S.event_outcome = S.ExecOk [] } in
  let tr : S.exec_transcript = [probe_event] in
  let pending : S.pending_submission =
    { S.pending_index = bi 0; S.pending_submission_digest = "sd";
      S.pending_semantic_digest = "cd";
      S.pending_candidate =
        { S.pc_candidate_id = "c"; S.candidate_x = [huge_pos];
          S.candidate_y = [huge_neg] };
      S.pending_findings = [] } in
  let witness : S.witness_data =
    { S.witness_index = bi 0; S.witness_submission_digest = "sd";
      S.witness_semantic_digest = "cd"; S.witness_x = [huge_pos];
      S.witness_y = [huge_neg]; S.witness_o_x = [huge_pos2];
      S.witness_o_y = [huge_neg2]; S.witness_findings = [] } in
  let ops2 : S.primitive_ops =
    { S.op_parse_commitment = unused "op_parse_commitment (scenario 2)";
      S.op_signer_authorised = unused "op_signer_authorised (scenario 2)";
      S.op_signature_valid = unused "op_signature_valid (scenario 2)";
      S.op_manifest_policy_matches = unused "op_manifest_policy_matches (scenario 2)";
      S.op_manifest_audit_matches = unused "op_manifest_audit_matches (scenario 2)";
      S.op_manifest_context_matches = unused "op_manifest_context_matches (scenario 2)";
      S.op_ledger_mismatch = unused "op_ledger_mismatch (scenario 2)";
      S.op_record_identity_mismatch = unused "op_record_identity_mismatch (scenario 2)";
      S.op_completeness_wellformed = unused "op_completeness_wellformed (scenario 2)";
      S.op_stage1_check =
        (fun _ _ _ _ _ ->
          { S.s1_index = bi 0; S.s1_submission_digest = "sd";
            S.s1_candidate_id = Some "c"; S.s1_semantic_digest = Some "cd";
            S.s1_verdict = S.S1Pending pending; S.s1_findings = [] });
      S.op_preflight = (fun _ -> S.PreflightOk []);
      S.op_eval_o3 = (fun _ _ _ -> S.O3Ok (rc, []));
      S.op_stage2_check =
        (fun _ _ _ ps ->
          (* Confirm the pending candidate that actually arrived here (via
             run_stage1's fold, not a value plucked out of scope) still
             carries the huge coordinates op_stage1_check installed --
             i.e. run_stage1 -> run_stage2 genuinely threads the Z-typed
             candidate data, not just whatever this callback chooses to
             construct independently. *)
          (match ps.S.pending_candidate.S.candidate_x,
                 ps.S.pending_candidate.S.candidate_y with
           | [cx], [cy] when eqbi cx huge_pos && eqbi cy huge_neg -> ()
           | _ -> fail "scenario 2: pending candidate coordinates corrupted \
                        between op_stage1_check and op_stage2_check");
          { S.s2_index = bi 0; S.s2_verdict = S.ValidWitness witness;
            S.s2_findings = [] });
      S.op_record_crosscheck = (fun _ _ _ _ -> []);
      S.op_transcript_digest = (fun _ -> "digest") } in
  let out = S.assess_validated ops2 ti2 vr (S.LiveTranscript (tr, cb)) in
  (match out with
   | S.Inadmissible cert ->
       (match cert.S.certificate_body with
        | S.InadmissibleBody (w, others, _findings) ->
            if others <> [] then fail "scenario 2: unexpected extra witnesses";
            if not (eqbi (List.hd w.S.witness_x) huge_pos)
               || not (eqbi (List.hd w.S.witness_y) huge_neg)
               || not (eqbi (List.hd w.S.witness_o_x) huge_pos2)
               || not (eqbi (List.hd w.S.witness_o_y) huge_neg2)
            then fail "scenario 2: witness coordinates corrupted in transit"
        | _ -> fail "scenario 2: expected InadmissibleBody")
   | S.Exact _ -> fail "scenario 2: expected Inadmissible, got Exact"
   | S.Obstructed _ -> fail "scenario 2: expected Inadmissible, got Obstructed"
   | S.Underdetermined _ -> fail "scenario 2: expected Inadmissible, got Underdetermined");
  if S.verdict_of out <> S.INADMISSIBLE
  then fail "scenario 2: verdict_of disagrees with the outcome constructor";

  print_string
    "PASS: arbitrary-precision extraction (ExtractOrchestration.v, \
     Big_int_Z) -- validate_campaign's fuel charging exact and correct at a \
     ~10^29 boundary (both accepting at equality and rejecting one unit \
     past it); candidate/witness Z coordinates at ~4*10^40 magnitude (both \
     signs) survive run_stage1 -> run_stage2 -> decide -> assess_validated \
     unmodified\n"
