(* Exercises the extracted concrete stage-2 checker (Stage2.stage2_check) and its
   Orchestration adapter (Stage2Adapter.adapter_stage2_check): a valid witness, a
   not-a-witness (C4), every obstruction reason, the O6b-before-O6c order, the
   O6d fuel boundary, and malformed-length inputs at both the candidate and the
   event boundary.

   Z and nat are extracted to OCaml int (see ExtractStage2.v): this links with no
   bignum library and is NOT the exact-integer verifier. *)

module S = Extracted_stage2

let v1 (z : int) : int S.vec = S.of_list [z]
let hd1 : int S.vec -> int = function S.Cons (z, _, _) -> z | S.Nil -> 0

let id_v (x : int S.vec) : int S.vec = x

let mk_policy ~quantise : S.policy =
  { S.domainb = (fun _ -> true);
    S.quantise;
    S.target = (fun v -> hd1 v <> 0) }

let mk_ctx ~quantise : S.auditContext =
  { S.context_policy = mk_policy ~quantise;
    S.preproc = id_v;
    S.model = id_v }

let const_quant : int S.vec -> int S.vec = fun _ -> v1 0
let id_quant : int S.vec -> int S.vec = id_v

let x = v1 0
let y = v1 2
let ok i o = Some (S.OeOk (v1 i, v1 o))
let failed i = Some (S.OeFailed (v1 i))
let exhausted i = Some (S.OeExhausted (v1 i))
let rng_all : int S.vec -> bool = fun _ -> true
let rng_none : int S.vec -> bool = fun _ -> false

let run ?(ctx = mk_ctx ~quantise:const_quant) ?(rng = rng_all) ?(fuel_ok = true)
        eX0 eX1 eY0 eY1 =
  S.stage2_check 1 1 1 ctx rng fuel_ok x y eX0 eX1 eY0 eY1

let fail msg = Printf.printf "FAIL: %s\n" msg; exit 1

let () =
  (* 1. valid witness *)
  (match run (ok 0 0) (ok 0 0) (ok 2 2) (ok 2 2) with
   | S.S2Valid (_, _) -> ()
   | _ -> fail "expected S2Valid");

  (* 2. not a witness: quantiser distinguishes o_x from o_y (C4) *)
  (match run ~ctx:(mk_ctx ~quantise:id_quant) (ok 0 0) (ok 0 0) (ok 2 2) (ok 2 2) with
   | S.S2NotWitness -> () | _ -> fail "expected S2NotWitness");

  (* 3. O6a: a missing keyed event *)
  (match run (ok 0 0) (ok 0 0) (ok 2 2) None with
   | S.S2Obstructed S.S2ExecMissing -> () | _ -> fail "expected S2ExecMissing");

  (* 4. O6b before O6c: wrong input AND a failed outcome -> ExecInputMismatch *)
  (match run (failed 5) (ok 0 0) (ok 2 2) (ok 2 2) with
   | S.S2Obstructed S.S2ExecInputMismatch -> ()
   | S.S2Obstructed S.S2ExecFailure -> fail "O6c ran before O6b"
   | _ -> fail "expected S2ExecInputMismatch");

  (* 5. O6c: correct inputs, one failed outcome -> ExecFailure *)
  (match run (failed 0) (ok 0 0) (ok 2 2) (ok 2 2) with
   | S.S2Obstructed S.S2ExecFailure -> () | _ -> fail "expected S2ExecFailure");

  (* 6. O6c: exhaustion dominates plain failure *)
  (match run (exhausted 0) (ok 0 0) (failed 2) (ok 2 2) with
   | S.S2Obstructed S.S2ExecFuelExhausted -> ()
   | _ -> fail "expected S2ExecFuelExhausted (exhaustion dominates)");

  (* 7. O6d: per-candidate fuel boundary, otherwise-valid events *)
  (match run ~fuel_ok:false (ok 0 0) (ok 0 0) (ok 2 2) (ok 2 2) with
   | S.S2Obstructed S.S2ExecFuelExhausted -> ()
   | _ -> fail "expected S2ExecFuelExhausted (O6d)");

  (* 8. O4: non-repeatable X value *)
  (match run (ok 0 0) (ok 0 9) (ok 2 2) (ok 2 2) with
   | S.S2Obstructed S.S2NonDeterministic -> ()
   | _ -> fail "expected S2NonDeterministic");

  (* 9. O5: observation out of range *)
  (match run ~rng:rng_none (ok 0 0) (ok 0 0) (ok 2 2) (ok 2 2) with
   | S.S2Obstructed S.S2ObsOutOfRange -> ()
   | _ -> fail "expected S2ObsOutOfRange");

  (match S.o_reason_of_fail S.S2NonDeterministic,
         S.o_reason_of_fail S.S2ExecInputMismatch with
   | S.NonDeterministic, S.ExecInputMismatch -> ()
   | _ -> fail "o_reason_of_fail mapping wrong");

  (* ---- adapter ---- *)
  let ps ~cx ~cy : S.pending_submission =
    { S.pending_index = 7;
      S.pending_submission_digest = "sd"; S.pending_semantic_digest = "cd";
      S.pending_candidate = { S.pc_candidate_id = "c"; S.candidate_x = cx; S.candidate_y = cy };
      S.pending_findings = [] } in
  let rc : S.resolved_context =
    { S.resolved_policy = "p"; S.resolved_context_token = "t"; S.resolved_descriptor = "d" } in
  let sched : S.fuel_schedule =
    { S.commitment_parse_fuel = 0; S.signature_verify_fuel = 0;
      S.manifest_bind_fuel = 0; S.record_bind_fuel = 0; S.preflight_fuel = 0;
      S.stage1_base_fuel = 1; S.stage1_per_byte_fuel = 0 } in
  let cfg ~mcf ~mfpc : S.verifier_config =
    { S.max_candidates = 10; S.max_wire_bytes = 100; S.max_transcript_bytes = 100;
      S.max_fuel = 1000; S.model_call_fuel = mcf; S.max_fuel_per_candidate = mfpc;
      S.schedule = sched; S.config_trust_anchor = { S.ta_authorised_signers = []; S.ta_keys = [] } } in
  let ev role rep inp out : S.exec_event =
    { S.event_key = { S.key_phase = S.Stage2Phase 7; S.key_role = role; S.key_repeat = rep };
      S.event_input = inp; S.event_outcome = out } in
  let ok_ev role rep i o = ev role rep [i] (S.ExecOk [o]) in
  let tr_ok : S.exec_transcript =
    [ ok_ev S.XRole 0 0 0; ok_ev S.XRole 1 0 0; ok_ev S.YRole 0 2 2; ok_ev S.YRole 1 2 2 ] in
  let ctx = mk_ctx ~quantise:const_quant in
  let good_cfg = cfg ~mcf:1 ~mfpc:100 in

  (match (S.adapter_stage2_check 1 1 1 ctx rng_all rc good_cfg tr_ok (ps ~cx:[0] ~cy:[2])).S.s2_verdict with
   | S.ValidWitness w when w.S.witness_index = 7
       && w.S.witness_o_x = [0] && w.S.witness_o_y = [2] -> ()
   | _ -> fail "adapter: expected ValidWitness index 7");

  (* adapter O6d: model_call_fuel too big for max_fuel_per_candidate *)
  (match (S.adapter_stage2_check 1 1 1 ctx rng_all rc (cfg ~mcf:30 ~mfpc:100) tr_ok (ps ~cx:[0] ~cy:[2])).S.s2_verdict with
   | S.WitnessCheckObstructed S.ExecFuelExhausted -> ()
   | _ -> fail "adapter: expected WitnessCheckObstructed ExecFuelExhausted (O6d)");

  (* adapter C1 re-check *)
  (match (S.adapter_stage2_check 1 1 1 ctx rng_all rc good_cfg tr_ok (ps ~cx:[0] ~cy:[0])).S.s2_verdict with
   | S.S2NotAWitness S.InputsEqual -> ()
   | _ -> fail "adapter: expected S2NotAWitness InputsEqual");

  (* adapter: missing events *)
  (match (S.adapter_stage2_check 1 1 1 ctx rng_all rc good_cfg [] (ps ~cx:[0] ~cy:[2])).S.s2_verdict with
   | S.WitnessCheckObstructed S.ExecMissing -> ()
   | _ -> fail "adapter: expected WitnessCheckObstructed ExecMissing");

  (* adapter: malformed candidate length -> relabelled fallback, not InputsEqual *)
  (match (S.adapter_stage2_check 1 1 1 ctx rng_all rc good_cfg tr_ok (ps ~cx:[0;0] ~cy:[2])).S.s2_verdict with
   | S.WitnessCheckObstructed S.ExecFailure -> ()
   | S.S2NotAWitness S.InputsEqual -> fail "adapter: malformed candidate mislabelled InputsEqual"
   | _ -> fail "adapter: expected WitnessCheckObstructed ExecFailure for malformed candidate");

  (* adapter: malformed event-vector length -> slot None -> ExecMissing (event present
     but unusable; excluded upstream by atomic parse_transcript) *)
  let tr_bad_input : S.exec_transcript =
    [ ev S.XRole 0 [0;0] (S.ExecOk [0]); ok_ev S.XRole 1 0 0;
      ok_ev S.YRole 0 2 2; ok_ev S.YRole 1 2 2 ] in
  (match (S.adapter_stage2_check 1 1 1 ctx rng_all rc good_cfg tr_bad_input (ps ~cx:[0] ~cy:[2])).S.s2_verdict with
   | S.WitnessCheckObstructed S.ExecMissing -> ()
   | _ -> fail "adapter: expected WitnessCheckObstructed ExecMissing for malformed event vector");

  print_string "PASS: stage-2 checker -- valid, not-a-witness, all obstructions, \
                O6b<O6c order, O6d fuel boundary, malformed candidate/event lengths\n"
