(* Exercises the extracted concrete stage-2 checker (Stage2.stage2_check) and its
   Orchestration adapter (Stage2Adapter.adapter_stage2_check): a valid witness, a
   not-a-witness (C4), every obstruction reason, the O6b-before-O6c order, the
   O6d fuel boundary, and malformed-length inputs at both the candidate and the
   event boundary -- plus (closure-report obligation 3) a valid witness with
   huge positive/negative coordinates, and the O6d fuel boundary itself
   (Stage2Adapter.fuel_ok) at magnitudes beyond a native 63-bit OCaml int.
   (A huge pending/witness *index* is already covered in test_stage1.ml and
   test_stage1_wrapper.ml -- not repeated here.)

   Z and nat now extract to Big_int_Z.big_int (see ExtractStage2.v): true
   arbitrary precision, not merely a wider fixed-width int. *)

module S = Extracted_stage2

let bi = Big_int_Z.big_int_of_int
let big = Big_int_Z.big_int_of_string
let eqbi = Big_int_Z.eq_big_int
let list_eqbi a b = try List.for_all2 eqbi a b with Invalid_argument _ -> false

(* well beyond max_int (2^62 - 1 on a 64-bit system) *)
let huge_pos = big "40000000000000000000000000000000000000000" (* 4*10^40 *)
let huge_neg = big "-40000000000000000000000000000000000000001"
let huge_o1 = big "70000000000000000000000000000000000000002"
let huge_o2 = big "-70000000000000000000000000000000000000003"
let huge_mcf = big "10000000000000000000000000000000000000000" (* 10^40 *)

let v1 (z : Big_int_Z.big_int) : Big_int_Z.big_int S.vec = S.of_list [z]
let hd1 : Big_int_Z.big_int S.vec -> Big_int_Z.big_int =
  function S.Cons (z, _, _) -> z | S.Nil -> bi 0

let id_v (x : Big_int_Z.big_int S.vec) : Big_int_Z.big_int S.vec = x

let default_target v = not (eqbi (hd1 v) (bi 0))

let mk_policy ?(target = default_target) ~quantise () : S.policy =
  { S.domainb = (fun _ -> true);
    S.quantise;
    S.target }

let mk_ctx ?(target = default_target) ~quantise () : S.auditContext =
  { S.context_policy = mk_policy ~target ~quantise ();
    S.preproc = id_v;
    S.model = id_v }

let const_quant : Big_int_Z.big_int S.vec -> Big_int_Z.big_int S.vec =
  fun _ -> v1 (bi 0)
let id_quant : Big_int_Z.big_int S.vec -> Big_int_Z.big_int S.vec = id_v

let x = v1 (bi 0)
let y = v1 (bi 2)
let ok i o = Some (S.OeOk (v1 i, v1 o))
let failed i = Some (S.OeFailed (v1 i))
let exhausted i = Some (S.OeExhausted (v1 i))
let rng_all : Big_int_Z.big_int S.vec -> bool = fun _ -> true
let rng_none : Big_int_Z.big_int S.vec -> bool = fun _ -> false

let run ?(ctx = mk_ctx ~quantise:const_quant ()) ?(rng = rng_all) ?(fuel_ok = true)
        eX0 eX1 eY0 eY1 =
  S.stage2_check (bi 1) (bi 1) (bi 1) ctx rng fuel_ok x y eX0 eX1 eY0 eY1

let fail msg = Printf.printf "FAIL: %s\n" msg; exit 1

let () =
  (* 1. valid witness *)
  (match run (ok (bi 0) (bi 0)) (ok (bi 0) (bi 0)) (ok (bi 2) (bi 2)) (ok (bi 2) (bi 2)) with
   | S.S2Valid (_, _) -> ()
   | _ -> fail "expected S2Valid");

  (* 2. not a witness: quantiser distinguishes o_x from o_y (C4) *)
  (match run ~ctx:(mk_ctx ~quantise:id_quant ())
           (ok (bi 0) (bi 0)) (ok (bi 0) (bi 0)) (ok (bi 2) (bi 2)) (ok (bi 2) (bi 2)) with
   | S.S2NotWitness -> () | _ -> fail "expected S2NotWitness");

  (* 3. O6a: a missing keyed event *)
  (match run (ok (bi 0) (bi 0)) (ok (bi 0) (bi 0)) (ok (bi 2) (bi 2)) None with
   | S.S2Obstructed S.S2ExecMissing -> () | _ -> fail "expected S2ExecMissing");

  (* 4. O6b before O6c: wrong input AND a failed outcome -> ExecInputMismatch *)
  (match run (failed (bi 5)) (ok (bi 0) (bi 0)) (ok (bi 2) (bi 2)) (ok (bi 2) (bi 2)) with
   | S.S2Obstructed S.S2ExecInputMismatch -> ()
   | S.S2Obstructed S.S2ExecFailure -> fail "O6c ran before O6b"
   | _ -> fail "expected S2ExecInputMismatch");

  (* 5. O6c: correct inputs, one failed outcome -> ExecFailure *)
  (match run (failed (bi 0)) (ok (bi 0) (bi 0)) (ok (bi 2) (bi 2)) (ok (bi 2) (bi 2)) with
   | S.S2Obstructed S.S2ExecFailure -> () | _ -> fail "expected S2ExecFailure");

  (* 6. O6c: exhaustion dominates plain failure *)
  (match run (exhausted (bi 0)) (ok (bi 0) (bi 0)) (failed (bi 2)) (ok (bi 2) (bi 2)) with
   | S.S2Obstructed S.S2ExecFuelExhausted -> ()
   | _ -> fail "expected S2ExecFuelExhausted (exhaustion dominates)");

  (* 7. O6d: per-candidate fuel boundary, otherwise-valid events *)
  (match run ~fuel_ok:false (ok (bi 0) (bi 0)) (ok (bi 0) (bi 0)) (ok (bi 2) (bi 2)) (ok (bi 2) (bi 2)) with
   | S.S2Obstructed S.S2ExecFuelExhausted -> ()
   | _ -> fail "expected S2ExecFuelExhausted (O6d)");

  (* 8. O4: non-repeatable X value *)
  (match run (ok (bi 0) (bi 0)) (ok (bi 0) (bi 9)) (ok (bi 2) (bi 2)) (ok (bi 2) (bi 2)) with
   | S.S2Obstructed S.S2NonDeterministic -> ()
   | _ -> fail "expected S2NonDeterministic");

  (* 9. O5: observation out of range *)
  (match run ~rng:rng_none (ok (bi 0) (bi 0)) (ok (bi 0) (bi 0)) (ok (bi 2) (bi 2)) (ok (bi 2) (bi 2)) with
   | S.S2Obstructed S.S2ObsOutOfRange -> ()
   | _ -> fail "expected S2ObsOutOfRange");

  (match S.o_reason_of_fail S.S2NonDeterministic,
         S.o_reason_of_fail S.S2ExecInputMismatch with
   | S.NonDeterministic, S.ExecInputMismatch -> ()
   | _ -> fail "o_reason_of_fail mapping wrong");

  (* ---- beyond-63-bit: a valid witness with a huge POSITIVE x coordinate, a
     huge NEGATIVE y coordinate, and huge (differing) observation values.
     stage2_check itself never inspects domainb/target (those are stage-1
     concerns) -- it does require the event inputs to equal preproc's output
     on the ACTUAL x/y passed in (O6b), so x/y here must be the huge vectors
     themselves, not the module's fixed [0]/[2] `run` closes over. *)
  let x_huge = v1 huge_pos and y_huge = v1 huge_neg in
  (match S.stage2_check (bi 1) (bi 1) (bi 1) (mk_ctx ~quantise:const_quant ())
           rng_all true x_huge y_huge
           (ok huge_pos huge_o1) (ok huge_pos huge_o1)
           (ok huge_neg huge_o2) (ok huge_neg huge_o2) with
   | S.S2Valid (ox, oy) when list_eqbi (S.to_list (bi 1) ox) [huge_o1]
                          && list_eqbi (S.to_list (bi 1) oy) [huge_o2] -> ()
   | S.S2Valid _ -> fail "huge valid witness: observation vectors corrupted"
   | _ -> fail "expected S2Valid (huge positive x, huge negative y)");

  (* ---- adapter ---- *)
  let ps ~cx ~cy : S.pending_submission =
    { S.pending_index = bi 7;
      S.pending_submission_digest = "sd"; S.pending_semantic_digest = "cd";
      S.pending_candidate = { S.pc_candidate_id = "c"; S.candidate_x = cx; S.candidate_y = cy };
      S.pending_findings = [] } in
  let rc : S.resolved_context =
    { S.resolved_policy = "p"; S.resolved_context_token = "t"; S.resolved_descriptor = "d" } in
  let sched : S.fuel_schedule =
    { S.commitment_parse_fuel = bi 0; S.signature_verify_fuel = bi 0;
      S.manifest_bind_fuel = bi 0; S.record_bind_fuel = bi 0; S.preflight_fuel = bi 0;
      S.stage1_base_fuel = bi 1; S.stage1_per_byte_fuel = bi 0 } in
  let cfg ~mcf ~mfpc : S.verifier_config =
    { S.max_candidates = bi 10; S.max_wire_bytes = bi 100; S.max_transcript_bytes = bi 100;
      S.max_fuel = bi 1000; S.model_call_fuel = mcf; S.max_fuel_per_candidate = mfpc;
      S.schedule = sched; S.config_trust_anchor = { S.ta_authorised_signers = []; S.ta_keys = [] } } in
  let ev role rep inp out : S.exec_event =
    { S.event_key = { S.key_phase = S.Stage2Phase (bi 7); S.key_role = role; S.key_repeat = rep };
      S.event_input = inp; S.event_outcome = out } in
  let ok_ev role rep i o = ev role rep [i] (S.ExecOk [o]) in
  let tr_ok : S.exec_transcript =
    [ ok_ev S.XRole (bi 0) (bi 0) (bi 0); ok_ev S.XRole (bi 1) (bi 0) (bi 0);
      ok_ev S.YRole (bi 0) (bi 2) (bi 2); ok_ev S.YRole (bi 1) (bi 2) (bi 2) ] in
  let ctx = mk_ctx ~quantise:const_quant () in
  let good_cfg = cfg ~mcf:(bi 1) ~mfpc:(bi 100) in

  (match (S.adapter_stage2_check (bi 1) (bi 1) (bi 1) ctx rng_all rc good_cfg tr_ok
            (ps ~cx:[bi 0] ~cy:[bi 2])).S.s2_verdict with
   | S.ValidWitness w when eqbi w.S.witness_index (bi 7)
       && list_eqbi w.S.witness_o_x [bi 0] && list_eqbi w.S.witness_o_y [bi 2] -> ()
   | _ -> fail "adapter: expected ValidWitness index 7");

  (* adapter O6d: model_call_fuel too big for max_fuel_per_candidate *)
  (match (S.adapter_stage2_check (bi 1) (bi 1) (bi 1) ctx rng_all rc
            (cfg ~mcf:(bi 30) ~mfpc:(bi 100)) tr_ok
            (ps ~cx:[bi 0] ~cy:[bi 2])).S.s2_verdict with
   | S.WitnessCheckObstructed S.ExecFuelExhausted -> ()
   | _ -> fail "adapter: expected WitnessCheckObstructed ExecFuelExhausted (O6d)");

  (* adapter C1 re-check *)
  (match (S.adapter_stage2_check (bi 1) (bi 1) (bi 1) ctx rng_all rc good_cfg tr_ok
            (ps ~cx:[bi 0] ~cy:[bi 0])).S.s2_verdict with
   | S.S2NotAWitness S.InputsEqual -> ()
   | _ -> fail "adapter: expected S2NotAWitness InputsEqual");

  (* adapter: missing events *)
  (match (S.adapter_stage2_check (bi 1) (bi 1) (bi 1) ctx rng_all rc good_cfg []
            (ps ~cx:[bi 0] ~cy:[bi 2])).S.s2_verdict with
   | S.WitnessCheckObstructed S.ExecMissing -> ()
   | _ -> fail "adapter: expected WitnessCheckObstructed ExecMissing");

  (* adapter: malformed candidate length -> relabelled fallback, not InputsEqual *)
  (match (S.adapter_stage2_check (bi 1) (bi 1) (bi 1) ctx rng_all rc good_cfg tr_ok
            (ps ~cx:[bi 0; bi 0] ~cy:[bi 2])).S.s2_verdict with
   | S.WitnessCheckObstructed S.ExecFailure -> ()
   | S.S2NotAWitness S.InputsEqual -> fail "adapter: malformed candidate mislabelled InputsEqual"
   | _ -> fail "adapter: expected WitnessCheckObstructed ExecFailure for malformed candidate");

  (* adapter: malformed event-vector length -> slot None -> ExecMissing (event present
     but unusable; excluded upstream by atomic parse_transcript) *)
  let tr_bad_input : S.exec_transcript =
    [ ev S.XRole (bi 0) [bi 0; bi 0] (S.ExecOk [bi 0]); ok_ev S.XRole (bi 1) (bi 0) (bi 0);
      ok_ev S.YRole (bi 0) (bi 2) (bi 2); ok_ev S.YRole (bi 1) (bi 2) (bi 2) ] in
  (match (S.adapter_stage2_check (bi 1) (bi 1) (bi 1) ctx rng_all rc good_cfg tr_bad_input
            (ps ~cx:[bi 0] ~cy:[bi 2])).S.s2_verdict with
   | S.WitnessCheckObstructed S.ExecMissing -> ()
   | _ -> fail "adapter: expected WitnessCheckObstructed ExecMissing for malformed event vector");

  (* ---- beyond-63-bit: Stage2Adapter.fuel_ok (4 * model_call_fuel <=?
     max_fuel_per_candidate), a genuine arithmetic comparison, at a ~4*10^40
     boundary -- accepts at exact equality, rejects one unit past it. *)
  let mfpc_exact = Big_int_Z.mult_big_int (bi 4) huge_mcf in
  (match (S.adapter_stage2_check (bi 1) (bi 1) (bi 1) ctx rng_all rc
            (cfg ~mcf:huge_mcf ~mfpc:mfpc_exact) tr_ok
            (ps ~cx:[bi 0] ~cy:[bi 2])).S.s2_verdict with
   | S.ValidWitness _ -> ()
   | S.WitnessCheckObstructed S.ExecFuelExhausted ->
       fail "fuel_ok wrongly rejected 4*model_call_fuel exactly equal to \
             max_fuel_per_candidate at huge magnitude"
   | _ -> fail "expected ValidWitness at the exact huge fuel_ok boundary");
  let mfpc_one_short = Big_int_Z.pred_big_int mfpc_exact in
  (match (S.adapter_stage2_check (bi 1) (bi 1) (bi 1) ctx rng_all rc
            (cfg ~mcf:huge_mcf ~mfpc:mfpc_one_short) tr_ok
            (ps ~cx:[bi 0] ~cy:[bi 2])).S.s2_verdict with
   | S.WitnessCheckObstructed S.ExecFuelExhausted -> ()
   | _ -> fail "expected WitnessCheckObstructed ExecFuelExhausted one unit \
                short of the huge fuel_ok boundary");

  print_string "PASS: stage-2 checker -- valid, not-a-witness, all obstructions, \
                O6b<O6c order, O6d fuel boundary, malformed candidate/event lengths; \
                plus a valid witness with huge positive/negative coordinates and \
                fuel_ok's exact/one-past boundary at ~4*10^40 magnitude\n"
