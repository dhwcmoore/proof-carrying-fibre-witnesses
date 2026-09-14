(* Exercises the extracted F.3 stage-1 parser wrapper (Stage1Wrapper.op_stage1_wrapper):
   parse-failure rejection, the B4-before-B5 and B5-before-C1 precedence, and the
   digest/candidate/index binding on a successful parse -- plus (closure-report
   obligation 3) the B5 integer-literal-representability boundary, and
   candidate/index data, at magnitudes beyond a native 63-bit OCaml int.

   Z / nat now extract to Big_int_Z.big_int (see ExtractStage2.v): true
   arbitrary precision, not merely a wider fixed-width int. *)

module S = Extracted_stage2

let bi = Big_int_Z.big_int_of_int
let big = Big_int_Z.big_int_of_string
let eqbi = Big_int_Z.eq_big_int
let list_eqbi a b = try List.for_all2 eqbi a b with Invalid_argument _ -> false

(* well beyond max_int (2^62 - 1 on a 64-bit system) *)
let huge_threshold = big "40000000000000000000000000000000000000000" (* 4*10^40 *)
let huge_threshold_plus1 = Big_int_Z.succ_big_int huge_threshold
let huge_neg = big "-40000000000000000000000000000000000000001"
let huge_index = big "100000000000000000000000000000" (* 10^29 *)

let hd1 : Big_int_Z.big_int S.vec -> Big_int_Z.big_int =
  function S.Cons (z, _, _) -> z | S.Nil -> bi 0
let id_v (x : Big_int_Z.big_int S.vec) : Big_int_Z.big_int S.vec = x

(* the original "<> 0" target, converted baseline: `bi 0`/`eqbi`, unchanged
   behaviour for every pre-existing test case ([0], [2], [200]). *)
let ctx : S.auditContext =
  { S.context_policy =
      { S.domainb = (fun _ -> true); S.quantise = id_v;
        S.target = (fun v -> not (eqbi (hd1 v) (bi 0))) };
    S.preproc = id_v; S.model = id_v }

(* a SEPARATE, sign-based context used ONLY by the new huge signed-coordinate
   case below (target(huge_pos) <> target(huge_neg), needed to reach a valid
   Pending there) -- never substituted for `ctx`, so no pre-existing case's
   expected result depends on it. *)
let ctx_sign : S.auditContext =
  { S.context_policy =
      { S.domainb = (fun _ -> true); S.quantise = id_v;
        S.target = (fun v -> Big_int_Z.sign_big_int (hd1 v) > 0) };
    S.preproc = id_v; S.model = id_v }

(* B5: literals up to 100 are representable (unchanged -- every pre-existing
   test case below still runs through this exact function with this exact
   threshold, so their expected results are unaffected). *)
let parse_literal (z : Big_int_Z.big_int) : Big_int_Z.big_int option =
  if Big_int_Z.le_big_int z (bi 100) then Some z else None

(* a SEPARATE representability check with a ~4*10^40 threshold, used only by
   the new beyond-63-bit cases below -- never substituted for the original,
   so no pre-existing case's expected result can be affected by it. *)
let parse_literal_huge (z : Big_int_Z.big_int) : Big_int_Z.big_int option =
  if Big_int_Z.le_big_int z huge_threshold then Some z else None

let semd (_ : S.parsed_candidate) : S.digest = "semd"

(* submission_wire_length / max_wire_bytes: converted baseline (bi 1 / bi 100,
   unchanged from the pre-existing values) -- lower_parse is F.3-external and
   stubbed below (it ignores cfg/pd/sub entirely), so these fields are never
   examined by op_stage1_wrapper's own logic here regardless of magnitude;
   setting them to an unexamined huge value would add no meaningful coverage.
   The genuine "configured bounds" arithmetic boundary
   (Stage2Adapter.fuel_ok's 4 * model_call_fuel <=? max_fuel_per_candidate)
   is covered in test_stage2.ml instead. *)
let sub : S.candidate_submission =
  { S.submission_wire = "w"; S.submission_wire_length = bi 1;
    S.submission_digest = "sub-dg" }

let lower (result : (S.b_reason, Big_int_Z.big_int list * Big_int_Z.big_int list) S.sum)
  : S.verifier_config -> S.policy_document -> S.candidate_submission ->
    (S.b_reason, Big_int_Z.big_int list * Big_int_Z.big_int list) S.sum =
  fun _ _ _ -> result

let sched : S.fuel_schedule =
  { S.commitment_parse_fuel = bi 0; S.signature_verify_fuel = bi 0;
    S.manifest_bind_fuel = bi 0; S.record_bind_fuel = bi 0;
    S.preflight_fuel = bi 0; S.stage1_base_fuel = bi 1;
    S.stage1_per_byte_fuel = bi 0 }
let cfg : S.verifier_config =
  { S.max_candidates = bi 10; S.max_wire_bytes = bi 100;
    S.max_transcript_bytes = bi 100; S.max_fuel = bi 1000;
    S.model_call_fuel = bi 1; S.max_fuel_per_candidate = bi 100;
    S.schedule = sched;
    S.config_trust_anchor = { S.ta_authorised_signers = []; S.ta_keys = [] } }

let cand_id (_ : S.candidate_submission) : S.digest = "cid"

let run ?(ctx = ctx) ?(parse_literal = parse_literal) ?(i = bi 7) lp =
  S.op_stage1_wrapper (bi 1) (bi 1) (bi 1) ctx (lower lp) parse_literal semd cand_id
    cfg "pd" "p" i sub

let fail msg = Printf.printf "FAIL: %s\n" msg; exit 1

let () =
  (* 1. lower-tier structural failure *)
  (match (run (S.Inl S.MalformedStructure)).S.s1_verdict with
   | S.S1Rejected S.MalformedStructure -> ()
   | _ -> fail "expected S1Rejected MalformedStructure");

  (* 2. B4: wrong dimension *)
  (match (run (S.Inr ([bi 0], [bi 2; bi 2]))).S.s1_verdict with
   | S.S1Rejected S.InputStructureError -> ()
   | _ -> fail "expected S1Rejected InputStructureError (B4)");

  (* 3. B4 BEFORE B5: bad x literal AND wrong y dimension -> B4 wins *)
  (match (run (S.Inr ([bi 200], [bi 2; bi 2]))).S.s1_verdict with
   | S.S1Rejected S.InputStructureError -> ()
   | S.S1Rejected S.MalformedIntegerLiteral -> fail "B5 ran before B4"
   | _ -> fail "expected S1Rejected InputStructureError (B4 before B5)");

  (* 4. B5: unrepresentable literal, dimensions ok *)
  (match (run (S.Inr ([bi 200], [bi 2]))).S.s1_verdict with
   | S.S1Rejected S.MalformedIntegerLiteral -> ()
   | _ -> fail "expected S1Rejected MalformedIntegerLiteral (B5)");

  (* 5. B5 BEFORE C1: both literals unrepresentable and would be equal -> B5 wins *)
  (match (run (S.Inr ([bi 200], [bi 200]))).S.s1_verdict with
   | S.S1Rejected S.MalformedIntegerLiteral -> ()
   | S.S1NotAWitness S.InputsEqual -> fail "C1 ran before B5"
   | _ -> fail "expected S1Rejected MalformedIntegerLiteral (B5 before C1)");

  (* 6. success: pending, with candidate + both digests + index bound *)
  (match (run (S.Inr ([bi 0], [bi 2]))).S.s1_verdict with
   | S.S1Pending ps
       when eqbi ps.S.pending_index (bi 7)
         && ps.S.pending_submission_digest = "sub-dg"
         && ps.S.pending_semantic_digest = "semd"
         && list_eqbi ps.S.pending_candidate.S.candidate_x [bi 0]
         && list_eqbi ps.S.pending_candidate.S.candidate_y [bi 2]
         && ps.S.pending_findings = [] -> ()
   | S.S1Pending _ -> fail "pending fields not bound to the raw submission"
   | _ -> fail "expected S1Pending");

  (* the whole stage1_result also carries the raw digest and index *)
  let r = run (S.Inr ([bi 0], [bi 2])) in
  if not (eqbi r.S.s1_index (bi 7)) || r.S.s1_submission_digest <> "sub-dg"
     || r.S.s1_findings <> []
  then fail "stage1_result fields not preserved";

  (* ---- beyond-63-bit: B5 accepts exactly at a ~4*10^40 representability
     boundary ---- *)
  (match (run ~parse_literal:parse_literal_huge
            (S.Inr ([huge_threshold], [bi 2]))).S.s1_verdict with
   | S.S1Rejected S.MalformedIntegerLiteral ->
       fail "B5 wrongly rejected a literal exactly at the huge boundary"
   | S.S1Pending _ | S.S1NotAWitness _ -> ()
   | S.S1Rejected _ -> fail "unexpected rejection at the huge B5 boundary");

  (* ---- beyond-63-bit: one unit past that same boundary must be rejected
     (B5) -- no silent acceptance from precision loss ---- *)
  (match (run ~parse_literal:parse_literal_huge
            (S.Inr ([huge_threshold_plus1], [bi 2]))).S.s1_verdict with
   | S.S1Rejected S.MalformedIntegerLiteral -> ()
   | _ -> fail "expected MalformedIntegerLiteral one unit past the huge B5 \
                boundary");

  (* ---- beyond-63-bit: a full success path with a huge POSITIVE x
     coordinate, a huge NEGATIVE y coordinate (both representable -- B5 here
     is an upper bound only, same as the original), and a huge pending
     index, all surviving into the bound pending_submission bit-exact.
     Needs ctx_sign (the default ctx's nonzero-based target would agree on
     both huge_threshold and huge_neg -- both nonzero -- and reject via C5
     TargetsAgree instead of reaching Pending). ---- *)
  (match (run ~ctx:ctx_sign ~parse_literal:parse_literal_huge ~i:huge_index
            (S.Inr ([huge_threshold], [huge_neg]))).S.s1_verdict with
   | S.S1Pending ps
       when eqbi ps.S.pending_index huge_index
         && list_eqbi ps.S.pending_candidate.S.candidate_x [huge_threshold]
         && list_eqbi ps.S.pending_candidate.S.candidate_y [huge_neg] -> ()
   | S.S1Pending _ -> fail "huge Pending: index or coordinates corrupted"
   | _ -> fail "expected S1Pending (huge positive x, huge negative y, huge \
                index)");

  print_string "PASS: stage-1 wrapper -- structural reject, B4<B5, B5<C1, \
                digest/candidate/index binding on success; plus B5 \
                equality/one-past-boundary and huge positive/negative \
                candidate coordinates + huge pending index at ~4*10^40 / \
                ~10^29 magnitude\n"
