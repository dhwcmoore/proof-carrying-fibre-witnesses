(* Exercises the extracted F.3 stage-1 parser wrapper (Stage1Wrapper.op_stage1_wrapper):
   parse-failure rejection, the B4-before-B5 and B5-before-C1 precedence, and the
   digest/candidate/index binding on a successful parse.

   Z / nat -> OCaml int (see ExtractStage2.v): test harness only. *)

module S = Extracted_stage2

let hd1 : int S.vec -> int = function S.Cons (z, _, _) -> z | S.Nil -> 0
let id_v (x : int S.vec) : int S.vec = x

let ctx : S.auditContext =
  { S.context_policy =
      { S.domainb = (fun _ -> true); S.quantise = id_v;
        S.target = (fun v -> hd1 v <> 0) };
    S.preproc = id_v; S.model = id_v }

(* B5: literals up to 100 are representable *)
let parse_literal (z : int) : int option = if z <= 100 then Some z else None
let semd (_ : S.parsed_candidate) : S.digest = "semd"

let sub : S.candidate_submission =
  { S.submission_wire = "w"; S.submission_wire_length = 1; S.submission_digest = "sub-dg" }

let lower (result : (S.b_reason, int list * int list) S.sum)
  : S.verifier_config -> S.policy_document -> S.candidate_submission ->
    (S.b_reason, int list * int list) S.sum =
  fun _ _ _ -> result

let sched : S.fuel_schedule =
  { S.commitment_parse_fuel = 0; S.signature_verify_fuel = 0;
    S.manifest_bind_fuel = 0; S.record_bind_fuel = 0; S.preflight_fuel = 0;
    S.stage1_base_fuel = 1; S.stage1_per_byte_fuel = 0 }
let cfg : S.verifier_config =
  { S.max_candidates = 10; S.max_wire_bytes = 100; S.max_transcript_bytes = 100;
    S.max_fuel = 1000; S.model_call_fuel = 1; S.max_fuel_per_candidate = 100;
    S.schedule = sched; S.config_trust_anchor = { S.ta_authorised_signers = []; S.ta_keys = [] } }

let run lp =
  S.op_stage1_wrapper 1 1 1 ctx (lower lp) parse_literal semd cfg "pd" "p" 7 sub

let fail msg = Printf.printf "FAIL: %s\n" msg; exit 1

let () =
  (* 1. lower-tier structural failure *)
  (match (run (S.Inl S.MalformedStructure)).S.s1_verdict with
   | S.S1Rejected S.MalformedStructure -> ()
   | _ -> fail "expected S1Rejected MalformedStructure");

  (* 2. B4: wrong dimension *)
  (match (run (S.Inr ([0], [2; 2]))).S.s1_verdict with
   | S.S1Rejected S.InputStructureError -> ()
   | _ -> fail "expected S1Rejected InputStructureError (B4)");

  (* 3. B4 BEFORE B5: bad x literal AND wrong y dimension -> B4 wins *)
  (match (run (S.Inr ([200], [2; 2]))).S.s1_verdict with
   | S.S1Rejected S.InputStructureError -> ()
   | S.S1Rejected S.MalformedIntegerLiteral -> fail "B5 ran before B4"
   | _ -> fail "expected S1Rejected InputStructureError (B4 before B5)");

  (* 4. B5: unrepresentable literal, dimensions ok *)
  (match (run (S.Inr ([200], [2]))).S.s1_verdict with
   | S.S1Rejected S.MalformedIntegerLiteral -> ()
   | _ -> fail "expected S1Rejected MalformedIntegerLiteral (B5)");

  (* 5. B5 BEFORE C1: both literals unrepresentable and would be equal -> B5 wins *)
  (match (run (S.Inr ([200], [200]))).S.s1_verdict with
   | S.S1Rejected S.MalformedIntegerLiteral -> ()
   | S.S1NotAWitness S.InputsEqual -> fail "C1 ran before B5"
   | _ -> fail "expected S1Rejected MalformedIntegerLiteral (B5 before C1)");

  (* 6. success: pending, with candidate + both digests + index bound *)
  (match (run (S.Inr ([0], [2]))).S.s1_verdict with
   | S.S1Pending ps
       when ps.S.pending_index = 7
         && ps.S.pending_submission_digest = "sub-dg"
         && ps.S.pending_semantic_digest = "semd"
         && ps.S.pending_candidate.S.candidate_x = [0]
         && ps.S.pending_candidate.S.candidate_y = [2]
         && ps.S.pending_findings = [] -> ()
   | S.S1Pending _ -> fail "pending fields not bound to the raw submission"
   | _ -> fail "expected S1Pending");

  (* the whole stage1_result also carries the raw digest and index *)
  let r = run (S.Inr ([0], [2])) in
  if r.S.s1_index <> 7 || r.S.s1_submission_digest <> "sub-dg" || r.S.s1_findings <> []
  then fail "stage1_result fields not preserved";

  print_string "PASS: stage-1 wrapper -- structural reject, B4<B5, B5<C1, \
                digest/candidate/index binding on success\n"
