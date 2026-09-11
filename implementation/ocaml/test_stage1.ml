(* Exercises the extracted concrete stage-1 semantic checker
   (Stage1.stage1_semantic_check): a valid Pending, the C1/C2/C3/C5 rejection
   reasons, their precedence (an earlier check wins over a later one), and the
   B4 dimension check winning over C1.

   Z / nat -> OCaml int (see ExtractStage2.v): test harness only. *)

module S = Extracted_stage2

let v1 (z : int) : int S.vec = S.of_list [z]
let hd1 : int S.vec -> int = function S.Cons (z, _, _) -> z | S.Nil -> 0
let id_v (x : int S.vec) : int S.vec = x

let ctx ~domainb ~target : S.auditContext =
  { S.context_policy = { S.domainb; S.quantise = id_v; S.target };
    S.preproc = id_v; S.model = id_v }

let all_true : int S.vec -> bool = fun _ -> true
let dom_is0 : int S.vec -> bool = fun v -> hd1 v = 0        (* [0] in, [2] out *)
let tgt_neq0 : int S.vec -> bool = fun v -> hd1 v <> 0
let tgt_true : int S.vec -> bool = fun _ -> true

let cand cx cy : S.parsed_candidate = { S.pc_candidate_id = "c"; S.candidate_x = cx; S.candidate_y = cy }

let run ?(domainb = all_true) ?(target = tgt_neq0) c =
  S.stage1_semantic_check 1 1 1 (ctx ~domainb ~target) "sd" "cd" 7 c

let fail msg = Printf.printf "FAIL: %s\n" msg; exit 1

let () =
  (* valid Pending *)
  (match run (cand [0] [2]) with
   | S.S1Pending ps when ps.S.pending_index = 7
       && ps.S.pending_candidate.S.candidate_x = [0]
       && ps.S.pending_candidate.S.candidate_y = [2] -> ()
   | _ -> fail "expected S1Pending index 7");

  (* C1 InputsEqual *)
  (match run (cand [0] [0]) with
   | S.S1NotAWitness S.InputsEqual -> () | _ -> fail "expected InputsEqual");

  (* C1 precedence over C2: x = y AND x not in domain -> still InputsEqual *)
  (match run ~domainb:dom_is0 (cand [2] [2]) with
   | S.S1NotAWitness S.InputsEqual -> ()
   | S.S1NotAWitness S.XNotInDomain -> fail "C2 ran before C1"
   | _ -> fail "expected InputsEqual (C1 before C2)");

  (* C2 XNotInDomain *)
  (match run ~domainb:dom_is0 (cand [2] [0]) with
   | S.S1NotAWitness S.XNotInDomain -> () | _ -> fail "expected XNotInDomain");

  (* C2 precedence over C5: x not in domain AND targets agree -> XNotInDomain *)
  (match run ~domainb:dom_is0 ~target:tgt_true (cand [2] [0]) with
   | S.S1NotAWitness S.XNotInDomain -> ()
   | S.S1NotAWitness S.TargetsAgree -> fail "C5 ran before C2"
   | _ -> fail "expected XNotInDomain (C2 before C5)");

  (* C3 YNotInDomain *)
  (match run ~domainb:dom_is0 (cand [0] [2]) with
   | S.S1NotAWitness S.YNotInDomain -> () | _ -> fail "expected YNotInDomain");

  (* C5 TargetsAgree *)
  (match run ~target:tgt_true (cand [0] [2]) with
   | S.S1NotAWitness S.TargetsAgree -> () | _ -> fail "expected TargetsAgree");

  (* B4: malformed x dimension -> InputStructureError *)
  (match run (cand [0;0] [2]) with
   | S.S1Rejected S.InputStructureError -> ()
   | _ -> fail "expected S1Rejected InputStructureError (bad x length)");

  (* B4: malformed y dimension -> InputStructureError *)
  (match run (cand [0] [2;2]) with
   | S.S1Rejected S.InputStructureError -> ()
   | _ -> fail "expected S1Rejected InputStructureError (bad y length)");

  (* B4 precedence over C1: both malformed and equal -> InputStructureError *)
  (match run (cand [0;0] [0;0]) with
   | S.S1Rejected S.InputStructureError -> ()
   | S.S1NotAWitness S.InputsEqual -> fail "C1 ran before B4"
   | _ -> fail "expected S1Rejected InputStructureError (B4 before C1)");

  print_string "PASS: stage-1 semantic checker -- valid Pending, C1/C2/C3/C5, \
                precedence C1<C2, C2<C5, B4<C1\n"
