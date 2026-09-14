(* Exercises the extracted concrete stage-1 semantic checker
   (Stage1.stage1_semantic_check): a valid Pending, the C1/C2/C3/C5 rejection
   reasons, their precedence (an earlier check wins over a later one), the
   B4 dimension check winning over C1 -- plus (closure-report obligation 3)
   candidate coordinates and the pending index at magnitudes beyond a native
   63-bit OCaml int.

   Z / nat now extract to Big_int_Z.big_int (see ExtractStage2.v): true
   arbitrary precision, not merely a wider fixed-width int. *)

module S = Extracted_stage2

let bi = Big_int_Z.big_int_of_int
let big = Big_int_Z.big_int_of_string
let eqbi = Big_int_Z.eq_big_int
let list_eqbi a b = try List.for_all2 eqbi a b with Invalid_argument _ -> false

(* well beyond max_int (2^62 - 1 on a 64-bit system) *)
let huge_pos = big "40000000000000000000000000000000000000000" (* 4*10^40 *)
let huge_pos_plus1 = Big_int_Z.succ_big_int huge_pos
let huge_neg = big "-40000000000000000000000000000000000000001"
let huge_index = big "100000000000000000000000000000" (* 10^29 *)

let v1 (z : Big_int_Z.big_int) : Big_int_Z.big_int S.vec = S.of_list [z]
let hd1 : Big_int_Z.big_int S.vec -> Big_int_Z.big_int =
  function S.Cons (z, _, _) -> z | S.Nil -> bi 0
let id_v (x : Big_int_Z.big_int S.vec) : Big_int_Z.big_int S.vec = x

let ctx ~domainb ~target : S.auditContext =
  { S.context_policy = { S.domainb; S.quantise = id_v; S.target };
    S.preproc = id_v; S.model = id_v }

let all_true : Big_int_Z.big_int S.vec -> bool = fun _ -> true
let dom_is0 : Big_int_Z.big_int S.vec -> bool =
  fun v -> eqbi (hd1 v) (bi 0)        (* [0] in, [2] out *)
let tgt_neq0 : Big_int_Z.big_int S.vec -> bool =
  fun v -> not (eqbi (hd1 v) (bi 0))
let tgt_true : Big_int_Z.big_int S.vec -> bool = fun _ -> true
(* sign-based target: distinguishes a huge positive from a huge negative
   coordinate without ever comparing them to a small literal *)
let tgt_sign : Big_int_Z.big_int S.vec -> bool =
  fun v -> Big_int_Z.sign_big_int (hd1 v) > 0

let cand cx cy : S.parsed_candidate =
  { S.pc_candidate_id = "c"; S.candidate_x = cx; S.candidate_y = cy }

let run ?(domainb = all_true) ?(target = tgt_neq0) ?(i = bi 7) c =
  S.stage1_semantic_check (bi 1) (bi 1) (bi 1) (ctx ~domainb ~target) "sd" "cd" i c

let fail msg = Printf.printf "FAIL: %s\n" msg; exit 1

let () =
  (* valid Pending *)
  (match run (cand [bi 0] [bi 2]) with
   | S.S1Pending ps when eqbi ps.S.pending_index (bi 7)
       && list_eqbi ps.S.pending_candidate.S.candidate_x [bi 0]
       && list_eqbi ps.S.pending_candidate.S.candidate_y [bi 2] -> ()
   | _ -> fail "expected S1Pending index 7");

  (* C1 InputsEqual *)
  (match run (cand [bi 0] [bi 0]) with
   | S.S1NotAWitness S.InputsEqual -> () | _ -> fail "expected InputsEqual");

  (* C1 precedence over C2: x = y AND x not in domain -> still InputsEqual *)
  (match run ~domainb:dom_is0 (cand [bi 2] [bi 2]) with
   | S.S1NotAWitness S.InputsEqual -> ()
   | S.S1NotAWitness S.XNotInDomain -> fail "C2 ran before C1"
   | _ -> fail "expected InputsEqual (C1 before C2)");

  (* C2 XNotInDomain *)
  (match run ~domainb:dom_is0 (cand [bi 2] [bi 0]) with
   | S.S1NotAWitness S.XNotInDomain -> () | _ -> fail "expected XNotInDomain");

  (* C2 precedence over C5: x not in domain AND targets agree -> XNotInDomain *)
  (match run ~domainb:dom_is0 ~target:tgt_true (cand [bi 2] [bi 0]) with
   | S.S1NotAWitness S.XNotInDomain -> ()
   | S.S1NotAWitness S.TargetsAgree -> fail "C5 ran before C2"
   | _ -> fail "expected XNotInDomain (C2 before C5)");

  (* C3 YNotInDomain *)
  (match run ~domainb:dom_is0 (cand [bi 0] [bi 2]) with
   | S.S1NotAWitness S.YNotInDomain -> () | _ -> fail "expected YNotInDomain");

  (* C5 TargetsAgree *)
  (match run ~target:tgt_true (cand [bi 0] [bi 2]) with
   | S.S1NotAWitness S.TargetsAgree -> () | _ -> fail "expected TargetsAgree");

  (* B4: malformed x dimension -> InputStructureError *)
  (match run (cand [bi 0; bi 0] [bi 2]) with
   | S.S1Rejected S.InputStructureError -> ()
   | _ -> fail "expected S1Rejected InputStructureError (bad x length)");

  (* B4: malformed y dimension -> InputStructureError *)
  (match run (cand [bi 0] [bi 2; bi 2]) with
   | S.S1Rejected S.InputStructureError -> ()
   | _ -> fail "expected S1Rejected InputStructureError (bad y length)");

  (* B4 precedence over C1: both malformed and equal -> InputStructureError *)
  (match run (cand [bi 0; bi 0] [bi 0; bi 0]) with
   | S.S1Rejected S.InputStructureError -> ()
   | S.S1NotAWitness S.InputsEqual -> fail "C1 ran before B4"
   | _ -> fail "expected S1Rejected InputStructureError (B4 before C1)");

  (* ---- beyond-63-bit: C1 equality at ~4*10^40 magnitude ---- *)
  (match run (cand [huge_pos] [huge_pos]) with
   | S.S1NotAWitness S.InputsEqual -> ()
   | _ -> fail "expected InputsEqual at huge magnitude (equality must not \
                spuriously fail at scale)");

  (* ---- beyond-63-bit: one unit past that same huge value must NOT be
     treated as equal (no false positive from precision loss), and control
     correctly falls through to C5 (both coordinates share the same sign,
     so tgt_sign agrees on both) ---- *)
  (match run ~target:tgt_sign (cand [huge_pos] [huge_pos_plus1]) with
   | S.S1NotAWitness S.TargetsAgree -> ()
   | S.S1NotAWitness S.InputsEqual ->
       fail "huge_pos and huge_pos+1 spuriously treated as equal"
   | _ -> fail "expected TargetsAgree (huge_pos vs huge_pos+1, same sign)");

  (* ---- beyond-63-bit: a valid Pending witness with one huge POSITIVE and
     one huge NEGATIVE coordinate, and a huge pending index -- all three
     survive the checker and come back bit-exact ---- *)
  (match run ~target:tgt_sign ~i:huge_index (cand [huge_pos] [huge_neg]) with
   | S.S1Pending ps when eqbi ps.S.pending_index huge_index
       && list_eqbi ps.S.pending_candidate.S.candidate_x [huge_pos]
       && list_eqbi ps.S.pending_candidate.S.candidate_y [huge_neg] -> ()
   | S.S1Pending _ -> fail "huge Pending: index or coordinates corrupted"
   | _ -> fail "expected S1Pending (huge positive x, huge negative y, \
                differing sign-based targets)");

  print_string "PASS: stage-1 semantic checker -- valid Pending, C1/C2/C3/C5, \
                precedence C1<C2, C2<C5, B4<C1; plus C1 equality/one-past-\
                boundary and huge positive/negative candidate coordinates + \
                huge pending index at ~4*10^40 / ~10^29 magnitude\n"
