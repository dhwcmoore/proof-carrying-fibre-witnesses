(* Closure-report obligation 3 (arbitrary-precision extraction), the
   FibreWitnessKernel.v half: ExtractFibreWitnessKernel.v extracts Policy /
   AuditContext / domainb / quantise / target / observation with
   ExtrOcamlZBigInt + ExtrOcamlNatBigInt, so every Z entry of a
   Vec Z n = Vector.t Z n is a Big_int_Z.big_int, not a native OCaml int.
   Companion to test_orchestration_bigint.ml; see that file's header for the
   general rationale (magnitudes here exceed max_int on a 64-bit system). *)

module S = Extracted_fibre_witness_kernel

let big = Big_int_Z.big_int_of_string
let bi = Big_int_Z.big_int_of_int
let eqbi = Big_int_Z.eq_big_int
let fail msg = Printf.printf "FAIL: %s\n" msg; exit 1

let rec vec_of_list (xs : Big_int_Z.big_int list) : Big_int_Z.big_int S.vec =
  match xs with
  | [] -> S.Nil
  | x :: tl -> S.Cons (x, bi (List.length tl), vec_of_list tl)

let rec vec_to_list (v : Big_int_Z.big_int S.vec) : Big_int_Z.big_int list =
  match v with
  | S.Nil -> []
  | S.Cons (x, _, tl) -> x :: vec_to_list tl

let vec_eq (a : Big_int_Z.big_int S.vec) (b : Big_int_Z.big_int S.vec) : bool =
  try List.for_all2 eqbi (vec_to_list a) (vec_to_list b)
  with Invalid_argument _ -> false

let huge_pos = big "40000000000000000000000000000000000000000" (* 4*10^40 *)
let huge_neg = big "-40000000000000000000000000000000000000001"

let () =
  (* ---- domainb / quantise / target: a CheckedWitness-shaped scenario
     (FibreWitnessKernel.CheckedWitness) at magnitudes beyond int64 -- both
     x and y in domain, quantised observations agree (quantise here is a
     constant function, so any two inputs trivially agree), targets differ
     because they read the sign of a huge value in each direction. ---- *)
  let policy : S.policy =
    { S.domainb = (fun _ -> true);
      S.quantise = (fun _ -> vec_of_list [ bi 0 ]);
      S.target =
        (fun v ->
          match v with
          | S.Cons (h, _, _) -> Big_int_Z.sign_big_int h > 0
          | S.Nil -> false) } in
  let x = vec_of_list [ huge_pos ] and y = vec_of_list [ huge_neg ] in
  let o_x = vec_of_list [ huge_pos ] and o_y = vec_of_list [ huge_neg ] in
  if not (S.domainb (bi 1) (bi 1) policy x) then fail "domainb x";
  if not (S.domainb (bi 1) (bi 1) policy y) then fail "domainb y";
  if not (S.target (bi 1) (bi 1) policy x) then fail "target x should be true (positive)";
  if S.target (bi 1) (bi 1) policy y then fail "target y should be false (negative)";
  if not (vec_eq (S.quantise (bi 1) (bi 1) policy o_x) (S.quantise (bi 1) (bi 1) policy o_y))
  then fail "quantised observations should agree (constant quantiser)";

  (* ---- observation = model . preproc, with a genuine arithmetic transform
     (negation) applied to a huge Z value inside the vector -- confirms
     arithmetic on vector elements, not just pass-through storage, stays
     exact at this magnitude. ---- *)
  let negate_vec (v : Big_int_Z.big_int S.vec) : Big_int_Z.big_int S.vec =
    vec_of_list (List.map Big_int_Z.minus_big_int (vec_to_list v)) in
  let id_vec (v : Big_int_Z.big_int S.vec) : Big_int_Z.big_int S.vec = v in
  let ctx : S.auditContext =
    { S.context_policy = policy; S.preproc = negate_vec; S.model = id_vec } in
  let observed = S.observation (bi 1) (bi 1) (bi 1) ctx x in
  if not (vec_eq observed (vec_of_list [ Big_int_Z.minus_big_int huge_pos ]))
  then fail "observation (negate . identity) did not preserve magnitude exactly";

  print_string
    "PASS: arbitrary-precision extraction (ExtractFibreWitnessKernel.v, \
     Big_int_Z) -- domainb/quantise/target reproduce a CheckedWitness-shaped \
     scenario and observation's negation transform stays exact, all at \
     ~4*10^40 magnitude\n"
