(* Extraction of the concrete stage-2 checker and its Orchestration adapter
   for an executable exercise.

   Closure-report obligation 3 (arbitrary-precision extracted OCaml): Z and
   nat extract to Big_int_Z.big_int (Zarith's arbitrary-precision
   representation), NOT OCaml's native, fixed-width [int] -- the same mapping now used by all current extraction units.
   Strings still extract to OCaml [string] (ExtrOcamlNativeString).

   Genuinely compiled, linked (against zarith) and EXECUTED by
   test_stage2.ml, test_stage1.ml, test_stage1_wrapper.ml,
   test_context_resolution.ml, and test_manifest_matching.ml (Makefile
   `test:` target). See those harnesses' headers for exactly what is and is
   not exercised at arbitrary-precision magnitude. *)
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatBigInt
  ExtrOcamlZBigInt ExtrOcamlNativeString.
From PCFW Require Import Stage1 Stage1Wrapper ContextResolution Stage2 Stage2Adapter
  ManifestMatching.

Extraction Language OCaml.
Extraction "ocaml/extracted_stage2.ml"
  stage2_check o_reason_of_fail fuel_ok
  Vector.of_list Vector.to_list
  adapter_stage2_check
  stage1_semantic_check
  op_stage1_wrapper wire_parse
  preflight_check eval_o3_check resolve
  descriptor_eqb manifest_policy_matches_impl manifest_context_matches_impl.
