(* Extraction of the concrete stage-2 checker and its Orchestration adapter for
   an executable exercise ONLY.

   Z and nat are extracted to OCaml [int], string to OCaml [string]: this build
   has no bignum or Coq-string dependency and links directly.

   THIS IS NOT THE EXACT-INTEGER VERIFIER.  It carries no overflow-safety
   guarantee: the machine-int arithmetic here can wrap, unlike the Coq [Z] the
   proofs are about.  The exact-integer verifier extracts [Z] to an
   arbitrary-precision type (deferred -- the verifying environment's [zarith]
   ships no interface files).  Use this extraction to exercise control flow and
   verdicts, not for any assurance claim. *)
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt
  ExtrOcamlNativeString.
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
