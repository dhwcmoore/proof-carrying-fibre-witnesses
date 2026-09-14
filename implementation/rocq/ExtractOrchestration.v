(** The arbitrary-precision extraction of Orchestration.v (closure-report
    obligation 3: "Complete extracted-OCaml compilation, linking and
    execution with the required arbitrary-precision library").

    Z and nat extract to Big_int_Z.big_int (Zarith's arbitrary-precision
    representation), NOT OCaml's native, fixed-width [int]. This is ONE OF
    TWO arbitrary-precision extractions in the project -- the other is
    ExtractFibreWitnessKernel.v (also ExtrOcamlZBigInt / ExtrOcamlNatBigInt).
    The remaining three active extractions -- ExtractStage2.v,
    ExtractManifestAuthentication.v, ExtractTranscriptDigest.v -- use
    ExtrOcamlNatInt / ExtrOcamlZInt and say so in their own headers; for
    those, fuel/budget/index/candidate-coordinate values remain silently
    bounded by machine word size.

    Genuinely compiled, linked and EXECUTED against zarith by
    ocaml/test_orchestration_bigint.ml (Makefile `test:` target) -- not
    merely coqc'd, which is all this file did before this revision. See
    that harness's header for exactly what is and is not exercised. *)

From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlZBigInt
  ExtrOcamlNatBigInt ExtrOcamlNativeString.
From PCFW Require Import Orchestration.

Extraction Language OCaml.
Extraction "ocaml/extracted_orchestration.ml"
  validate_campaign replay decide assess_validated verdict_of.
