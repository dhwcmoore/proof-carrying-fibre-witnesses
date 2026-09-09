From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlZBigInt
  ExtrOcamlNatBigInt.
From PCFW Require Import Orchestration.

Extraction Language OCaml.
Extraction "ocaml/extracted_orchestration.ml"
  validate_campaign replay decide assess_validated verdict_of.
