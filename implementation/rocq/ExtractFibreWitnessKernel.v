From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlZBigInt
  ExtrOcamlNatBigInt.
From PCFW Require Import FibreWitnessKernel.

Extraction Language OCaml.
Extraction "ocaml/extracted_fibre_witness_kernel.ml"
  domainb quantise target observation.

