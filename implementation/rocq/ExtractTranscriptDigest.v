(* Extraction of the op_transcript_digest interface (TranscriptDigest.v) for
   an executable exercise ONLY -- a SEPARATE, self-contained extraction unit
   (its own output file) so it shares no dependency closure with
   [ExtractStage2.v] and cannot collide with -- or perturb the OCaml type
   naming of -- the unrelated `FibreWitnessKernel.Policy` record already
   extracted there.

   nat and Z use the kernel's Zarith mappings. The digest hook remains abstract;
   bigint input preservation is not a concrete transcript digest or faithfulness
   implementation. *)
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatBigInt ExtrOcamlZBigInt
  ExtrOcamlNativeString.
From PCFW Require Import Orchestration TranscriptDigest.

Extraction Language OCaml.
Extraction "ocaml/extracted_transcript_digest.ml"
  assess_validated set_transcript_digest outcome_transcript_evidence
  typed_digest_of op_transcript_digest.
