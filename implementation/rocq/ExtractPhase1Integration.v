(* One extraction closure for the EXISTING pipeline builder, assessment and
   evidence projections. No new formal definitions or trust assumptions.
   The harness has an explicit empty-campaign/typed-input boundary; the digest
   hook stays abstract and no model/parser/capture hook may be called. *)
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatBigInt
  ExtrOcamlZBigInt ExtrOcamlNativeString.
From PCFW Require Import Orchestration CanonicalV1 RecordCrosscheck ManifestPipeline TranscriptDigest.

Extraction Language OCaml.
Extraction "ocaml/extracted_phase1_integration.ml"
  pipeline_ops validate_campaign assess_validated verdict_of
  set_transcript_digest outcome_transcript_evidence typed_digest_of
  render_manifest campaign_manifest_digest parse_record_full_impl.
