From PCFW Require Import Orchestration TranscriptDigest ManifestPipeline.

(* op_transcript_digest: the operation itself, and preservation of every
   other primitive_ops field *)
Print Assumptions TranscriptDigest.set_transcript_digest_field.
Print Assumptions TranscriptDigest.set_transcript_digest_preserves_others.
Print Assumptions TranscriptDigest.op_transcript_digest_deterministic.

(* non-interference: validate_campaign / replay / verdict are unaffected *)
Print Assumptions TranscriptDigest.validate_campaign_indep_of_transcript_digest.
Print Assumptions TranscriptDigest.replay_indep_of_transcript_digest.
Print Assumptions TranscriptDigest.decide_verdict_indep_of_tev.
Print Assumptions TranscriptDigest.verdict_indep_of_transcript_digest.

(* evidence projections and binding *)
Print Assumptions TranscriptDigest.decide_transcript_evidence.
Print Assumptions TranscriptDigest.live_evidence_uses_typed_transcript_digest.
Print Assumptions TranscriptDigest.offline_evidence_uses_both_digests.

(* malformed-transcript separation *)
Print Assumptions TranscriptDigest.malformed_evidence_uses_only_wire_digest.
Print Assumptions TranscriptDigest.malformed_assess_indep_of_transcript_digest.
Print Assumptions TranscriptDigest.malformed_no_typed_digest.

(* live/offline agreement on the typed digest *)
Print Assumptions TranscriptDigest.live_offline_typed_digest_agree.

(* agreement with the normative denotation (transcript_digest_v1 abstract) *)
Print Assumptions TranscriptDigest.transcript_digest_v1_deterministic.
Print Assumptions TranscriptDigest.live_evidence_digest_agrees.
Print Assumptions TranscriptDigest.offline_evidence_digest_agrees.

(* pipeline integration *)
Print Assumptions ManifestPipeline.pipeline_ops_transcript_digest.
Print Assumptions ManifestPipeline.pipeline_transcript_digest_agrees.
