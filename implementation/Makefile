.PHONY: check rocq ocaml check-kernel-trust check-source-trust assumptions test clean gate-tests release integer-audit differential byte-vectors policy-audit

# Keep inspection after compilation, including when the caller uses make -j.
.NOTPARALLEL:

# F.3 named-component libraries for the authentication harness (SHA-256, bignum).
# F.3 crypto-library locations. Override on the command line if needed, e.g.
#   make check OCAML_LIB=$(ocamlfind printconf destdir)
OCAML_LIB ?= $(shell opam var lib 2>/dev/null || echo $(HOME)/.opam/default/lib)
ZARITH ?= $(OCAML_LIB)/zarith
SHALIB ?= $(OCAML_LIB)/sha
export OCAML_LIB ZARITH SHALIB

check: check-source-trust rocq ocaml assumptions policy-audit test integer-audit differential byte-vectors

rocq:
	coqc -Q rocq PCFW rocq/FibreWitnessKernel.v
	coqc -Q rocq PCFW rocq/ExtractFibreWitnessKernel.v
	coqc -Q rocq PCFW rocq/Orchestration.v
	coqc -Q rocq PCFW rocq/ExtractOrchestration.v
	coqc -Q rocq PCFW rocq/CanonicalV1.v
	coqc -Q rocq PCFW rocq/Stage2.v
	coqc -Q rocq PCFW rocq/Stage2Adapter.v
	coqc -Q rocq PCFW rocq/Stage1.v
	coqc -Q rocq PCFW rocq/Stage1Invariant.v
	coqc -Q rocq PCFW rocq/Stage1Wrapper.v
	coqc -Q rocq PCFW rocq/ContextResolution.v
	coqc -Q rocq PCFW rocq/PipelineWiring.v
	coqc -Q rocq PCFW rocq/ValidationBinding.v
	coqc -Q rocq PCFW rocq/ManifestMatching.v
	coqc -Q rocq PCFW rocq/ManifestAuthentication.v
	coqc -Q rocq PCFW rocq/ManifestLedger.v
	coqc -Q rocq PCFW rocq/ManifestAudit.v
	coqc -Q rocq PCFW rocq/CampaignRecord.v
	coqc -Q rocq PCFW rocq/RecordCrosscheck.v
	coqc -Q rocq PCFW rocq/CompletenessWellformed.v
	coqc -Q rocq PCFW rocq/TranscriptDigest.v
	coqc -Q rocq PCFW rocq/ManifestPipeline.v
	coqc -Q rocq PCFW rocq/ExtractStage2.v
	coqc -Q rocq PCFW rocq/ExtractManifestAuthentication.v
	coqc -Q rocq PCFW rocq/ExtractTranscriptDigest.v
	coqc -Q rocq PCFW rocq/ExtractPhase1Integration.v
	coqchk -Q rocq PCFW PCFW.FibreWitnessKernel PCFW.Orchestration \
	  PCFW.Stage2 PCFW.Stage2Adapter PCFW.Stage1 PCFW.Stage1Invariant PCFW.Stage1Wrapper PCFW.ContextResolution PCFW.PipelineWiring PCFW.ValidationBinding PCFW.CanonicalV1 PCFW.ManifestMatching PCFW.ManifestAuthentication PCFW.ManifestLedger PCFW.ManifestAudit PCFW.CampaignRecord PCFW.RecordCrosscheck PCFW.CompletenessWellformed PCFW.TranscriptDigest PCFW.ManifestPipeline

assumptions: check-source-trust rocq
	python3 scripts/audit.py assumptions

policy-audit: rocq
	python3 scripts/policy_surface.py

ocaml: rocq
	ocamlc -I ocaml -I $(ZARITH) -c ocaml/extracted_orchestration.mli
	ocamlc -I ocaml -I $(ZARITH) -c ocaml/extracted_orchestration.ml

test: ocaml rocq
	ocamlc -I ocaml -I $(ZARITH) -c ocaml/extracted_fibre_witness_kernel.mli
	ocamlc -I ocaml -I $(ZARITH) -c ocaml/extracted_fibre_witness_kernel.ml
	ocamlc -custom -I ocaml -I $(ZARITH) $(ZARITH)/zarith.cma ocaml/extracted_fibre_witness_kernel.cmo ocaml/test_fibre_witness_kernel_bigint.ml -o ocaml/test_fibre_witness_kernel_bigint
	./ocaml/test_fibre_witness_kernel_bigint
	ocamlc -custom -I ocaml -I $(ZARITH) $(ZARITH)/zarith.cma ocaml/extracted_orchestration.cmo ocaml/test_orchestration_bigint.ml -o ocaml/test_orchestration_bigint
	./ocaml/test_orchestration_bigint
	ocamlc -custom -I ocaml -I $(ZARITH) $(ZARITH)/zarith.cma ocaml/extracted_orchestration.cmo ocaml/test_context_bundle.ml -o ocaml/test_context_bundle
	./ocaml/test_context_bundle
	ocamlc -I ocaml -I $(ZARITH) -c ocaml/extracted_stage2.mli
	ocamlc -I ocaml -I $(ZARITH) -c ocaml/extracted_stage2.ml
	ocamlc -custom -I ocaml -I $(ZARITH) $(ZARITH)/zarith.cma ocaml/extracted_stage2.cmo ocaml/test_stage2.ml -o ocaml/test_stage2
	./ocaml/test_stage2
	ocamlc -custom -I ocaml -I $(ZARITH) $(ZARITH)/zarith.cma ocaml/extracted_stage2.cmo ocaml/test_stage1.ml -o ocaml/test_stage1
	./ocaml/test_stage1
	ocamlc -custom -I ocaml -I $(ZARITH) $(ZARITH)/zarith.cma ocaml/extracted_stage2.cmo ocaml/test_stage1_wrapper.ml -o ocaml/test_stage1_wrapper
	./ocaml/test_stage1_wrapper
	ocamlc -custom -I ocaml -I $(ZARITH) $(ZARITH)/zarith.cma ocaml/extracted_stage2.cmo ocaml/test_context_resolution.ml -o ocaml/test_context_resolution
	./ocaml/test_context_resolution
	ocamlc -custom -I ocaml -I $(ZARITH) $(ZARITH)/zarith.cma ocaml/extracted_stage2.cmo ocaml/test_manifest_matching.ml -o ocaml/test_manifest_matching
	./ocaml/test_manifest_matching
	ocamlc -I ocaml -I $(ZARITH) -c ocaml/extracted_transcript_digest.mli
	ocamlc -I ocaml -I $(ZARITH) -c ocaml/extracted_transcript_digest.ml
	ocamlc -custom -I ocaml -I $(ZARITH) $(ZARITH)/zarith.cma ocaml/extracted_transcript_digest.cmo ocaml/test_transcript_digest.ml -o ocaml/test_transcript_digest
	./ocaml/test_transcript_digest
	ocamlc -I ocaml -I $(ZARITH) -c ocaml/extracted_manifest_auth.mli
	ocamlc -I ocaml -I $(ZARITH) -c ocaml/extracted_manifest_auth.ml
	ocamlc -I ocaml -I $(ZARITH) -I $(SHALIB) -c ocaml/manifest_crypto_fixture.ml
	ocamlc -custom -I ocaml -I $(ZARITH) -I $(SHALIB) $(ZARITH)/zarith.cma $(SHALIB)/sha.cma -cclib -lsha_stubs -cclib -L$(SHALIB) ocaml/manifest_crypto_fixture.cmo ocaml/extracted_manifest_auth.cmo ocaml/test_manifest_authentication.ml -o ocaml/test_manifest_authentication
	./ocaml/test_manifest_authentication
	ocamlc -I ocaml -I $(ZARITH) -c ocaml/extracted_phase1_integration.mli
	ocamlc -I ocaml -I $(ZARITH) -c ocaml/extracted_phase1_integration.ml
	ocamlc -I ocaml -I $(ZARITH) -c ocaml/phase1_bytes.ml
	ocamlc -custom -I ocaml -I $(ZARITH) -I $(SHALIB) $(ZARITH)/zarith.cma $(SHALIB)/sha.cma -cclib -lsha_stubs -cclib -L$(SHALIB) ocaml/manifest_crypto_fixture.cmo ocaml/extracted_phase1_integration.cmo ocaml/phase1_bytes.cmo ocaml/test_phase1_integration.ml -o ocaml/test_phase1_integration
	./ocaml/test_phase1_integration
	ocamlc -custom -I ocaml -I $(ZARITH) -I $(SHALIB) $(ZARITH)/zarith.cma $(SHALIB)/sha.cma -cclib -lsha_stubs -cclib -L$(SHALIB) ocaml/manifest_crypto_fixture.cmo ocaml/extracted_phase1_integration.cmo ocaml/phase1_bytes.cmo ocaml/test_byte_boundaries.ml -o ocaml/test_byte_boundaries
	./ocaml/test_byte_boundaries
	ocamlc -custom -I ocaml -I $(ZARITH) $(ZARITH)/zarith.cma ocaml/extracted_phase1_integration.cmo ocaml/extracted_stage2.cmo ocaml/extracted_transcript_digest.cmo ocaml/extracted_manifest_auth.cmo ocaml/test_integer_differential.ml -o ocaml/test_integer_differential
	./ocaml/test_integer_differential

byte-vectors: test
	python3 scripts/byte_vectors.py

integer-audit: test
	python3 scripts/integer_surface.py

differential: test
	python3 scripts/differential.py

check-kernel-trust: check-source-trust

check-source-trust:
	python3 scripts/audit.py tokens

gate-tests:
	python3 scripts/test_gates.py

release:
	python3 scripts/release.py

clean:
	find rocq -type f \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' -o -name '*.aux' \) -delete
	find ocaml -type f \( -name '*.cmi' -o -name '*.cmo' -o -name '*.cmx' -o -name '*.o' \) -delete
	rm -f ocaml/test_context_bundle ocaml/test_stage2 ocaml/test_stage1 ocaml/test_stage1_wrapper ocaml/test_context_resolution ocaml/test_manifest_matching ocaml/test_transcript_digest ocaml/test_manifest_authentication ocaml/test_fibre_witness_kernel_bigint ocaml/test_orchestration_bigint
	rm -f ocaml/extracted_stage2.ml ocaml/extracted_stage2.mli
	rm -f ocaml/extracted_transcript_digest.ml ocaml/extracted_transcript_digest.mli
	rm -f ocaml/extracted_manifest_auth.ml ocaml/extracted_manifest_auth.mli
	rm -f ocaml/extracted_orchestration.ml ocaml/extracted_orchestration.mli
	rm -f ocaml/extracted_fibre_witness_kernel.ml ocaml/extracted_fibre_witness_kernel.mli
	rm -f ocaml/extracted_phase1_integration.ml ocaml/extracted_phase1_integration.mli ocaml/test_phase1_integration ocaml/test_integer_differential ocaml/test_byte_boundaries
	rm -f .lia.cache
