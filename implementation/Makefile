.PHONY: check rocq ocaml check-kernel-trust assumptions test clean

# F.3 named-component libraries for the authentication harness (SHA-256, bignum).
# F.3 crypto-library locations. Override on the command line if needed, e.g.
#   make check OCAML_LIB=$(ocamlfind printconf destdir)
OCAML_LIB ?= $(shell opam var lib 2>/dev/null || echo $(HOME)/.opam/default/lib)
ZARITH ?= $(OCAML_LIB)/zarith
SHALIB ?= $(OCAML_LIB)/sha

check: rocq ocaml check-kernel-trust assumptions test

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
	coqc -Q rocq PCFW rocq/ManifestPipeline.v
	coqc -Q rocq PCFW rocq/ExtractStage2.v
	coqc -Q rocq PCFW rocq/ExtractManifestAuthentication.v
	coqchk -Q rocq PCFW PCFW.FibreWitnessKernel PCFW.Orchestration \
	  PCFW.Stage2 PCFW.Stage2Adapter PCFW.Stage1 PCFW.Stage1Invariant PCFW.Stage1Wrapper PCFW.ContextResolution PCFW.PipelineWiring PCFW.ValidationBinding PCFW.CanonicalV1 PCFW.ManifestMatching PCFW.ManifestAuthentication PCFW.ManifestLedger PCFW.ManifestAudit PCFW.CampaignRecord PCFW.RecordCrosscheck PCFW.ManifestPipeline
	coqtop -quiet -Q rocq PCFW < rocq/PrintKernelAssumptions.v

assumptions:
	coqtop -quiet -Q rocq PCFW < rocq/PrintOrchestrationAssumptions.v
	coqtop -quiet -Q rocq PCFW < rocq/PrintStage2Assumptions.v

ocaml:
	ocamlc -I ocaml -c ocaml/orchestration.mli
	ocamlc -I ocaml -c ocaml/orchestration.ml

test: ocaml rocq
	ocamlc -I ocaml ocaml/orchestration.cmo ocaml/test_context_bundle.ml -o ocaml/test_context_bundle
	./ocaml/test_context_bundle
	ocamlc -I ocaml -c ocaml/extracted_stage2.mli
	ocamlc -I ocaml -c ocaml/extracted_stage2.ml
	ocamlc -I ocaml ocaml/extracted_stage2.cmo ocaml/test_stage2.ml -o ocaml/test_stage2
	./ocaml/test_stage2
	ocamlc -I ocaml ocaml/extracted_stage2.cmo ocaml/test_stage1.ml -o ocaml/test_stage1
	./ocaml/test_stage1
	ocamlc -I ocaml ocaml/extracted_stage2.cmo ocaml/test_stage1_wrapper.ml -o ocaml/test_stage1_wrapper
	./ocaml/test_stage1_wrapper
	ocamlc -I ocaml ocaml/extracted_stage2.cmo ocaml/test_context_resolution.ml -o ocaml/test_context_resolution
	./ocaml/test_context_resolution
	ocamlc -I ocaml ocaml/extracted_stage2.cmo ocaml/test_manifest_matching.ml -o ocaml/test_manifest_matching
	./ocaml/test_manifest_matching
	ocamlc -I ocaml -c ocaml/extracted_manifest_auth.mli
	ocamlc -I ocaml -c ocaml/extracted_manifest_auth.ml
	ocamlc -custom -I ocaml -I $(ZARITH) -I $(SHALIB) $(ZARITH)/zarith.cma $(SHALIB)/sha.cma -cclib -lsha_stubs -cclib -L$(SHALIB) ocaml/extracted_manifest_auth.cmo ocaml/test_manifest_authentication.ml -o ocaml/test_manifest_authentication
	./ocaml/test_manifest_authentication

check-kernel-trust:
	! grep -En '\b(Admitted|admit|Axiom|Parameter|Hypothesis)\b' rocq/FibreWitnessKernel.v

clean:
	find rocq -type f \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' -o -name '*.aux' \) -delete
	find ocaml -type f \( -name '*.cmi' -o -name '*.cmo' -o -name '*.cmx' -o -name '*.o' \) -delete
	rm -f ocaml/test_context_bundle ocaml/test_stage2 ocaml/test_stage1 ocaml/test_stage1_wrapper ocaml/test_context_resolution ocaml/test_manifest_matching ocaml/test_manifest_authentication
	rm -f ocaml/extracted_stage2.ml ocaml/extracted_stage2.mli
	rm -f ocaml/extracted_manifest_auth.ml ocaml/extracted_manifest_auth.mli
	rm -f ocaml/extracted_orchestration.ml ocaml/extracted_orchestration.mli
	rm -f ocaml/extracted_fibre_witness_kernel.ml ocaml/extracted_fibre_witness_kernel.mli
	rm -f .lia.cache
