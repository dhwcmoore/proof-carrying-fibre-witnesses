(* Bounded typed-component integration: empty campaign; real manifest auth,
   existing record checks, exact fuel, supplied events and abstract digest hook.
   No claim about model execution, capture, replay faithfulness or encoding. *)
module S = Extracted_phase1_integration
open S
open Manifest_crypto_fixture
let n x = if x < 0 then invalid_arg "negative nat" else Big_int_Z.big_int_of_int x
let big = Big_int_Z.big_int_of_string
let huge = big "100000000000000000000000000000000000000000000000000000000000000000000000000000001"
let negative = big "-40000000000000000000000000000000000000001"
let d64 c = String.make 64 c
let cd = { cd_model_artifact_digest=d64 'a'; cd_preprocessing_digest=d64 'b'; cd_inference_spec_digest=d64 'c' }
let mv = { cm_audit_instance_id="ai-0001"; cm_campaign_id="cmp-1"; cm_context_digests=cd; cm_policy_hash=d64 'd'; cm_submission_digests=[] }
let md = campaign_manifest_digest sha256_hex mv
let seed = unhex "9d61b19deffdefff1c95bf2be5aa39d8a0b52e5e6a1d81e7e60a5f4b0d0c8b3a1"
let pk = Ed25519.pubkey ~sk:seed
let wire = { cw_digest=md; cw_signer="release-fixture"; cw_signature=hex (Ed25519.sign ~sk:seed ~msg:md) }
let record budget =
  "{\"audit_instance_id\":\"ai-0001\",\"campaign_id\":\"cmp-1\",\"completeness\":\"unknown\",\"context_digests\":" ^ render_context_descriptor cd ^
  ",\"manifest_digest\":\"" ^ md ^ "\",\"policy_hash\":\"" ^ d64 'd' ^ "\",\"recorded_results\":[],\"resource_budget\":{\"max_candidates\":" ^ Big_int_Z.string_of_big_int budget ^ "}}"
let cfg = { max_candidates=huge; max_wire_bytes=huge; max_transcript_bytes=huge; max_fuel=huge; model_call_fuel=n 1; max_fuel_per_candidate=huge;
  schedule={ commitment_parse_fuel=huge; signature_verify_fuel=n 0; manifest_bind_fuel=n 0; record_bind_fuel=n 0; preflight_fuel=n 0; stage1_base_fuel=n 0; stage1_per_byte_fuel=n 0 };
  config_trust_anchor={ ta_authorised_signers=["release-fixture"]; ta_keys=["release-fixture",pk] } }
let ti = { ti_commitment_wire=wire; ti_manifest=render_manifest mv; ti_submissions=[]; ti_record=record huge; ti_completeness=CompletenessUnknown; ti_config=cfg; ti_policy_document="fixture"; ti_policy="fixture"; ti_policy_digest=d64 'd' }
let unused _ = failwith "reserved hook unexpectedly called"
let tr = [{ event_key={key_phase=Stage2Phase huge;key_role=XRole;key_repeat=huge}; event_input=[negative;huge]; event_outcome=ExecOk [negative] }]
let digest_calls = ref 0
let digest events = incr digest_calls; assert (events=tr); "numeric-fixture"
let base = { op_parse_commitment=unused;op_signer_authorised=(fun _ -> unused);op_signature_valid=(fun _ _ -> unused);op_manifest_policy_matches=(fun _ -> unused);op_manifest_audit_matches=(fun _ -> unused);op_manifest_context_matches=(fun _ -> unused);op_ledger_mismatch=(fun _ -> unused);op_record_identity_mismatch=(fun _ _ _ -> unused);op_completeness_wellformed=unused;op_stage1_check=(fun _ _ _ _ -> unused);op_preflight=unused;op_eval_o3=(fun _ _ -> unused);op_stage2_check=(fun _ _ _ -> unused);op_record_crosscheck=(fun _ _ _ -> unused);op_transcript_digest=digest }
let ops = pipeline_ops sha256_hex ed25519_verify ed25519_pubkey_valid String.equal (fun _ -> cd) (fun _ -> "ai-0001") base
let assess input = assess_validated ops input (validate_campaign ops input) (LiveTranscript(tr,CtxNotNeeded))
let () =
  (match validate_campaign ops ti with ValidCampaign(_,fl) -> assert (fl.fuel_consumed=huge) | _ -> assert false);
  (match parse_record_full_impl ti.ti_record with Some r -> assert (r.rf_budget.rb_max_candidates=Some huge) | None -> assert false);
  let out = assess ti in assert (verdict_of out=UNDERDETERMINED);
  assert (typed_digest_of (outcome_transcript_evidence out)=Some "numeric-fixture");
  (match out with Underdetermined r -> assert (List.for_all (fun f -> f.finding_outcome<>Fail) r.report_replay.replay_record_findings) | _ -> assert false);
  let calls = !digest_calls in
  let exhausted = {ti with ti_config={cfg with max_fuel=Big_int_Z.pred_big_int huge}} in
  assert (verdict_of (assess exhausted)=OBSTRUCTED); assert (!digest_calls=calls);
  let tampered={ti with ti_manifest=render_manifest {mv with cm_campaign_id="tampered"}} in
  (match validate_campaign ops tampered with InvalidCampaign(SignatureInvalid,_,_) -> () | _ -> assert false);
  assert (verdict_of (assess tampered)=OBSTRUCTED);
  let unknown={ti with ti_commitment_wire={wire with cw_signer="unknown"}} in
  (match validate_campaign ops unknown with InvalidCampaign(SignerNotAuthorised,_,_) -> () | _ -> assert false);
  let mismatch=assess {ti with ti_record=record (Big_int_Z.succ_big_int huge)} in
  assert (verdict_of mismatch=UNDERDETERMINED);
  (match mismatch with Underdetermined r -> assert (List.exists (fun f -> f.finding_outcome=Fail) r.report_replay.replay_record_findings) | _ -> assert false);
  print_endline "phase1 typed integration: PASS (empty campaign; abstract digest; reserved hooks unused)"

(* Byte adapter integration remains submission-free. Policy bytes are opaque:
   §2.3 semantic load validation and kernel-policy interpretation are residual. *)
let () =
  let module B=Phase1_bytes in
  let model="existing model byte snapshot" and pre="existing preprocessing snapshot" and inf="existing inference snapshot" in
  let d={cd_model_artifact_digest=B.hash sha256_hex "pcfw.model_artifact.v1" model;
         cd_preprocessing_digest=B.hash sha256_hex "pcfw.preprocessing_spec.v1" pre;
         cd_inference_spec_digest=B.hash sha256_hex "pcfw.inference_spec.v1" inf} in
  let descriptor_bytes=render_context_descriptor d in
  let policy_bytes="{\"audit_instance_id\":\"ai-0001\"}" in
  let policy_digest=B.hash sha256_hex "pcfw.policy_payload.v1" policy_bytes in
  let p=B.bind_policy_bytes sha256_hex ~committed_bytes:policy_bytes ~expected_digest:policy_digest policy_bytes in
  let m={mv with cm_context_digests=d;cm_policy_hash=policy_digest} in
  let manifest_bytes=render_manifest m in
  let parsed=B.manifest manifest_bytes in
  let md=campaign_manifest_digest sha256_hex parsed in
  let mc_bytes=B.render(B.Object["digest",B.Text md;"signer",B.Text "release-fixture";"signature",B.Text(hex(Ed25519.sign ~sk:seed ~msg:md))]) in
  let cw=B.commitment mc_bytes in
  let complete_bytes="{\"k\":\"complete\",\"v\":{\"body\":0,\"scheme\":\"registry-v0\"}}" in
  let rbytes="{\"audit_instance_id\":\"ai-0001\",\"campaign_id\":\"cmp-1\",\"completeness\":"^complete_bytes^",\"context_digests\":"^descriptor_bytes^
      ",\"manifest_digest\":\""^md^"\",\"policy_hash\":\""^policy_digest^"\",\"recorded_results\":[],\"resource_budget\":{\"max_candidates\":"^Big_int_Z.string_of_big_int huge^"}}" in
  let input=B.bind_record {ti with ti_commitment_wire=cw;ti_manifest=manifest_bytes;ti_policy_document=policy_bytes;ti_policy=p;ti_policy_digest=policy_digest} rbytes in
  assert(input.ti_completeness=CompletenessComplete{completeness_scheme="registry-v0";completeness_body="0"});
  let loaded=B.bind_context sha256_hex ~manifest_descriptor:parsed.cm_context_digests descriptor_bytes ~model ~preprocessing:pre ~inference:inf in
  assert(loaded.loaded_descriptor=descriptor_bytes);
  let raw=B.transcript_bytes tr in
  let wire=B.parse_transcript sha256_hex cfg ~n_pre:(n 2) ~n_obs:(n 1) raw in
  let digest=B.transcript_digest sha256_hex in
  let bops=pipeline_ops sha256_hex ed25519_verify ed25519_pubkey_valid String.equal
      (fun q->assert(q=p);d) (fun q->assert(q=p);"ai-0001") (set_transcript_digest base digest) in
  let vr=validate_campaign bops input in
  (match vr with ValidCampaign _->()|_->assert false);
  let output=assess_validated bops input vr (OfflineParse(wire,CtxNotNeeded)) in
  assert(verdict_of output=UNDERDETERMINED);
  (match outcome_transcript_evidence output with OfflineTranscript(td,wd)->assert(td=digest tr);assert(wd=B.hash sha256_hex "pcfw.exec_transcript_wire.v1" raw)|_->assert false);
  let malformed=B.parse_transcript sha256_hex cfg ~n_pre:(n 2) ~n_obs:(n 1) (" "^raw) in
  assert(verdict_of(assess_validated bops input vr (OfflineParse(malformed,CtxNotNeeded)))=OBSTRUCTED);
  (* A canonical identity mutation is detected by existing validation. *)
  let mutated=B.render(match B.decode rbytes with B.Object xs->B.Object(List.map(fun(k,v)->if k="context_digests" then k,B.decode(render_context_descriptor cd) else k,v)xs)|_->assert false) in
  (match validate_campaign bops {input with ti_record=mutated} with InvalidCampaign(RecordIdentityMismatch "context_digests",_,_)->()|_->assert false);
  print_endline "PASS: byte integration; canonical snapshots -> existing validation/auth/record -> offline parse/digest -> verdict; opaque policy, no model/capture"
