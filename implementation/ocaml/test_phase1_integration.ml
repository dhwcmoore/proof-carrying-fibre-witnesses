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
