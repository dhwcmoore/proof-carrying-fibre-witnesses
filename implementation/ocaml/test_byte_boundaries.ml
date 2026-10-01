(* Adversarial byte/typed boundary tests. No model execution or faithfulness. *)
module B=Phase1_bytes
module S=Extracted_phase1_integration
open Manifest_crypto_fixture
let n=Big_int_Z.big_int_of_int
let big=Big_int_Z.big_int_of_string
let huge=big "100000000000000000000000000000000000000000000000000000000000000000000000000000001"
let count=ref 0
let check label test = incr count; if not(test()) then failwith label
let bad label f = check label (fun ()->try ignore(f());false with B.Reject _->true)
let parse_bad label bytes = bad label (fun ()->B.decode bytes)
let d64 c=String.make 64 c
let descriptor={S.cd_model_artifact_digest=d64 'a';S.cd_preprocessing_digest=d64 'b';S.cd_inference_spec_digest=d64 'c'}
let mv={S.cm_audit_instance_id="ai";S.cm_campaign_id="campaign";S.cm_context_digests=descriptor;S.cm_policy_hash=d64 'd';S.cm_submission_digests=[]}
let record completeness =
 "{\"audit_instance_id\":\"ai\",\"campaign_id\":\"campaign\",\"completeness\":"^completeness^",\"context_digests\":"^S.render_context_descriptor descriptor^",\"manifest_digest\":\""^d64 'e'^"\",\"policy_hash\":\""^d64 'd'^"\",\"recorded_results\":[],\"resource_budget\":{}}"
let cfg={S.max_candidates=huge;S.max_wire_bytes=huge;S.max_transcript_bytes=huge;S.max_fuel=huge;S.model_call_fuel=n 1;S.max_fuel_per_candidate=huge;
 S.schedule={S.commitment_parse_fuel=n 0;S.signature_verify_fuel=n 0;S.manifest_bind_fuel=n 0;S.record_bind_fuel=n 0;S.preflight_fuel=n 0;S.stage1_base_fuel=n 0;S.stage1_per_byte_fuel=n 0};S.config_trust_anchor={S.ta_authorised_signers=[];S.ta_keys=[]}}
let event phase role repeat outcome={S.event_key={S.key_phase=phase;S.key_role=role;S.key_repeat=repeat};S.event_input=[Big_int_Z.minus_big_int huge];S.event_outcome=outcome}
let vectors=[[];[event S.ContextProbe S.Probe (n 0) (S.ExecOk [huge])];[event (S.Stage2Phase huge) S.XRole huge (S.ExecFailed "bad\n\000\011\"\\");event (S.Stage2Phase huge) S.YRole (n 1) S.ExecExhausted]]
let replace old fresh s =
 let rec find i=if i+String.length old>String.length s then failwith("missing fixture "^old) else if String.sub s i (String.length old)=old then i else find(i+1) in
 let i=find 0 in String.sub s 0 i ^ fresh ^ String.sub s (i+String.length old)(String.length s-i-String.length old)
let malformed bytes cfg = match B.parse_transcript sha256_hex cfg ~n_pre:(n 1) ~n_obs:(n 1) bytes with
 | S.MalformedParse(_,d)->d=B.hash sha256_hex "pcfw.exec_transcript_wire.v1" bytes | _->false
let () =
 if Array.length Sys.argv=2 && Sys.argv.(1)="--transcript-vectors" then
  List.iter(fun tr->Printf.printf "%s\t%s\t%s\n" (B.transcript_bytes tr) (hex(B.transcript_digest_input tr)) (B.transcript_digest sha256_hex tr)) vectors
 else if Array.length Sys.argv=1 then (
 List.iter(fun (label,s)->parse_bad label s)
 ["duplicate","{\"a\":0,\"a\":1}";"reordered","{\"b\":0,\"a\":1}";"whitespace","[ 0]";"leading zero","01";"negative zero","-0";"plus","+1";"float","1.0";"truncated","{\"a\":";"trailing","[]\n";"malformed UTF8","\"\xff\"";"UTF8 outside scope","\"\xc3\xa9\"";"alternate string escape","\"\\u0061\"";"alternate control escape","\"\\u000a\"";"uppercase escape","\"\\u000B\"";"raw control","\"\n\"";"escaped slash","\"\\/\"";"trailing comma","[1,]"];
 check "huge exact roundtrip" (fun()->let s=Big_int_Z.string_of_big_int huge in B.render(B.decode s)=s);
 check "large negative" (fun()->let s="-"^Big_int_Z.string_of_big_int huge in B.render(B.decode s)=s);
 bad "depth limit" (fun()->B.decode ~max_depth:1 "[[[0]]]");
 check "manifest decoder" (fun()->B.manifest(S.render_manifest mv)=mv);
 bad "missing manifest field" (fun()->B.manifest "{}");
 bad "unknown manifest field" (fun()->B.manifest(replace "\"campaign_id\":" "\"bogus\":0,\"campaign_id\":" (S.render_manifest mv)));
 bad "descriptor missing" (fun()->B.descriptor "{}");
 bad "descriptor unknown" (fun()->B.descriptor(replace "\"inference_spec_digest\":" "\"extra\":0,\"inference_spec_digest\":" (S.render_context_descriptor descriptor)));
 check "unknown completeness derived" (fun()->snd(B.record(record "\"unknown\""))=S.CompletenessUnknown);
 let incomplete="{\"k\":\"incomplete\",\"v\":[{\"detail\":\"d\",\"kind\":\"k\"}]}" in
 check "incomplete decoded" (fun()->snd(B.record(record incomplete))=S.CompletenessIncomplete);
 let complete="{\"k\":\"complete\",\"v\":{\"body\":{\"n\":0},\"scheme\":\"registry-v0\"}}" in
 check "complete decoded" (fun()->snd(B.record(record complete))=S.CompletenessComplete {S.completeness_scheme="registry-v0";S.completeness_body="{\"n\":0}"});
 bad "old unbound 42 rejected" (fun()->B.record(record "42"));
 bad "empty scheme" (fun()->B.record(record(replace "registry-v0" "" complete)));
 bad "completeness unknown tag" (fun()->B.record(record "{\"k\":\"bogus\",\"v\":0}"));
 bad "incomplete wrong payload" (fun()->B.record(record "{\"k\":\"incomplete\",\"v\":0}"));
 bad "completeness mismatch" (fun()->B.check_completeness S.CompletenessUnknown (snd(B.record(record complete))));
 bad "negative budget" (fun()->B.record(replace "\"resource_budget\":{}" "\"resource_budget\":{\"max_candidates\":-1}" (record "\"unknown\"")));
 let policy="{\"audit_instance_id\":\"ai\"}" in let pd=B.hash sha256_hex "pcfw.policy_payload.v1" policy in
 check "opaque policy bytes bound" (fun()->B.bind_policy_bytes sha256_hex ~committed_bytes:policy ~expected_digest:pd policy=policy);
 bad "policy digest mismatch" (fun()->B.bind_policy_bytes sha256_hex ~committed_bytes:policy ~expected_digest:(d64 '0') policy);
 bad "policy bytes mismatch" (fun()->B.bind_policy_bytes sha256_hex ~committed_bytes:policy ~expected_digest:pd "{}");
 bad "apparent same value mutation" (fun()->B.bind_policy_bytes sha256_hex ~committed_bytes:policy ~expected_digest:pd (" "^policy));
 let model="weights" and pre="pre" and inf="spec" in
 let d={S.cd_model_artifact_digest=B.hash sha256_hex "pcfw.model_artifact.v1" model;S.cd_preprocessing_digest=B.hash sha256_hex "pcfw.preprocessing_spec.v1" pre;S.cd_inference_spec_digest=B.hash sha256_hex "pcfw.inference_spec.v1" inf} in
 let load ~manifest_descriptor ~model =B.bind_context sha256_hex ~manifest_descriptor (S.render_context_descriptor d) ~model ~preprocessing:pre ~inference:inf in
 check "context snapshots bound" (fun()->(load ~manifest_descriptor:d ~model).S.loaded_model_bytes=model);
 bad "descriptor/manifest mismatch" (fun()->load ~manifest_descriptor:descriptor ~model);
 bad "model snapshot mutation" (fun()->load ~manifest_descriptor:d ~model:(model^"x"));
 bad "inference snapshot mutation" (fun()->B.bind_context sha256_hex ~manifest_descriptor:d (S.render_context_descriptor d) ~model ~preprocessing:pre ~inference:(inf^"x"));
 bad "preprocessing snapshot mutation" (fun()->B.bind_context sha256_hex ~manifest_descriptor:d (S.render_context_descriptor d) ~model ~preprocessing:(pre^"x") ~inference:inf);
 let raw="candidate bytes" in let sd=B.hash sha256_hex "pcfw.candidate_submission.v1" raw in
 check "submission snapshot" (fun()->(B.bind_submission sha256_hex sd raw).S.submission_wire=raw);
 bad "stale manifest entry" (fun()->B.bind_submission sha256_hex sd (raw^"x"));
 List.iter (fun tr->check "transcript roundtrip" (fun()->match B.parse_transcript sha256_hex cfg ~n_pre:(n 1) ~n_obs:(n 1) (B.transcript_bytes tr) with S.WellformedParse(t,_)->t=tr | _->false)) vectors;
 let bytes=B.transcript_bytes(List.nth vectors 1) in
 List.iter(fun (label,bytes)->check label (fun()->malformed bytes cfg))
 ["transcript negative repeat",replace "\"repeat\":0" "\"repeat\":-1" bytes;
  "transcript unknown tag",replace "\"ok\"" "\"bogus\"" bytes;
  "transcript unknown field",replace "\"input\":" "\"context_id\":\"foreign\",\"input\":" bytes;
  "transcript missing field",replace "\"repeat\":0," "" bytes;
  "transcript duplicate",replace "\"repeat\":0" "\"repeat\":0,\"repeat\":0" bytes;
  "transcript unknown role",replace "\"probe\"" "\"alien\"" bytes;
  "transcript truncated",String.sub bytes 0 (String.length bytes-1);
  "transcript leading zero",replace "\"repeat\":0" "\"repeat\":00" bytes];
 check "transcript byte limit" (fun()->malformed bytes {cfg with S.max_transcript_bytes=n 1});
 check "dimensions conditional on context" (fun()->match B.parse_transcript sha256_hex cfg ~n_pre:(n 2) ~n_obs:(n 1) bytes with S.MalformedParse _->true | _->false);
 check "event order digest input" (fun()->let tr=List.nth vectors 2 in B.transcript_digest_input tr<>B.transcript_digest_input(List.rev tr));
 check "digest domain separation" (fun()->B.transcript_digest_input []="pcfw.exec_transcript.v1\031[]");
 check "digest mutation observable" (fun()->B.transcript_digest sha256_hex []<>B.transcript_digest sha256_hex(List.nth vectors 1));
 Printf.printf "PASS: byte boundary battery; %d cases; bounded ASCII adapter\n" !count
 ) else failwith "unknown harness mode"
