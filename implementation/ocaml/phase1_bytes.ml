(* Bounded, hand-written ASCII-wire adapter around existing extraction.
   Trusted wrapper: tests are not a Gallina parser-correctness theorem.
   No policy semantic loader, model realisation, capture or faithfulness. *)
module S = Extracted_phase1_integration
exception Reject of string
let reject s = raise (Reject s)
let big = Big_int_Z.big_int_of_string
let host_nat n = Big_int_Z.big_int_of_int n
let nonnegative n = if Big_int_Z.sign_big_int n < 0 then reject "negative natural" else n
let byte_length s = host_nat (String.length s)
let digest_input tag bytes = tag ^ "\031" ^ bytes
let hash sha tag bytes = sha (digest_input tag bytes)

type value = Object of (string * value) list | Array of value list
           | Text of string | Integer of Big_int_Z.big_int | Boolean of bool | Null
let rec render = function
 | Text s -> if String.exists (fun c -> Char.code c > 127) s then reject "ASCII-wire scope"; S.json_string s
 | Integer n -> Big_int_Z.string_of_big_int n
 | Boolean true -> "true" | Boolean false -> "false" | Null -> "null"
 | Array xs -> "[" ^ String.concat "," (List.map render xs) ^ "]"
 | Object xs ->
   let sorted=List.sort (fun (a,_) (b,_) -> String.compare a b) xs in
   let rec unique = function (a,_)::((b,_)::_ as rest) -> if a=b then reject "duplicate key"; unique rest | _->() in
   unique sorted;
   "{" ^ String.concat "," (List.map (fun (k,v)->render(Text k)^":"^render v) sorted) ^ "}"

let decode ?(max_depth=128) bytes =
 if max_depth < 0 then reject "negative depth limit";
 if String.exists (fun c -> Char.code c > 127) bytes then reject "ASCII-wire scope";
 let size=String.length bytes in
 let char i = if i>=size then reject "truncated input" else bytes.[i] in
 let text i =
   let suffix=String.sub bytes i (size-i) in
   match S.parse_json_string suffix with
   | Some(s,rest)->s,size-String.length rest
   | None->reject "string grammar" in
 let rec value depth i =
   if depth>max_depth then reject "parser depth limit";
   match char i with
   | '"' -> let s,j=text i in Text s,j
   | '[' -> if char(i+1)=']' then Array [],i+2 else
      let rec items j acc = let v,k=value(depth+1) j in match char k with
       | ']'->Array(List.rev(v::acc)),k+1 | ','->items(k+1)(v::acc) | _->reject "array grammar" in items(i+1) []
   | '{' -> if char(i+1)='}' then Object [],i+2 else
      let rec members j previous acc =
       let k,p=text j in
       (match previous with Some old when String.compare old k>=0 -> reject "key order/duplicate" | _->());
       if char p<>':' then reject "object grammar";
       let v,q=value(depth+1)(p+1) in match char q with
       | '}'->Object(List.rev((k,v)::acc)),q+1 | ','->members(q+1)(Some k)((k,v)::acc) | _->reject "object grammar" in members(i+1) None []
   | 't' -> literal "true" (Boolean true) i
   | 'f' -> literal "false" (Boolean false) i
   | 'n' -> literal "null" Null i
   | '-' | '0'..'9' ->
      let j=ref (if char i='-' then i+1 else i) in
      let start = !j in
      while !j<size && bytes.[!j]>='0' && bytes.[!j]<='9' do incr j done;
      if !j=start then reject "integer grammar";
      let token=String.sub bytes i (!j-i) in
      let n=try big token with Failure _->reject "integer grammar" in
      if Big_int_Z.string_of_big_int n<>token then reject "noncanonical integer";
      Integer n,!j
   | _ -> reject "value grammar"
 and literal token v i =
   let length=String.length token in
   if i+length>size || String.sub bytes i length<>token then reject "literal grammar";
   v,i+length in
 let v,finish=value 0 0 in
 if finish<>size || render v<>bytes then reject "noncanonical bytes";
 v

let fields = function Object xs->xs | _->reject "expected object"
let exact keys value =
 let xs=fields value in
 if List.map fst xs<>List.sort String.compare keys then reject "missing/unknown fields";xs
let get key xs = match List.assoc_opt key xs with Some v->v | None->reject ("missing "^key)
let string = function Text s->s | _->reject "expected string"
let integer = function Integer n->n | _->reject "expected integer"
let array = function Array xs->xs | _->reject "expected array"
let nat v = nonnegative(integer v)
let hex64 s = if String.length s<>64 || not(S.all_lower_hex s) then reject "digest grammar";s
let descriptor_value value =
 let xs=exact ["inference_spec_digest";"model_artifact_digest";"preprocessing_digest"] value in
 {S.cd_model_artifact_digest=hex64(string(get "model_artifact_digest" xs));
  S.cd_preprocessing_digest=hex64(string(get "preprocessing_digest" xs));
  S.cd_inference_spec_digest=hex64(string(get "inference_spec_digest" xs))}
let descriptor bytes = descriptor_value(decode bytes)
let manifest bytes =
 ignore(decode bytes);
 match S.parse_manifest_impl bytes with Some m when S.render_manifest m=bytes->m | _->reject "manifest decode"
let commitment bytes =
 let xs=exact ["digest";"signature";"signer"] (decode bytes) in
 let wire={S.cw_digest=string(get "digest" xs);S.cw_signature=string(get "signature" xs);S.cw_signer=string(get "signer" xs)} in
 match S.parse_commitment_impl wire with S.CommitmentParsed _->wire | _->reject "commitment encoding"

let completeness value =
 let result=match value with
 | Text "unknown"->S.CompletenessUnknown
 | Object _ -> let xs=exact ["k";"v"] value in
   (match string(get "k" xs) with
    | "incomplete"->
      List.iter (fun x->let f=exact ["kind";"detail"] x in ignore(string(get "kind" f));ignore(string(get "detail" f))) (array(get "v" xs));
      S.CompletenessIncomplete
    | "complete"->let cert=exact ["body";"scheme"] (get "v" xs) in
      S.CompletenessComplete {S.completeness_scheme=string(get "scheme" cert);S.completeness_body=render(get "body" cert)}
    | _->reject "completeness tag")
 | _->reject "completeness structure" in
 if not(S.op_completeness_wellformed_impl result) then reject "completeness wellformedness";
 result
let record bytes =
 let value=decode bytes in
 let xs=exact ["audit_instance_id";"campaign_id";"completeness";"context_digests";"manifest_digest";"policy_hash";"recorded_results";"resource_budget"] value in
 let cs=completeness(get "completeness" xs) in
 match S.parse_record_full_impl bytes with Some r->r,cs | None->reject "typed record decode"
let bind_record ti bytes =
 let _,cs=record bytes in {ti with S.ti_record=bytes;S.ti_completeness=cs}
let check_completeness supplied derived = if supplied<>derived then reject "completeness mismatch"

(* Policy bytes are bound as an OPAQUE canonical value. This is not the §2.3
   semantic policy loader and does not instantiate policy digest injectivity. *)
let bind_policy_bytes sha ~committed_bytes ~expected_digest bytes =
 ignore(decode committed_bytes);ignore(decode bytes);
 if bytes<>committed_bytes then reject "committed policy bytes differ";
 if hash sha "pcfw.policy_payload.v1" bytes<>expected_digest then reject "policy digest mismatch";
 bytes
let bind_context sha ~manifest_descriptor descriptor_bytes ~model ~preprocessing ~inference =
 let d=descriptor descriptor_bytes in
 if d<>manifest_descriptor then reject "descriptor/manifest mismatch";
 if hash sha "pcfw.model_artifact.v1" model<>d.S.cd_model_artifact_digest then reject "model bytes mismatch";
 if hash sha "pcfw.preprocessing_spec.v1" preprocessing<>d.S.cd_preprocessing_digest then reject "preprocessing bytes mismatch";
 if hash sha "pcfw.inference_spec.v1" inference<>d.S.cd_inference_spec_digest then reject "inference bytes mismatch";
 {S.loaded_descriptor=descriptor_bytes;S.loaded_model_bytes=model;S.loaded_preproc_bytes=preprocessing;S.loaded_inference_bytes=inference;S.loaded_context_token=descriptor_bytes}
let bind_submission sha expected bytes =
 let actual=hash sha "pcfw.candidate_submission.v1" bytes in
 if actual<>expected then reject "stale submission entry";
 {S.submission_wire=bytes;S.submission_wire_length=byte_length bytes;S.submission_digest=actual}

let phase_value = function S.ContextProbe->Text "context_probe" | S.Stage2Phase n->Object["k",Text "stage2";"v",Integer(nonnegative n)]
let role_value = function S.Probe->Text "probe" | S.XRole->Text "x" | S.YRole->Text "y"
let zs xs = Array(List.map (fun n->Integer n) xs)
let event_value e =
 let k=e.S.event_key in
 let outcome=match e.S.event_outcome with
 | S.ExecExhausted->Text "exhausted"
 | S.ExecFailed s->Object["k",Text "failed";"v",Text s]
 | S.ExecOk xs->Object["k",Text "ok";"v",zs xs] in
 Object["input",zs e.S.event_input;"key",Object["phase",phase_value k.S.key_phase;"repeat",Integer(nonnegative k.S.key_repeat);"role",role_value k.S.key_role];"outcome",outcome]
let transcript_bytes tr = render(Array(List.map event_value tr))
let transcript_digest_input tr = digest_input "pcfw.exec_transcript.v1" (transcript_bytes tr)
let transcript_digest sha tr = sha(transcript_digest_input tr)
let event ~n_pre ~n_obs value =
 let xs=exact ["input";"key";"outcome"] value in
 let key=exact ["phase";"repeat";"role"] (get "key" xs) in
 let phase=match get "phase" key with
 | Text "context_probe"->S.ContextProbe
 | Object _ as p->let f=exact ["k";"v"] p in if string(get "k" f)<>"stage2" then reject "phase tag"; S.Stage2Phase(nat(get "v" f))
 | _->reject "phase structure" in
 let role=match string(get "role" key) with "probe"->S.Probe|"x"->S.XRole|"y"->S.YRole|_->reject "role tag" in

 let vector expected v = let ns=List.map integer (array v) in
  if not(Big_int_Z.eq_big_int (host_nat(List.length ns)) expected) then reject "vector dimension";ns in
 let input=vector n_pre (get "input" xs) in
 let outcome=match get "outcome" xs with
 | Text "exhausted"->S.ExecExhausted
 | Object _ as o->let f=exact ["k";"v"] o in (match string(get "k" f) with
   | "ok"->S.ExecOk(vector n_obs(get "v" f)) | "failed"->S.ExecFailed(string(get "v" f)) | _->reject "outcome tag")
 | _->reject "outcome structure" in
 {S.event_key={S.key_phase=phase;S.key_role=role;S.key_repeat=nat(get "repeat" key)};S.event_input=input;S.event_outcome=outcome}
let parse_transcript sha cfg ~n_pre ~n_obs bytes =
 let wire_digest=hash sha "pcfw.exec_transcript_wire.v1" bytes in
 try
  ignore(nonnegative cfg.S.max_transcript_bytes);ignore(nonnegative n_pre);ignore(nonnegative n_obs);
  if Big_int_Z.gt_big_int (byte_length bytes) cfg.S.max_transcript_bytes then reject "transcript byte limit";
  let tr=List.map (event ~n_pre ~n_obs) (array(decode bytes)) in
  if transcript_bytes tr<>bytes then reject "transcript reencoding";
  S.WellformedParse(tr,wire_digest)
 with Reject reason->S.MalformedParse(reason,wire_digest)
