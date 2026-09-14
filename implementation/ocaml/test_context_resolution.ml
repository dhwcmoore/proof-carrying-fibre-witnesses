(* Exercises the extracted O1/O2/O3 checks (ContextResolution):
   descriptor unparseable / O1 mismatch / O2 mismatch / both pass;
   probe-spec unavailable / O3 mismatch / O3 pass; resolve None/Some.
   O1/O2 now compare against the *parsed descriptor* of `loaded_descriptor lc`;
   the O3 probe is *derived from* `loaded_inference_bytes lc` -- plus
   (closure-report obligation 3) the O3 probe-input/observation equality
   check at magnitudes beyond a native 63-bit OCaml int, including a
   one-past-boundary mismatch.

   Z / nat now extract to Big_int_Z.big_int (see ExtractStage2.v): true
   arbitrary precision, not merely a wider fixed-width int. *)

module S = Extracted_stage2

let bi = Big_int_Z.big_int_of_int
let big = Big_int_Z.big_int_of_string

(* well beyond max_int (2^62 - 1 on a 64-bit system) *)
let huge_in = big "40000000000000000000000000000000000000000" (* 4*10^40 *)
let huge_obs = big "-70000000000000000000000000000000000000003"
let huge_obs_plus1 = Big_int_Z.succ_big_int huge_obs

let id_v (x : Big_int_Z.big_int S.vec) : Big_int_Z.big_int S.vec = x
let ctx : S.auditContext =
  { S.context_policy = { S.domainb = (fun _ -> true); S.quantise = id_v;
                         S.target = (fun _ -> false) };
    S.preproc = id_v; S.model = id_v }

let deqb (a : string) (b : string) : bool = a = b
let dg (b : string) : string = b   (* component digest = the byte string *)

let committed : S.context_descriptor =
  { S.cd_model_artifact_digest = "M"; S.cd_preprocessing_digest = "PP"; S.cd_inference_spec_digest = "INF" }
let parse_descriptor (s : string) : S.context_descriptor option =
  if s = "desc" then Some committed else None

let probe_in : Big_int_Z.big_int S.vec = S.of_list [bi 1; bi 2]
let probe_obs : Big_int_Z.big_int S.vec = S.of_list [bi 9]
let probe_of_spec (b : string) : (Big_int_Z.big_int S.vec * Big_int_Z.big_int S.vec) option =
  if b = "INF" then Some (probe_in, probe_obs) else None

(* a second, huge-magnitude probe spec, wired to a different inference-bytes
   token so it never interferes with the small-value probe above *)
let probe_in_huge : Big_int_Z.big_int S.vec = S.of_list [huge_in]
let probe_obs_huge : Big_int_Z.big_int S.vec = S.of_list [huge_obs]
let probe_of_spec_huge (b : string) : (Big_int_Z.big_int S.vec * Big_int_Z.big_int S.vec) option =
  if b = "INF-HUGE" then Some (probe_in_huge, probe_obs_huge) else None

let lc ~desc ~m ~pp ~inf : S.loaded_context =
  { S.loaded_descriptor = desc; S.loaded_model_bytes = m;
    S.loaded_preproc_bytes = pp; S.loaded_inference_bytes = inf;
    S.loaded_context_token = "tok" }

let preflight l = S.preflight_check deqb dg dg dg parse_descriptor l
let o3 l e = S.eval_o3_check (bi 2) (bi 1) probe_of_spec l e "p-committed"
let o3_huge l e = S.eval_o3_check (bi 1) (bi 1) probe_of_spec_huge l e "p-committed"
let resolve l e =
  S.resolve (bi 2) (bi 2) (bi 1) ctx "p-committed" deqb dg dg dg parse_descriptor probe_of_spec l e

let ev ~inp ~out : S.exec_event =
  { S.event_key = { S.key_phase = S.ContextProbe; S.key_role = S.Probe; S.key_repeat = bi 0 };
    S.event_input = inp; S.event_outcome = out }

let good_lc = lc ~desc:"desc" ~m:"M" ~pp:"PP" ~inf:"INF"
let good_ev = ev ~inp:[bi 1; bi 2] ~out:(S.ExecOk [bi 9])
let fail msg = Printf.printf "FAIL: %s\n" msg; exit 1

let () =
  (match preflight (lc ~desc:"bad" ~m:"M" ~pp:"PP" ~inf:"INF") with
   | S.PreflightFail (S.ArtifactMismatch, _) -> ()
   | _ -> fail "expected PreflightFail ArtifactMismatch (descriptor unparseable)");

  (match preflight (lc ~desc:"desc" ~m:"WRONG" ~pp:"PP" ~inf:"INF") with
   | S.PreflightFail (S.ArtifactMismatch, _) -> ()
   | _ -> fail "expected PreflightFail ArtifactMismatch (O1)");

  (match preflight (lc ~desc:"desc" ~m:"M" ~pp:"WRONG" ~inf:"INF") with
   | S.PreflightFail (S.SpecMismatch, _) -> ()
   | _ -> fail "expected PreflightFail SpecMismatch (O2)");

  (match preflight good_lc with
   | S.PreflightOk _ -> () | _ -> fail "expected PreflightOk");

  (* changing only the descriptor now changes acceptance *)
  (match preflight (lc ~desc:"bad" ~m:"M" ~pp:"PP" ~inf:"INF") with
   | S.PreflightOk _ -> fail "descriptor no longer affects acceptance"
   | _ -> ());

  (match o3 (lc ~desc:"desc" ~m:"M" ~pp:"PP" ~inf:"NOPROBE") good_ev with
   | S.O3Fail _ -> () | _ -> fail "expected O3Fail (probe unavailable)");

  (match o3 good_lc (ev ~inp:[bi 0; bi 0] ~out:(S.ExecOk [bi 9])) with
   | S.O3Fail _ -> () | _ -> fail "expected O3Fail (input mismatch)");

  (match o3 good_lc (ev ~inp:[bi 1; bi 2] ~out:(S.ExecOk [bi 0])) with
   | S.O3Fail _ -> () | _ -> fail "expected O3Fail (observation mismatch)");

  (match o3 good_lc good_ev with
   | S.O3Ok (rc, _) when rc.S.resolved_policy = "p-committed"
       && rc.S.resolved_descriptor = "desc" -> ()
   | _ -> fail "expected O3Ok");

  (match resolve (lc ~desc:"bad" ~m:"M" ~pp:"PP" ~inf:"INF") good_ev with
   | None -> () | _ -> fail "resolve None on preflight failure");

  (match resolve good_lc (ev ~inp:[bi 0; bi 0] ~out:(S.ExecOk [bi 9])) with
   | None -> () | _ -> fail "resolve None on O3 failure");

  (match resolve good_lc good_ev with
   | Some (_c, rc) when rc.S.resolved_policy = "p-committed"
       && rc.S.resolved_descriptor = "desc" -> ()
   | _ -> fail "resolve Some on full success");

  (* ---- beyond-63-bit: O3's probe-input/observation equality (list_zeqb)
     at ~4*10^40 / ~-7*10^40 magnitude -- exact match accepts *)
  let huge_lc = lc ~desc:"desc" ~m:"M" ~pp:"PP" ~inf:"INF-HUGE" in
  (match o3_huge huge_lc (ev ~inp:[huge_in] ~out:(S.ExecOk [huge_obs])) with
   | S.O3Ok (rc, _) when rc.S.resolved_policy = "p-committed" -> ()
   | _ -> fail "expected O3Ok at huge probe-input/observation magnitude");

  (* one unit off the observation -> O3Fail (no false accept from precision
     loss at this magnitude) *)
  (match o3_huge huge_lc (ev ~inp:[huge_in] ~out:(S.ExecOk [huge_obs_plus1])) with
   | S.O3Fail _ -> ()
   | _ -> fail "expected O3Fail one unit past the huge observation match");

  (* the input side has the same one-past-boundary property *)
  (match o3_huge huge_lc
           (ev ~inp:[Big_int_Z.succ_big_int huge_in] ~out:(S.ExecOk [huge_obs])) with
   | S.O3Fail _ -> ()
   | _ -> fail "expected O3Fail one unit past the huge input match");

  print_string "PASS: context resolution -- descriptor-bound O1/O2, spec-derived \
                O3 probe, resolve None/Some; plus O3's probe-input/observation \
                equality/one-past-boundary at ~4*10^40 magnitude\n"
