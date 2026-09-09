(** O1 / O2 (preflight) and O3 (probe re-execution): the checks now *consume*
    [loaded_descriptor lc] and [loaded_inference_bytes lc], rather than comparing
    against free parameters.  Precise limits below.

    - [preflight_check] runs [parse_descriptor (loaded_descriptor lc)] and
      compares the loaded byte-digests against the resulting record's fields.
      This is sensitivity to the *decoded* descriptor: [parse_descriptor] may map
      distinct encodings to the same [descriptor], so not every byte change to
      [loaded_descriptor lc] alters acceptance.
    - [eval_o3_check] runs [probe_of_spec (loaded_inference_bytes lc)].  Feeding
      those (O2-digest-checked) bytes to the decoder establishes the *provenance*
      of the decoder's input.  It does NOT establish the decoder's correctness:
      the probe equals the inference spec's checkpoint probe only under
      [probe_of_spec] conformance (F.3).  Vector types give dimensions relative
      to [n_pre] / [n_obs].
    - [preflight_ok_artifact_bound] links a [PreflightOk] to the authenticated
      commitment via the explicit relation [commits] and to [C] via
      [committed_bytes_realise] -- BUT only under the hypothesis
      [parse_descriptor (loaded_descriptor lc) = Some committed_descriptor].
      That the *accepted* execution uses the authenticated descriptor is not
      established here (see "Next" in PHASE_1_STATUS.md).
    - [realises_C : loaded_context -> Prop] remains an uninterpreted predicate;
      its entire meaning is supplied by the [committed_bytes_realise] hypothesis.
      The only change from the previous revision is the *shape* of that
      hypothesis -- it is now conditioned on
      [byte_digest_consistent lc committed_descriptor] instead of being
      unconditional.

    Still F.3-external:
    - [parse_descriptor] / [probe_of_spec] correctness (wire decoding of the
      descriptor and the inference-spec probe);
    - [digest_eqb] / [model_digest_of] / ... truthfulness;
    - [commits committed_authcommitment committed_descriptor] (the manifest
      authentication chain);
    - that the loaded descriptor IS the committed one
      ([parse_descriptor (loaded_descriptor lc) = Some committed_descriptor]);
    - the kernel-[Policy] <-> policy-string correspondence;
    - [transcript_stage2_wf]; the [replay] path supplying [p_committed]. *)

From Coq Require Import Bool List ZArith String.
From Coq Require Vector.
From PCFW Require Import FibreWitnessKernel Orchestration Stage2 Stage2Adapter Stage1 CanonicalV1.
Import ListNotations.

Set Implicit Arguments.

(* THE shared context-descriptor type -- also used by ManifestMatching /
   ManifestAuthentication / ManifestPipeline. *)
Notation descriptor := CanonicalV1.context_descriptor.
Notation mkDescriptor := CanonicalV1.mkContextDescriptor.
Notation d_model_digest := CanonicalV1.cd_model_artifact_digest.
Notation d_preproc_digest := CanonicalV1.cd_preprocessing_digest.
Notation d_inference_digest := CanonicalV1.cd_inference_spec_digest.

Section CtxRes.
Context {n_in n_pre n_obs : nat}.

Variable C : AuditContext n_in n_pre n_obs.
Notation P := (context_policy C).

Variable p_committed : policy.

Variable digest_eqb : digest -> digest -> bool.
Hypothesis digest_eqb_true : forall a b, digest_eqb a b = true -> a = b.

(* F.3 hashing. *)
Variable model_digest_of preproc_digest_of inference_digest_of : bytes -> digest.

(* F.3 wire decoders. *)
Variable parse_descriptor : digest -> option descriptor.
Variable probe_of_spec :
  bytes -> option (Vec Z n_pre * Vec Z n_obs).

(* the descriptor and manifest commitment this audit authenticated. *)
Variable committed_descriptor : descriptor.
Variable committed_authcommitment : manifest_commitment.

(* F.3: the manifest commitment authenticates the descriptor's digests. *)
Variable commits : manifest_commitment -> descriptor -> Prop.
Hypothesis committed_authentic : commits committed_authcommitment committed_descriptor.

Definition pass_finding (id : string) : finding := mkFinding id Pass None.

Definition byte_digest_consistent (lc : loaded_context) (d : descriptor) : Prop :=
  model_digest_of (loaded_model_bytes lc) = d_model_digest d /\
  preproc_digest_of (loaded_preproc_bytes lc) = d_preproc_digest d /\
  inference_digest_of (loaded_inference_bytes lc) = d_inference_digest d.

(* residual F.3 semantic obligation, now conditioned on digest-consistency with
   the committed descriptor. *)
Variable realises_C : loaded_context -> Prop.
Hypothesis committed_bytes_realise :
  forall lc, byte_digest_consistent lc committed_descriptor -> realises_C lc.

(* ----- O1 / O2 ----- *)

Definition preflight_check (lc : loaded_context) : preflight_result :=
  match parse_descriptor (loaded_descriptor lc) with
  | None =>
      PreflightFail ArtifactMismatch [failed_finding "O1" "descriptor_unparseable"]
  | Some d =>
      if digest_eqb (model_digest_of (loaded_model_bytes lc)) (d_model_digest d)
      then if andb (digest_eqb (preproc_digest_of (loaded_preproc_bytes lc))
                               (d_preproc_digest d))
                   (digest_eqb (inference_digest_of (loaded_inference_bytes lc))
                               (d_inference_digest d))
           then PreflightOk [pass_finding "O1"; pass_finding "O2"]
           else PreflightFail SpecMismatch
                  [failed_finding "O2" "preproc_or_inference_digest_mismatch"]
      else PreflightFail ArtifactMismatch
             [failed_finding "O1" "model_artifact_digest_mismatch"]
  end.

Theorem preflight_ok_binds :
  forall lc fs,
    preflight_check lc = PreflightOk fs ->
    exists d,
      parse_descriptor (loaded_descriptor lc) = Some d /\
      byte_digest_consistent lc d.
Proof.
  intros lc fs H. unfold preflight_check in H.
  destruct (parse_descriptor (loaded_descriptor lc)) as [d|] eqn:Hd;
    [| discriminate].
  destruct (digest_eqb (model_digest_of (loaded_model_bytes lc)) (d_model_digest d))
    eqn:E1; [| discriminate].
  destruct (andb (digest_eqb (preproc_digest_of (loaded_preproc_bytes lc))
                             (d_preproc_digest d))
                 (digest_eqb (inference_digest_of (loaded_inference_bytes lc))
                             (d_inference_digest d))) eqn:E23; [| discriminate].
  apply andb_true_iff in E23 as [E2 E3].
  exists d. split; [ reflexivity |].
  unfold byte_digest_consistent.
  split; [ apply digest_eqb_true; exact E1 |].
  split; [ apply digest_eqb_true; exact E2 | apply digest_eqb_true; exact E3 ].
Qed.

Theorem preflight_fail_reason :
  forall lc rn fs,
    preflight_check lc = PreflightFail rn fs ->
    rn = ArtifactMismatch \/ rn = SpecMismatch.
Proof.
  intros lc rn fs H. unfold preflight_check in H.
  destruct (parse_descriptor (loaded_descriptor lc)) as [d|];
    [| injection H as <- _; left; reflexivity ].
  destruct (digest_eqb _ _); [| injection H as <- _; left; reflexivity ].
  destruct (andb _ _); [ discriminate | injection H as <- _; right; reflexivity ].
Qed.

(* O1/O2 success on an lc whose descriptor IS the committed one: the loaded
   bytes are digest-consistent with the descriptor the authenticated commitment
   binds, and (F.3) they realise C. *)
Theorem preflight_ok_artifact_bound :
  forall lc fs,
    preflight_check lc = PreflightOk fs ->
    parse_descriptor (loaded_descriptor lc) = Some committed_descriptor ->
    byte_digest_consistent lc committed_descriptor /\
    commits committed_authcommitment committed_descriptor /\
    realises_C lc.
Proof.
  intros lc fs Hpf Hdc.
  destruct (preflight_ok_binds lc Hpf) as (d & Hd & Hcons).
  rewrite Hdc in Hd. injection Hd as <-.
  split; [ exact Hcons |].
  split; [ exact committed_authentic |].
  exact (committed_bytes_realise Hcons).
Qed.

(* ----- O3 ----- *)

Definition eval_o3_check (lc : loaded_context) (ev : exec_event) (p : policy)
  : o3_result :=
  match probe_of_spec (loaded_inference_bytes lc) with
  | None => O3Fail [failed_finding "O3" "inference_spec_probe_unavailable"]
  | Some (pin, pobs) =>
      if andb (list_zeqb (event_input ev) (Vector.to_list pin))
              (match event_outcome ev with
               | ExecOk obs => list_zeqb obs (Vector.to_list pobs)
               | _ => false
               end)
      then O3Ok (mkResolvedContext p (loaded_context_token lc) (loaded_descriptor lc))
                [pass_finding "O3"]
      else O3Fail [failed_finding "O3" "probe_input_or_observation_mismatch"]
  end.

Theorem eval_o3_ok_binds :
  forall lc ev p rc fs,
    eval_o3_check lc ev p = O3Ok rc fs ->
    exists pin pobs,
      probe_of_spec (loaded_inference_bytes lc) = Some (pin, pobs) /\
      event_input ev = Vector.to_list pin /\
      event_outcome ev = ExecOk (Vector.to_list pobs) /\
      resolved_policy rc = p /\
      resolved_descriptor rc = loaded_descriptor lc.
Proof.
  intros lc ev p rc fs H. unfold eval_o3_check in H.
  destruct (probe_of_spec (loaded_inference_bytes lc)) as [[pin pobs]|] eqn:Hp;
    [| discriminate].
  destruct (andb (list_zeqb (event_input ev) (Vector.to_list pin))
                 (match event_outcome ev with
                  | ExecOk obs => list_zeqb obs (Vector.to_list pobs)
                  | _ => false end)) eqn:E; [| discriminate].
  apply andb_true_iff in E as [Ein Eout].
  apply list_zeqb_true_iff in Ein.
  injection H as <- _. cbn.
  exists pin, pobs. split; [ reflexivity |]. split; [ exact Ein |].
  destruct (event_outcome ev) as [obs| |] eqn:Ho; try discriminate.
  apply list_zeqb_true_iff in Eout. subst obs.
  repeat split; reflexivity.
Qed.

(* ----- resolve ----- *)

Definition resolve (lc : loaded_context) (ev : exec_event)
  : option (AuditContext n_in n_pre n_obs * resolved_context) :=
  match preflight_check lc with
  | PreflightFail _ _ => None
  | PreflightOk _ =>
      match eval_o3_check lc ev p_committed with
      | O3Fail _ => None
      | O3Ok rc _ => Some (C, rc)
      end
  end.

Theorem resolve_some_is_committed :
  forall lc ev Cr rc,
    resolve lc ev = Some (Cr, rc) ->
    parse_descriptor (loaded_descriptor lc) = Some committed_descriptor ->
    Cr = C /\
    resolved_policy rc = p_committed /\
    resolved_descriptor rc = loaded_descriptor lc /\
    byte_digest_consistent lc committed_descriptor /\
    commits committed_authcommitment committed_descriptor /\
    realises_C lc /\
    (exists pin pobs,
       probe_of_spec (loaded_inference_bytes lc) = Some (pin, pobs) /\
       event_input ev = Vector.to_list pin /\
       event_outcome ev = ExecOk (Vector.to_list pobs)).
Proof.
  intros lc ev Cr rc H Hdc. unfold resolve in H.
  destruct (preflight_check lc) as [rn fs | pf] eqn:Hpf; [ discriminate |].
  destruct (eval_o3_check lc ev p_committed) as [o3f | rc0 o3f] eqn:Ho3;
    [ discriminate |].
  injection H as <- <-.
  destruct (preflight_ok_artifact_bound lc Hpf Hdc) as (Hcons & Hauth & Hreal).
  destruct (eval_o3_ok_binds lc ev p_committed Ho3)
    as (pin & pobs & Hps & Hein & Heout & Hrp & Hrd).
  split; [ reflexivity |].
  split; [ exact Hrp |].
  split; [ exact Hrd |].
  split; [ exact Hcons |].
  split; [ exact Hauth |].
  split; [ exact Hreal |].
  exists pin, pobs.
  split; [ exact Hps |]. split; [ exact Hein | exact Heout ].
Qed.

Theorem stage1_stage2_use_resolved_context :
  forall lc ev Cr rc,
    resolve lc ev = Some (Cr, rc) ->
    parse_descriptor (loaded_descriptor lc) = Some committed_descriptor ->
    (forall sd cd i c,
       stage1_semantic_check Cr sd cd i c = stage1_semantic_check C sd cd i c) /\
    (forall rng rc' cfg tr ps,
       adapter_stage2_check Cr rng rc' cfg tr ps
       = adapter_stage2_check C rng rc' cfg tr ps) /\
    context_policy Cr = P.
Proof.
  intros lc ev Cr rc H Hdc.
  destruct (resolve_some_is_committed lc ev H Hdc) as (-> & _).
  repeat split; reflexivity.
Qed.

End CtxRes.
