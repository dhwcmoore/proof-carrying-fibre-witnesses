(** Concrete `op_completeness_wellformed` (VERDICT_SEMANTICS.md 5, step 9):

      ti.rec.completeness = Complete c  =>  c well-formed

    the LAST guard in `validate_campaign`, reached only after steps 1-8 (parse,
    signer, signature, policy/audit/context match, ledger, record identity) have
    all passed.  On `false` `validate_campaign` returns
    `Invalid CompletenessMalformed`; the wiring and the frozen check ORDER are
    UNCHANGED -- this unit only supplies the function occupying the
    already-existing `op_completeness_wellformed` slot.

    Revision 2 -- reviewer HELD revision 1 on two grounds, both addressed here:

    1. **Invented grammar.**  `wellformed_scheme` reused
       `ManifestAuthentication.printable_ascii_id` -- a predicate scoping a
       ROUND-TRIP THEOREM about manifest identifiers (`manifest_roundtrip_wf`),
       never a decoder-level acceptance gate anywhere in this codebase -- and so
       rejected DECODED strings (containing a quote, a backslash, a raw high
       byte) that `scheme:<string>` (AUDIT_POLICY 2.2.5) does not forbid.  FIXED:
       `wellformed_scheme` now requires only non-emptiness -- the one structural
       fact well-formedness can state without a scheme registry (empty in v0).
       `wellformed_body` keeps `CampaignRecord.skip_value` (the project's
       existing, reviewer-accepted canonical-value recognizer) but the header
       and every doc reference now say so HONESTLY: it recognises exactly one
       value of the **ASCII-wire canonical subset** `CampaignRecord.v` /
       `ManifestAuthentication.v` already use throughout this codebase (raw
       non-ASCII UTF-8 is OUT OF SCOPE for v0, same restriction, same
       rationale, same "future work" framing as those modules) -- NOT the full
       §2.2 canonical-value language, which permits raw UTF-8 string content.
       This narrower v0 scope is a proposed, explicitly flagged decision
       pending reviewer concurrence (the alternative -- a UTF-8-tolerant
       canonical-value recognizer -- is a substantially larger, separate
       decoder unit).  An INDEPENDENT propositional characterisation
       (`completeness_status_wf`, not phrased via this unit's own Boolean
       helpers) is added below, with `op_completeness_wellformed_impl_true_iff`
       now stated against it; the former Boolean-only statement survives as
       `_true_iff_bool`.
    2. **Unbound check.**  The governing step reads `ti.rec.completeness`, but
       `op_completeness_wellformed_impl` was applied to the separate
       `Orchestration` field `ti_completeness ti`, and no decoder or premise
       connected the two -- `CampaignRecord.skip_value` only SYNTACTICALLY
       consumes the record's `completeness` field, never interprets it.  FIXED
       in `ManifestPipeline.v`: an explicit per-input F.3 premise
       `record_completeness_load_validated`, exactly like
       `ManifestMatching.policy_digest_load_validated`, states that a
       (not-yet-built) completeness decoder applied to `ti_record ti` would
       recover `ti_completeness ti`; `validate_campaign_completeness_bound_to_
       record` is conditional on it and states the governing obligation over
       `ti.rec.completeness` directly.  A concrete decoder (preferred, per the
       reviewer) is future work -- see `PHASE_1_COMPLETENESS_WELLFORMED.md` §5.

    SCOPE.  `Orchestration.completeness_status` is already a typed value
    (`CompletenessUnknown | CompletenessIncomplete | CompletenessComplete
    completeness_certificate`).  There is no wire-decoding step in THIS module:
    it defines a PURE structural well-formedness predicate over an already-typed
    value.  It is UNRELATED to `Orchestration.valid_completeness_certificate_v0`
    (the *semantic* check `decide`'s `EXACT` branch uses -- a completeness-scheme
    REGISTRY lookup, empty in v0, hence always `false`, VERDICT_SEMANTICS.md
    6.9); that predicate, and `EXACT`'s dead-code status, are untouched by this
    unit.  `op_transcript_digest` is untouched and stays open.

    `completeness_certificate := { scheme : string ; body : string }`
    (AUDIT_POLICY_AND_EVIDENCE.md 2.2.5: `{scheme:<string>, body:<the
    canonical_value verbatim>}` -- `body` stores the certificate term's raw
    canonical text, the same convention `RecordCrosscheck.finding_offending`
    uses).  With the completeness-scheme registry empty in v0 there is no
    per-scheme grammar to check, so well-formedness is exactly:

      - `scheme` is non-empty (any other content -- Unicode, quotes,
        backslashes -- is legitimate DECODED string data; `scheme:<string>`
        imposes no further wire grammar, and only the empty string can never
        name a (future) scheme);
      - `body` is exactly one value of the ASCII-wire canonical subset, wholly
        consumed (see revision-2 note above).

    `CompletenessUnknown` / `CompletenessIncomplete` carry no certificate and are
    unconditionally well-formed. *)

From Coq Require Import String Ascii List Bool.
From PCFW Require Import Orchestration CampaignRecord.
Import ListNotations.
Open Scope string_scope.

(* ================= the two structural checks ================= *)

(* [scheme:<string>] (AUDIT_POLICY 2.2.5) carries NO further wire grammar.  The
   only structural fact well-formedness can state without a scheme registry
   (empty in v0) is that a scheme actually NAMES something -- the empty string
   cannot select any (future) scheme.  Unicode, a quote, or a backslash in the
   DECODED string are all legitimate: those are wire-ESCAPING concerns already
   resolved by the upstream JSON string decoder, not properties of the
   resulting value, so they impose no constraint here. *)
Definition wellformed_scheme (s : string) : bool := negb (String.eqb s "").

Lemma wellformed_scheme_true_iff : forall s,
  wellformed_scheme s = true <-> s <> "".
Proof.
  intro s. unfold wellformed_scheme.
  rewrite Bool.negb_true_iff, String.eqb_neq.
  reflexivity.
Qed.

(* [s] is exactly one value of the ASCII-wire canonical subset (see the
   revision-2 header note): [skip_value] consumes it and leaves NOTHING
   behind. *)
Definition wellformed_body (s : string) : bool :=
  match CampaignRecord.skip_value (String.length s) s with
  | Some EmptyString => true
  | _ => false
  end.

Lemma wellformed_body_true_iff : forall s,
  wellformed_body s = true <->
  CampaignRecord.skip_value (String.length s) s = Some EmptyString.
Proof.
  intro s. unfold wellformed_body.
  destruct (CampaignRecord.skip_value (String.length s) s) as [[|c r]|] eqn:E.
  - split; intro H; reflexivity.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
Qed.

(* ================= the certificate, and the op ================= *)

Definition wellformed_certificate (c : completeness_certificate) : bool :=
  wellformed_scheme (completeness_scheme c) && wellformed_body (completeness_body c).

Definition op_completeness_wellformed_impl (cs : completeness_status) : bool :=
  match cs with
  | CompletenessUnknown => true
  | CompletenessIncomplete => true
  | CompletenessComplete c => wellformed_certificate c
  end.

(* ----- Boolean-only characterisation (supporting) ----- *)
Theorem op_completeness_wellformed_impl_true_iff_bool : forall cs,
  op_completeness_wellformed_impl cs = true <->
  (cs = CompletenessUnknown \/ cs = CompletenessIncomplete \/
   exists c, cs = CompletenessComplete c /\
     wellformed_scheme (completeness_scheme c) = true /\
     wellformed_body (completeness_body c) = true).
Proof.
  intros [ | | c]; cbn.
  - split; intro; [left; reflexivity | reflexivity].
  - split; intro; [right; left; reflexivity | reflexivity].
  - unfold wellformed_certificate. rewrite andb_true_iff. split.
    + intros [Hs Hb]. right; right. exists c. split; [reflexivity | split; assumption].
    + intros [H | [H | (c' & Heq & Hs & Hb)]]; try discriminate.
      injection Heq as <-. split; assumption.
Qed.

(* ================= independent (specification-level) well-formedness =================

   Stated directly against the wire fields' own contract, NOT via this unit's
   own [wellformed_scheme] / [wellformed_body] Booleans -- so the correspondence
   theorem below is a genuine characterisation, not a re-typed restatement of
   the implementation. *)

Definition scheme_wf (s : string) : Prop := s <> "".

Definition body_wf (s : string) : Prop :=
  CampaignRecord.skip_value (String.length s) s = Some EmptyString.

Definition certificate_wf (c : completeness_certificate) : Prop :=
  scheme_wf (completeness_scheme c) /\ body_wf (completeness_body c).

Definition completeness_status_wf (cs : completeness_status) : Prop :=
  match cs with
  | CompletenessUnknown => True
  | CompletenessIncomplete => True
  | CompletenessComplete c => certificate_wf c
  end.

(* ----- positive characterisation, over the independent relation ----- *)
Theorem op_completeness_wellformed_impl_true_iff : forall cs,
  op_completeness_wellformed_impl cs = true <-> completeness_status_wf cs.
Proof.
  intros [ | | c]; cbn.
  - split; [intros _; exact I | intros _; reflexivity].
  - split; [intros _; exact I | intros _; reflexivity].
  - unfold certificate_wf, scheme_wf, body_wf, wellformed_certificate.
    rewrite andb_true_iff, wellformed_scheme_true_iff, wellformed_body_true_iff.
    tauto.
Qed.

(* ----- negative characterisation, over the same relation ----- *)
Theorem op_completeness_wellformed_impl_false_iff : forall cs,
  op_completeness_wellformed_impl cs = false <-> ~ completeness_status_wf cs.
Proof.
  intro cs. rewrite <- Bool.not_true_iff_false, op_completeness_wellformed_impl_true_iff.
  reflexivity.
Qed.

(* spelled out concretely -- which field failed, not just "not well-formed" --
   for readability and for cross-checking against the harness's mutations. *)
Corollary op_completeness_wellformed_impl_false_spec : forall cs,
  op_completeness_wellformed_impl cs = false <->
  exists c, cs = CompletenessComplete c /\
    (completeness_scheme c = "" \/
     CampaignRecord.skip_value (String.length (completeness_body c)) (completeness_body c)
       <> Some EmptyString).
Proof.
  intros [ | | c]; cbn.
  - split; [discriminate | intros (c & Heq & _); discriminate].
  - split; [discriminate | intros (c & Heq & _); discriminate].
  - unfold wellformed_certificate. rewrite andb_false_iff. split.
    + intros [H | H].
      * exists c. split; [reflexivity |]. left.
        unfold wellformed_scheme in H. rewrite Bool.negb_false_iff in H.
        apply String.eqb_eq in H. exact H.
      * exists c. split; [reflexivity |]. right.
        intro Hc. rewrite <- wellformed_body_true_iff in Hc. congruence.
    + intros (c' & Heq & [Hs | Hb]); injection Heq as <-.
      * left. unfold wellformed_scheme. rewrite Bool.negb_false_iff.
        apply String.eqb_eq. exact Hs.
      * right. destruct (wellformed_body (completeness_body c)) eqn:E; [| reflexivity].
        exfalso. apply Hb. apply wellformed_body_true_iff. exact E.
Qed.

(* ================= normative vectors ================= *)

Lemma wellformed_scheme_rejects_empty : wellformed_scheme "" = false.
Proof. vm_compute. reflexivity. Qed.
(* a quote, a backslash, and a raw high byte in a DECODED scheme string are all
   legitimate -- revision-2 fix (see the header). *)
Lemma wellformed_scheme_accepts_quote :
  wellformed_scheme "sch""eme" = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wellformed_scheme_accepts_backslash :
  wellformed_scheme "sch\eme" = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wellformed_scheme_accepts_high_byte :
  wellformed_scheme (String (ascii_of_nat 233) EmptyString) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wellformed_scheme_accepts_label :
  wellformed_scheme "scheme-v1" = true.
Proof. vm_compute. reflexivity. Qed.

Lemma wellformed_body_rejects_empty : wellformed_body "" = false.
Proof. vm_compute. reflexivity. Qed.
Lemma wellformed_body_rejects_trailing_garbage :
  wellformed_body "5x" = false.
Proof. vm_compute. reflexivity. Qed.
Lemma wellformed_body_rejects_leading_zero :
  wellformed_body "01" = false.
Proof. vm_compute. reflexivity. Qed.
Lemma wellformed_body_rejects_dup_keys :
  wellformed_body "{""a"":1,""a"":2}" = false.
Proof. vm_compute. reflexivity. Qed.
Lemma wellformed_body_rejects_not_json :
  wellformed_body "not-json" = false.
Proof. vm_compute. reflexivity. Qed.
(* v0's ASCII-wire subset does not accept a raw high byte inside a body STRING
   -- unlike a top-level scheme string, a body string still goes through the
   canonical-value string grammar ([CampaignRecord.skip_value] ->
   [ManifestAuthentication.parse_json_string]), which is scoped to the
   ASCII-wire subset throughout this codebase (see the header's revision-2
   note; full Unicode canonical_value is future work, pending approval). *)
Lemma wellformed_body_rejects_high_byte_string :
  wellformed_body (String (ascii_of_nat 34) (String (ascii_of_nat 233)
                     (String (ascii_of_nat 34) EmptyString))) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma wellformed_body_accepts_object :
  wellformed_body "{""a"":1,""b"":2}" = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wellformed_body_accepts_scalar :
  wellformed_body "true" = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wellformed_body_accepts_string :
  wellformed_body """hello""" = true.
Proof. vm_compute. reflexivity. Qed.

Lemma op_completeness_wellformed_impl_unknown :
  op_completeness_wellformed_impl CompletenessUnknown = true.
Proof. reflexivity. Qed.
Lemma op_completeness_wellformed_impl_incomplete :
  op_completeness_wellformed_impl CompletenessIncomplete = true.
Proof. reflexivity. Qed.
Lemma op_completeness_wellformed_impl_complete_wf :
  op_completeness_wellformed_impl
    (CompletenessComplete (mkCompletenessCertificate "scheme-v1" "{""a"":1}"))
  = true.
Proof. vm_compute. reflexivity. Qed.
Lemma op_completeness_wellformed_impl_complete_bad_scheme :
  op_completeness_wellformed_impl
    (CompletenessComplete (mkCompletenessCertificate "" "{""a"":1}"))
  = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_completeness_wellformed_impl_complete_bad_body :
  op_completeness_wellformed_impl
    (CompletenessComplete (mkCompletenessCertificate "scheme-v1" "not-json"))
  = false.
Proof. vm_compute. reflexivity. Qed.
(* a quoted scheme is now ACCEPTED (revision-2 fix). *)
Lemma op_completeness_wellformed_impl_complete_quoted_scheme :
  op_completeness_wellformed_impl
    (CompletenessComplete (mkCompletenessCertificate "sch""eme" "{""a"":1}"))
  = true.
Proof. vm_compute. reflexivity. Qed.
