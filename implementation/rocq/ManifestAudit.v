(** Concrete [op_manifest_audit_matches]: VERDICT_SEMANTICS.md 5 step 5 --

      ti.M.audit_instance_id = <the committed policy payload>.audit_instance_id

    [manifest_audit_matches_impl] decodes the manifest with the supplied decoder
    (the pipeline passes [ManifestAuthentication.parse_manifest_impl]) and
    compares [cm_audit_instance_id] with [policy_audit_instance_id_of (ti_policy
    ti)] by exact string equality.  A decode failure is [false].

    [policy_audit_instance_id_of] is an abstract projection of the policy string.
    Its correctness -- that it returns the audit_instance_id the load-validated
    policy actually commits to -- stays tied to policy load validation until the
    policy representation and its parser become concrete (a later unit).  This
    module proves only the comparison logic and its full [true] equivalence. *)

From Coq Require Import String Bool.
From PCFW Require Import Orchestration CanonicalV1.

Section Audit.

Variable parse : manifest -> option campaign_manifest_view.
Variable policy_audit_instance_id_of : policy -> string.

Definition manifest_audit_matches_impl (M : manifest) (ti : trusted_inputs) : bool :=
  match parse M with
  | None => false
  | Some cm =>
      String.eqb (cm_audit_instance_id cm)
                 (policy_audit_instance_id_of (ti_policy ti))
  end.

(* full equivalence, both directions -- not one-way soundness *)
Lemma manifest_audit_matches_impl_true_iff : forall M ti,
  manifest_audit_matches_impl M ti = true <->
  exists cm,
    parse M = Some cm /\
    cm_audit_instance_id cm = policy_audit_instance_id_of (ti_policy ti).
Proof.
  intros M ti. unfold manifest_audit_matches_impl. split.
  - destruct (parse M) as [cm|] eqn:E; [| discriminate].
    intro H. exists cm. split; [ reflexivity |].
    apply String.eqb_eq. exact H.
  - intros (cm & Hp & Hid). rewrite Hp. apply String.eqb_eq. exact Hid.
Qed.

Lemma manifest_audit_matches_impl_false_iff : forall M ti,
  manifest_audit_matches_impl M ti = false <->
  parse M = None \/
  exists cm,
    parse M = Some cm /\
    cm_audit_instance_id cm <> policy_audit_instance_id_of (ti_policy ti).
Proof.
  intros M ti. unfold manifest_audit_matches_impl. split.
  - destruct (parse M) as [cm|] eqn:E.
    + intro H. right. exists cm. split; [ reflexivity |].
      apply String.eqb_neq. exact H.
    + intro. left. reflexivity.
  - intros [Hn | (cm & Hp & Hne)].
    + rewrite Hn. reflexivity.
    + rewrite Hp. apply String.eqb_neq. exact Hne.
Qed.

End Audit.
