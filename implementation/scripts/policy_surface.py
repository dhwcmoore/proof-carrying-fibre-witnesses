#!/usr/bin/env python3
"""Kernel-typecheck the seven parametric policy interfaces, including premises."""

from pathlib import Path
import re
import subprocess
import sys
import tempfile

import audit


PREAMBLE = """
From Coq Require Import String.
From PCFW Require Import Orchestration CanonicalV1 ManifestMatching
  ManifestAuthentication ManifestPipeline.
Goal forall p ti, policy_binding p ti = (ti_policy ti = p).
Proof. intros. reflexivity. Qed.
Section InterfaceChecks.
Variable digest_eqb : digest -> digest -> bool.
Variable digest_eqb_true : forall a b, digest_eqb a b = true -> a = b.
Variable parse_manifest : manifest -> option campaign_manifest_view.
Variable p_committed : policy.
Variable committed_descriptor : cd.
Variable policy_context_of : policy -> cd.
Variable manifest_authenticated_by : manifest_commitment -> manifest -> Prop.
Variable audit_commitment : manifest_commitment.
Variable audit_manifest : manifest.
Variable audit_view : campaign_manifest_view.
Variable audit_authenticated : manifest_authenticated_by audit_commitment audit_manifest.
Variable audit_manifest_parses : parse_manifest audit_manifest = Some audit_view.
Variable committed_policy_context : policy_context_of p_committed = committed_descriptor.
Variable ops : primitive_ops.
Variable ops_context_match : op_manifest_context_matches ops =
  manifest_context_matches_impl digest_eqb parse_manifest policy_context_of.
Variable validated_commitment_is_audit : forall ti ac l0,
  validate_campaign ops ti = ValidCampaign ac l0 ->
  authenticated_commitment ac = audit_commitment.
Variable validated_manifest_is_audit : forall ti ac l0,
  validate_campaign ops ti = ValidCampaign ac l0 -> ti_manifest ti = audit_manifest.
Variable sha256_hex : bytes -> digest.
Variable ed25519_verify : bytes -> bytes -> bytes -> bool.
Variable ed25519_pubkey_valid : bytes -> bool.
Variable policy_audit_instance_id_of : policy -> string.
Variable committed_audit_instance_id : string.
Variable committed_policy_audit_id :
  policy_audit_instance_id_of p_committed = committed_audit_instance_id.
Variable concrete_manifest_parses : parse_manifest_impl audit_manifest = Some audit_view.
Variable base : primitive_ops.
Let pipe := pipeline_ops sha256_hex ed25519_verify ed25519_pubkey_valid
  digest_eqb policy_context_of policy_audit_instance_id_of base.
Variable pipeline_manifest_is_audit : forall ti ac l0,
  validate_campaign pipe ti = ValidCampaign ac l0 -> ti_manifest ti = audit_manifest.
"""

# Explicit @ applications and type annotations check both the complete parameter
# sequence and the remaining per-input statement. An additional premise, even
# renamed, cannot be silently supplied or skipped. No hash-to-policy function is
# present in these expected signatures.
INTERFACES = {
    "ManifestMatching.manifest_policy_matches_impl_sound": r"""
(@manifest_policy_matches_impl_sound digest_eqb parse_manifest p_committed audit_view :
 forall ti, policy_binding p_committed ti ->
 parse_manifest (ti_manifest ti) = Some audit_view ->
 manifest_policy_matches_impl digest_eqb parse_manifest (ti_manifest ti) ti = true ->
 ti_policy ti = p_committed)
""",
    "ManifestMatching.validate_campaign_concrete_binds_policy": r"""
(@validate_campaign_concrete_binds_policy p_committed ops :
 forall ti ac l0, policy_binding p_committed ti ->
 validate_campaign ops ti = ValidCampaign ac l0 -> ti_policy ti = p_committed)
""",
    "ManifestMatching.validate_campaign_concrete_binds": r"""
(@validate_campaign_concrete_binds digest_eqb digest_eqb_true parse_manifest
 p_committed committed_descriptor policy_context_of manifest_authenticated_by
 audit_commitment audit_manifest audit_view audit_authenticated audit_manifest_parses
 committed_policy_context ops ops_context_match validated_commitment_is_audit
 validated_manifest_is_audit :
 forall ti ac l0, policy_binding p_committed ti ->
 validate_campaign ops ti = ValidCampaign ac l0 ->
 ti_policy ti = p_committed /\
 commits_impl parse_manifest manifest_authenticated_by (authenticated_commitment ac)
   committed_descriptor)
""",
    "ManifestMatching.assess_validated_live_concrete": r"""
(@assess_validated_live_concrete p_committed ops :
 forall ti ac l0 tr cb, policy_binding p_committed ti ->
 validate_campaign ops ti = ValidCampaign ac l0 ->
 assess_validated ops ti (ValidCampaign ac l0) (LiveTranscript tr cb) =
 decide ops (replay ops ac cb (ti_config ti) (ti_policy_document ti) p_committed l0 tr)
   ac ti tr (LiveCapture (op_transcript_digest ops tr))
   (AuthenticatedCommitment (commitment_digest (authenticated_commitment ac))))
""",
    "ManifestMatching.assess_validated_offline_concrete": r"""
(@assess_validated_offline_concrete p_committed ops :
 forall ti ac l0 tr wd cb, policy_binding p_committed ti ->
 validate_campaign ops ti = ValidCampaign ac l0 ->
 assess_validated ops ti (ValidCampaign ac l0) (OfflineParse (WellformedParse tr wd) cb) =
 decide ops (replay ops ac cb (ti_config ti) (ti_policy_document ti) p_committed l0 tr)
   ac ti tr (OfflineTranscript (op_transcript_digest ops tr) wd)
   (AuthenticatedCommitment (commitment_digest (authenticated_commitment ac))))
""",
    "ManifestPipeline.validate_campaign_pipeline": r"""
(@validate_campaign_pipeline sha256_hex ed25519_verify ed25519_pubkey_valid
 digest_eqb digest_eqb_true p_committed committed_descriptor policy_context_of
 policy_audit_instance_id_of audit_manifest audit_view concrete_manifest_parses
 committed_policy_context base pipeline_manifest_is_audit :
 forall ti ac l0, policy_binding p_committed ti ->
 validate_campaign pipe ti = ValidCampaign ac l0 ->
 manifest_authenticated_by_impl sha256_hex ed25519_verify ed25519_pubkey_valid
   (ti_config ti) (authenticated_commitment ac) (authenticated_manifest ac) /\
 ti_policy ti = p_committed /\
 pipeline_commits sha256_hex ed25519_verify ed25519_pubkey_valid (ti_config ti)
   (authenticated_commitment ac) committed_descriptor)
""",
    "ManifestPipeline.validate_campaign_audit_agrees": r"""
(@validate_campaign_audit_agrees sha256_hex ed25519_verify ed25519_pubkey_valid
 digest_eqb p_committed policy_context_of policy_audit_instance_id_of
 committed_audit_instance_id committed_policy_audit_id base :
 forall ti ac l0, policy_binding p_committed ti ->
 validate_campaign pipe ti = ValidCampaign ac l0 ->
 exists v, parse_manifest_impl (ti_manifest ti) = Some v /\
 cm_audit_instance_id v = committed_audit_instance_id)
""",
}


def validate_result(result, symbols):
    output = result.stdout + "\n" + result.stderr
    if result.returncode or re.search(r"\b(?:Error|Anomaly)\s*:", output, re.I):
        raise audit.AuditError("policy interface typecheck failed:\n" + output)
    markers = re.findall(r"^PCFW_POLICY_CHECKED:.*$", output, re.M)
    if markers != [f"PCFW_POLICY_CHECKED:{s}" for s in symbols]:
        raise audit.AuditError("missing, duplicated or reordered policy interface checks")


def check_interfaces(impl=audit.IMPL, interfaces=INTERFACES, preamble=PREAMBLE):
    if not interfaces:
        raise audit.AuditError("empty policy interface surface")
    lines = [preamble]
    for symbol, statement in interfaces.items():
        lines.extend([f"Check {statement}.",
                      f'Goal True. idtac "PCFW_POLICY_CHECKED:{symbol}". Abort.'])
    lines.append("End InterfaceChecks.")
    with tempfile.TemporaryDirectory(prefix="pcfw-policy-interface-") as directory:
        source = Path(directory) / "PolicyInterfaces.v"
        source.write_text("\n".join(lines))
        result = subprocess.run(["coqc", "-Q", "rocq", "PCFW", str(source)],
                                cwd=impl, text=True, capture_output=True)
    validate_result(result, interfaces)
    print(f"PASS: {len(interfaces)} parametric policy interfaces checked; explicit local binding")


def main():
    try:
        check_interfaces()
    except (audit.AuditError, OSError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
