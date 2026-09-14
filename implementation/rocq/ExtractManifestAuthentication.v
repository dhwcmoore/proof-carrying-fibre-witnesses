(* Extraction of the concrete 2.4.1 authenticated-manifest validation for an
   executable exercise + normative-vector harness.

   sha256_hex, ed25519_verify and ed25519_pubkey_valid are Section VARIABLES of
   ManifestAuthentication: the extracted functions take them as arguments.  The
   OCaml harness supplies a real SHA-256 (the `sha` library), a pure-OCaml RFC
   8032 Ed25519 verify, and a canonical non-small-order public-key check, and
   checks them against the frozen campaign-manifest digest vector and an official
   Ed25519 test vector.

   Strings extract natively; there is no bignum dependency in this file. *)
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt
  ExtrOcamlNativeString.
From PCFW Require Import CanonicalV1 ManifestAuthentication ManifestLedger
  ManifestAudit CampaignRecord RecordCrosscheck CompletenessWellformed.

Extraction Language OCaml.
Extraction "ocaml/extracted_manifest_auth.ml"
  render_manifest campaign_manifest_digest
  parse_commitment_impl parse_manifest_impl
  all_lower_hex hex_decode
  signer_authorised_impl signature_valid_impl
  ld_mismatch ledger_mismatch_impl
  manifest_audit_matches_impl
  render_campaign_record parse_record_impl record_identity_mismatch_impl
  parse_record_full_impl parse_budget_object parse_scr_outcome
  crosscheck_impl crosscheck_budget_impl derive_expected record_crosscheck_impl
  derive_one advisory_finding_ids
  wellformed_scheme wellformed_body wellformed_certificate
  op_completeness_wellformed_impl.
