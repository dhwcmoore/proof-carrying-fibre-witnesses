# What `PHASE_0_CLOSURE_REPORT.md` must assert

This is a checklist for the designated reviewer. It is **not** a draft of the
report. The reviewer writes the report from the reviewer's own assessment and
places it in the shared project folder.

1. **Governing set at Revision 15.** The reviewer concurs with the amended
   `VERDICT_SEMANTICS.md`, `AUDIT_POLICY_AND_EVIDENCE.md` and `THREAT_MODEL.md`
   (`revised/` in this package), and states that the `revised/` copies now
   replace the Revision-14 root files. The diffs in `diffs/` are the exact
   change set.

2. **Scope of the amendment.** `ctx_reason` unchanged; `campaign_obstruction` +=
   `InconsistentContextBundle` (nullary); `context_state` +=
   `ContextBundleInconsistent` (nullary); §6.4 description corrected; §6.5 slot
   table + one row; §2.2 encoding + two nullary constructors; THREAT_MODEL +
   T30. No change to `T1`/`A1`/`E1`, the kernel, `TRUST_BOUNDARY.md`,
   `CLAIM_AND_DEFINITIONS.md`, `PROJECT_CHARTER.md`, `NON_CLAIMS.md`.

3. **Evidence separation.** The report reproduces `EVIDENCE_LEDGER.md`: section A
   (source and archive integrity) was independently verified by the reviewer;
   section B (build, `coqchk`, `Print Assumptions`, `make test`) was executed on
   the implementation-author's machine only, because the reviewer's environment
   lacks `coqc`. The report must not present section B as independently
   reproduced.

4. **What Phase 0 closure does NOT establish.** Closure ratifies the Phase 0
   specification and the mathematical core. It does not complete:
   - the five orchestration proof obligations still `Admitted` in
     `Orchestration.v` (`T2_sound`, `T2_complete`, `stage1_over_is_terminal`,
     `exact_unreachable_v0`, `validation_fuel_obstructed_unreachable_when_sufficient`);
   - the `primitive_ops` implementations and their contracts (including
     `stage2_witness_index_contract`);
   - extracted-OCaml build and execution against a real bignum library.
   These are Phase 1 work and must be listed in the report as open.

5. **Reviewer / author separation.** The report records that it is issued by the
   designated reviewer role, not the implementation-author role, and that the
   author neither issued nor was authorised to issue it.

6. **Consistency-audit decision (reviewer's call).**
   `PHASE_0_CONSISTENCY_AUDIT.md` is "Run 14, PASS" against Revision 14. The
   reviewer decides whether closure requires a **Run 15** re-audit against the
   amended set, or whether the bounded, mechanically-checked nature of the
   Revision-15 change (one new nullary constructor in each of two types, plus
   documentation) lets Run 14 stand with a recorded delta. Either way the
   decision is stated in the report.

7. **Archive of record.** The report names
   `unit1a_preclosure_compile_candidate_r4.zip` (sha256
   `d39db6c5392013a2ac6438e2bd82b74990985e3e5a2679e884cd841f4945139f`) as the
   implementation candidate that realises Revision 15, and this package
   (`phase0_closure_package_r1`, see its `MANIFEST.sha256`) as the closure
   input.

8. **Effect.** On issuance, Phase 0 is closed; Phase 1 may begin with the
   obligations in item 4. Phase 2 is not in scope and is not begun.
