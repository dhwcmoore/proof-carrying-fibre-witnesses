From PCFW Require Import Orchestration.

(* Repaired (REP1) and its supporting results are now axiom-free:
   each of the next three must print "Closed under the global context". *)
Print Assumptions REP1_not_run_has_no_witness.
Print Assumptions REP1_replay_not_run_has_no_witness.
Print Assumptions replay_stage2_wf.

(* The five formerly-Admitted orchestration obligations, now proved
   (PHASE_1_ORCHESTRATION_PROOFS.md); each must also print
   "Closed under the global context". *)
Print Assumptions T2_sound.
Print Assumptions T2_complete.
Print Assumptions stage1_over_is_terminal.
Print Assumptions exact_unreachable_v0.
Print Assumptions validation_fuel_obstructed_unreachable_when_sufficient.
