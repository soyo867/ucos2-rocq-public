From Ucos2Verify.VC.code.sched Require Import sched_fields_active_goal sched_fields_active_proof_auto sched_fields_active_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sched_fields_active_proof_auto.
  Include sched_fields_active_proof_manual.
End VC_Correctness.
