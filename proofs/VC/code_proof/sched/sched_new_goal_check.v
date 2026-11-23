From Ucos2Verify.VC.code.sched Require Import sched_new_goal sched_new_proof_auto sched_new_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sched_new_proof_auto.
  Include sched_new_proof_manual.
End VC_Correctness.
