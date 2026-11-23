From Ucos2Verify.VC.code.sched Require Import sched_new_full_goal sched_new_full_proof_auto_checked sched_new_full_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sched_new_full_proof_auto_checked.
  Include sched_new_full_proof_manual.
End VC_Correctness.
