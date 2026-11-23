From Ucos2Verify.VC.code.sched Require Import sched_goal sched_proof_auto_checked sched_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sched_proof_auto_checked.
  Include sched_proof_manual.
End VC_Correctness.
