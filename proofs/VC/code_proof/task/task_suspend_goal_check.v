From Ucos2Verify.VC.code.task Require Import task_suspend_goal task_suspend_proof_auto task_suspend_proof_manual.

Module VC_Correctness : VC_Correct.
  Include task_suspend_proof_auto.
  Include task_suspend_proof_manual.
End VC_Correctness.
