From Ucos2Verify.VC.code.core Require Import task_idle_goal task_idle_proof_auto task_idle_proof_manual.

Module VC_Correctness : VC_Correct.
  Include task_idle_proof_auto.
  Include task_idle_proof_manual.
End VC_Correctness.
