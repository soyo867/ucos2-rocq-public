From Ucos2Verify.VC.code.core Require Import init_task_idle_goal init_task_idle_proof_auto init_task_idle_proof_manual.

Module VC_Correctness : VC_Correct.
  Include init_task_idle_proof_auto.
  Include init_task_idle_proof_manual.
End VC_Correctness.
