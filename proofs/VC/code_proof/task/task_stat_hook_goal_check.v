From Ucos2Verify.VC.code.task Require Import task_stat_hook_goal task_stat_hook_proof_auto task_stat_hook_proof_manual.

Module VC_Correctness : VC_Correct.
  Include task_stat_hook_proof_auto.
  Include task_stat_hook_proof_manual.
End VC_Correctness.
