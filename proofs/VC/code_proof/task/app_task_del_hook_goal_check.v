From Ucos2Verify.VC.code.task Require Import app_task_del_hook_goal app_task_del_hook_proof_auto app_task_del_hook_proof_manual.

Module VC_Correctness : VC_Correct.
  Include app_task_del_hook_proof_auto.
  Include app_task_del_hook_proof_manual.
End VC_Correctness.
