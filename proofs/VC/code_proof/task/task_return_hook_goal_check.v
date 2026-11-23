From Ucos2Verify.VC.code.task Require Import task_return_hook_goal task_return_hook_proof_auto task_return_hook_proof_manual.

Module VC_Correctness : VC_Correct.
  Include task_return_hook_proof_auto.
  Include task_return_hook_proof_manual.
End VC_Correctness.
