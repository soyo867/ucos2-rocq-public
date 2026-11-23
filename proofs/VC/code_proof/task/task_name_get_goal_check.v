From Ucos2Verify.VC.code.task Require Import task_name_get_goal task_name_get_proof_auto task_name_get_proof_manual.

Module VC_Correctness : VC_Correct.
  Include task_name_get_proof_auto.
  Include task_name_get_proof_manual.
End VC_Correctness.
