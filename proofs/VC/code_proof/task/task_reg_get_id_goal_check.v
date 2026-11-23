From Ucos2Verify.VC.code.task Require Import task_reg_get_id_goal task_reg_get_id_proof_auto task_reg_get_id_proof_manual.

Module VC_Correctness : VC_Correct.
  Include task_reg_get_id_proof_auto.
  Include task_reg_get_id_proof_manual.
End VC_Correctness.
