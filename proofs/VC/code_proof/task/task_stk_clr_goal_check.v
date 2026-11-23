From Ucos2Verify.VC.code.task Require Import task_stk_clr_goal task_stk_clr_proof_auto task_stk_clr_proof_manual.

Module VC_Correctness : VC_Correct.
  Include task_stk_clr_proof_auto.
  Include task_stk_clr_proof_manual.
End VC_Correctness.
