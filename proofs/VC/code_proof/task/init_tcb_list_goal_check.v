From Ucos2Verify.VC.code.task Require Import init_tcb_list_goal init_tcb_list_proof_auto init_tcb_list_proof_manual.

Module VC_Correctness : VC_Correct.
  Include init_tcb_list_proof_auto.
  Include init_tcb_list_proof_manual.
End VC_Correctness.
