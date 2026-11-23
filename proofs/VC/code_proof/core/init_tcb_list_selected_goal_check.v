From Ucos2Verify.VC.code.core Require Import init_tcb_list_selected_goal init_tcb_list_selected_proof_auto init_tcb_list_selected_proof_manual.

Module VC_Correctness : VC_Correct.
  Include init_tcb_list_selected_proof_auto.
  Include init_tcb_list_selected_proof_manual.
End VC_Correctness.
