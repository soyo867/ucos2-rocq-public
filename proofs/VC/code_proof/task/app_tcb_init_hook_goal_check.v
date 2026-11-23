From Ucos2Verify.VC.code.task Require Import app_tcb_init_hook_goal app_tcb_init_hook_proof_auto app_tcb_init_hook_proof_manual.

Module VC_Correctness : VC_Correct.
  Include app_tcb_init_hook_proof_auto.
  Include app_tcb_init_hook_proof_manual.
End VC_Correctness.
