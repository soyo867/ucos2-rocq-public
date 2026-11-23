From Ucos2Verify.VC.code.task Require Import tcb_init_hook_goal tcb_init_hook_proof_auto tcb_init_hook_proof_manual.

Module VC_Correctness : VC_Correct.
  Include tcb_init_hook_proof_auto.
  Include tcb_init_hook_proof_manual.
End VC_Correctness.
