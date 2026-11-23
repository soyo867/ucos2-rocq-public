From Ucos2Verify.VC.code.interrupt Require Import os_init_hook_end_goal os_init_hook_end_proof_auto os_init_hook_end_proof_manual.

Module VC_Correctness : VC_Correct.
  Include os_init_hook_end_proof_auto.
  Include os_init_hook_end_proof_manual.
End VC_Correctness.
