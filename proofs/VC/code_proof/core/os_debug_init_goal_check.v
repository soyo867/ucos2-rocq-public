From Ucos2Verify.VC.code.core Require Import os_debug_init_goal os_debug_init_proof_auto os_debug_init_proof_manual.

Module VC_Correctness : VC_Correct.
  Include os_debug_init_proof_auto.
  Include os_debug_init_proof_manual.
End VC_Correctness.
