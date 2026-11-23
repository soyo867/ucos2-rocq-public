From Ucos2Verify.VC.code.core Require Import os_init_goal os_init_proof_auto os_init_proof_manual.

Module VC_Correctness : VC_Correct.
  Include os_init_proof_auto.
  Include os_init_proof_manual.
End VC_Correctness.
