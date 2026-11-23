From Ucos2Verify.VC.code.core Require Import os_start_goal os_start_proof_auto os_start_proof_manual.

Module VC_Correctness : VC_Correct.
  Include os_start_proof_auto.
  Include os_start_proof_manual.
End VC_Correctness.
