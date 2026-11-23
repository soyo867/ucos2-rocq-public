From Ucos2Verify.VC.code.core Require Import os_dummy_goal os_dummy_proof_auto os_dummy_proof_manual.

Module VC_Correctness : VC_Correct.
  Include os_dummy_proof_auto.
  Include os_dummy_proof_manual.
End VC_Correctness.
