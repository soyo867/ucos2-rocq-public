From Ucos2Verify.VC.code.core Require Import os_version_goal os_version_proof_auto os_version_proof_manual.

Module VC_Correctness : VC_Correct.
  Include os_version_proof_auto.
  Include os_version_proof_manual.
End VC_Correctness.
