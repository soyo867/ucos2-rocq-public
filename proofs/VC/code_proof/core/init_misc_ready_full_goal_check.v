From Ucos2Verify.VC.code.core Require Import init_misc_ready_full_goal init_misc_ready_full_proof_auto init_misc_ready_full_proof_manual.

Module VC_Correctness : VC_Correct.
  Include init_misc_ready_full_proof_auto.
  Include init_misc_ready_full_proof_manual.
End VC_Correctness.
