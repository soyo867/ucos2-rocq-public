From Ucos2Verify.VC.code.core Require Import stat_init_goal stat_init_proof_auto stat_init_proof_manual.

Module VC_Correctness : VC_Correct.
  Include stat_init_proof_auto.
  Include stat_init_proof_manual.
End VC_Correctness.
