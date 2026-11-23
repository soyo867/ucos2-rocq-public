From Ucos2Verify.VC.code.flag Require Import flag_init_goal flag_init_proof_auto flag_init_proof_manual.

Module VC_Correctness : VC_Correct.
  Include flag_init_proof_auto.
  Include flag_init_proof_manual.
End VC_Correctness.
