From Ucos2Verify.VC.code.flag Require Import flag_create_goal flag_create_proof_auto flag_create_proof_manual.

Module VC_Correctness : VC_Correct.
  Include flag_create_proof_auto.
  Include flag_create_proof_manual.
End VC_Correctness.
