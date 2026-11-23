From Ucos2Verify.VC.code.timer Require Import tmr_create_goal tmr_create_proof_auto tmr_create_proof_manual.

Module VC_Correctness : VC_Correct.
  Include tmr_create_proof_auto.
  Include tmr_create_proof_manual.
End VC_Correctness.
