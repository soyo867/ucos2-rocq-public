From Ucos2Verify.VC.code.timer Require Import tmr_free_goal tmr_free_proof_auto tmr_free_proof_manual.

Module VC_Correctness : VC_Correct.
  Include tmr_free_proof_auto.
  Include tmr_free_proof_manual.
End VC_Correctness.
