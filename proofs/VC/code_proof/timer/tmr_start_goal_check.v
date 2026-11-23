From Ucos2Verify.VC.code.timer Require Import tmr_start_goal tmr_start_proof_auto tmr_start_proof_manual.

Module VC_Correctness : VC_Correct.
  Include tmr_start_proof_auto.
  Include tmr_start_proof_manual.
End VC_Correctness.
