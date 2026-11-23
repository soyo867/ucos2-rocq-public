From Ucos2Verify.VC.code.timer Require Import tmr_stop_goal tmr_stop_proof_auto tmr_stop_proof_manual.

Module VC_Correctness : VC_Correct.
  Include tmr_stop_proof_auto.
  Include tmr_stop_proof_manual.
End VC_Correctness.
