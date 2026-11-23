From Ucos2Verify.VC.code.timer Require Import tmr_signal_goal tmr_signal_proof_auto tmr_signal_proof_manual.

Module VC_Correctness : VC_Correct.
  Include tmr_signal_proof_auto.
  Include tmr_signal_proof_manual.
End VC_Correctness.
