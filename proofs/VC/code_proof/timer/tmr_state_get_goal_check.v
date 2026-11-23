From Ucos2Verify.VC.code.timer Require Import tmr_state_get_goal tmr_state_get_proof_auto tmr_state_get_proof_manual.

Module VC_Correctness : VC_Correct.
  Include tmr_state_get_proof_auto.
  Include tmr_state_get_proof_manual.
End VC_Correctness.
