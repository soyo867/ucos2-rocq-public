From Ucos2Verify.VC.code.timer Require Import tmr_name_get_goal tmr_name_get_proof_auto tmr_name_get_proof_manual.

Module VC_Correctness : VC_Correct.
  Include tmr_name_get_proof_auto.
  Include tmr_name_get_proof_manual.
End VC_Correctness.
