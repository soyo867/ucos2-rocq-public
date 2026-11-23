From Ucos2Verify.VC.code.timer Require Import tmr_del_goal tmr_del_proof_auto tmr_del_proof_manual.

Module VC_Correctness : VC_Correct.
  Include tmr_del_proof_auto.
  Include tmr_del_proof_manual.
End VC_Correctness.
