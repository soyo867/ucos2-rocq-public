From Ucos2Verify.VC.code.timer Require Import tmr_link_goal tmr_link_proof_auto tmr_link_proof_manual.

Module VC_Correctness : VC_Correct.
  Include tmr_link_proof_auto.
  Include tmr_link_proof_manual.
End VC_Correctness.
