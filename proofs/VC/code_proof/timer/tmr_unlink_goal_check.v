From Ucos2Verify.VC.code.timer Require Import tmr_unlink_goal tmr_unlink_proof_auto tmr_unlink_proof_manual.

Module VC_Correctness : VC_Correct.
  Include tmr_unlink_proof_auto.
  Include tmr_unlink_proof_manual.
End VC_Correctness.
