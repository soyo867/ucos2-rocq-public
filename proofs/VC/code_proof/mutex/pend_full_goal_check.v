From Ucos2Verify.VC.code.mutex Require Import pend_full_goal pend_full_proof_auto pend_full_proof_manual.

Module VC_Correctness : VC_Correct.
  Include pend_full_proof_auto.
  Include pend_full_proof_manual.
End VC_Correctness.
