From Ucos2Verify.VC.code.sem Require Import pend_goal pend_proof_auto pend_proof_manual.

Module VC_Correctness : VC_Correct.
  Include pend_proof_auto.
  Include pend_proof_manual.
End VC_Correctness.
