From Ucos2Verify.VC.code.sem Require Import pend_abort_goal pend_abort_proof_auto pend_abort_proof_manual.

Module VC_Correctness : VC_Correct.
  Include pend_abort_proof_auto.
  Include pend_abort_proof_manual.
End VC_Correctness.
