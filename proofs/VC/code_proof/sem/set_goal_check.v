From Ucos2Verify.VC.code.sem Require Import set_goal set_proof_auto set_proof_manual.

Module VC_Correctness : VC_Correct.
  Include set_proof_auto.
  Include set_proof_manual.
End VC_Correctness.
