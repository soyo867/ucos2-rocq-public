From Ucos2Verify.VC.code.sem Require Import accept_goal accept_proof_auto accept_proof_manual.

Module VC_Correctness : VC_Correct.
  Include accept_proof_auto.
  Include accept_proof_manual.
End VC_Correctness.
