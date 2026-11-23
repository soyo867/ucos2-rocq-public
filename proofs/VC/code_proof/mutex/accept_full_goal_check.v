From Ucos2Verify.VC.code.mutex Require Import accept_full_goal accept_full_proof_auto accept_full_proof_manual.

Module VC_Correctness : VC_Correct.
  Include accept_full_proof_auto.
  Include accept_full_proof_manual.
End VC_Correctness.
