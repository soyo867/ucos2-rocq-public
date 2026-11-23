From Ucos2Verify.VC.code.mutex Require Import accept_return_goal accept_return_proof_auto_checked accept_return_proof_manual.

Module VC_Correctness : VC_Correct.
  Include accept_return_proof_auto_checked.
  Include accept_return_proof_manual.
End VC_Correctness.
