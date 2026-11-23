From Ucos2Verify.VC.code.mutex Require Import mutex_priority_goal mutex_priority_proof_auto mutex_priority_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mutex_priority_proof_auto.
  Include mutex_priority_proof_manual.
End VC_Correctness.
