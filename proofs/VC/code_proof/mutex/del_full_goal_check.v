From Ucos2Verify.VC.code.mutex Require Import del_full_goal del_full_proof_auto del_full_proof_manual.

Module VC_Correctness : VC_Correct.
  Include del_full_proof_auto.
  Include del_full_proof_manual.
End VC_Correctness.
