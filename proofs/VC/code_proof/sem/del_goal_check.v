From Ucos2Verify.VC.code.sem Require Import del_goal del_proof_auto del_proof_manual.

Module VC_Correctness : VC_Correct.
  Include del_proof_auto.
  Include del_proof_manual.
End VC_Correctness.
