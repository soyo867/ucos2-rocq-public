From Ucos2Verify.VC.code.core Require Import OS_StrLen_goal OS_StrLen_proof_auto OS_StrLen_proof_manual.

Module VC_Correctness : VC_Correct.
  Include OS_StrLen_proof_auto.
  Include OS_StrLen_proof_manual.
End VC_Correctness.
