From Ucos2Verify.VC.code.interrupt Require Import int_enter_api_goal int_enter_api_proof_auto int_enter_api_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_enter_api_proof_auto.
  Include int_enter_api_proof_manual.
End VC_Correctness.
