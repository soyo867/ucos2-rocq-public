From Ucos2Verify.VC.code.mutex Require Import query_return_goal query_return_proof_auto_checked query_return_proof_manual.

Module VC_Correctness : VC_Correct.
  Include query_return_proof_auto_checked.
  Include query_return_proof_manual.
End VC_Correctness.
