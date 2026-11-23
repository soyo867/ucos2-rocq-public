From Ucos2Verify.VC.code.sem Require Import query_goal query_proof_auto query_proof_manual.

Module VC_Correctness : VC_Correct.
  Include query_proof_auto.
  Include query_proof_manual.
End VC_Correctness.
