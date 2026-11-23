From Ucos2Verify.VC.code.memory Require Import mem_query_goal mem_query_proof_auto mem_query_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mem_query_proof_auto.
  Include mem_query_proof_manual.
End VC_Correctness.
