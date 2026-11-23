From Ucos2Verify.VC.code.queue Require Import q_query_goal q_query_proof_auto q_query_proof_manual.

Module VC_Correctness : VC_Correct.
  Include q_query_proof_auto.
  Include q_query_proof_manual.
End VC_Correctness.
