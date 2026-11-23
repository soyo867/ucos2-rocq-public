From Ucos2Verify.VC.code.task Require Import task_query_goal task_query_proof_auto task_query_proof_manual.

Module VC_Correctness : VC_Correct.
  Include task_query_proof_auto.
  Include task_query_proof_manual.
End VC_Correctness.
