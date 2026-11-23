From Ucos2Verify.VC.code.mbox Require Import mbox_query_goal mbox_query_proof_auto mbox_query_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mbox_query_proof_auto.
  Include mbox_query_proof_manual.
End VC_Correctness.
