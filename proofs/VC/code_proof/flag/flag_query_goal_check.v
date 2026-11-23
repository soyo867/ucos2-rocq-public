From Ucos2Verify.VC.code.flag Require Import flag_query_goal flag_query_proof_auto flag_query_proof_manual.

Module VC_Correctness : VC_Correct.
  Include flag_query_proof_auto.
  Include flag_query_proof_manual.
End VC_Correctness.
