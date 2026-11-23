From Ucos2Verify.VC.code.queue Require Import q_create_goal q_create_proof_auto q_create_proof_manual.

Module VC_Correctness : VC_Correct.
  Include q_create_proof_auto.
  Include q_create_proof_manual.
End VC_Correctness.
