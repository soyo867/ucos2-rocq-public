From Ucos2Verify.VC.code.queue Require Import q_accept_goal q_accept_proof_auto q_accept_proof_manual.

Module VC_Correctness : VC_Correct.
  Include q_accept_proof_auto.
  Include q_accept_proof_manual.
End VC_Correctness.
