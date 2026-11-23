From Ucos2Verify.VC.code.queue Require Import q_post_opt_goal q_post_opt_proof_auto q_post_opt_proof_manual.

Module VC_Correctness : VC_Correct.
  Include q_post_opt_proof_auto.
  Include q_post_opt_proof_manual.
End VC_Correctness.
