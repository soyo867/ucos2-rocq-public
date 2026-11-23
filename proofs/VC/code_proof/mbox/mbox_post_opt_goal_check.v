From Ucos2Verify.VC.code.mbox Require Import mbox_post_opt_goal mbox_post_opt_proof_auto mbox_post_opt_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mbox_post_opt_proof_auto.
  Include mbox_post_opt_proof_manual.
End VC_Correctness.
