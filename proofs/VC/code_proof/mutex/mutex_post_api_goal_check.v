From Ucos2Verify.VC.code.mutex Require Import mutex_post_api_goal mutex_post_api_proof_auto_checked mutex_post_api_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mutex_post_api_proof_auto_checked.
  Include mutex_post_api_proof_manual.
End VC_Correctness.
