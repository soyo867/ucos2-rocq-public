From Ucos2Verify.VC.code.mutex Require Import mutex_post_native_goal mutex_post_native_proof_auto mutex_post_native_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mutex_post_native_proof_auto.
  Include mutex_post_native_proof_manual.
End VC_Correctness.
