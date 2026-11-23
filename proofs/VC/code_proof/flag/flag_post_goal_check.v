From Ucos2Verify.VC.code.flag Require Import flag_post_goal flag_post_proof_auto flag_post_proof_manual.

Module VC_Correctness : VC_Correct.
  Include flag_post_proof_auto.
  Include flag_post_proof_manual.
End VC_Correctness.
