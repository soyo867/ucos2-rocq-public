From Ucos2Verify.VC.code.mutex Require Import post_full_goal post_full_proof_auto post_full_proof_manual.

Module VC_Correctness : VC_Correct.
  Include post_full_proof_auto.
  Include post_full_proof_manual.
End VC_Correctness.
