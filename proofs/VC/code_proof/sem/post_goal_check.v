From Ucos2Verify.VC.code.sem Require Import post_goal post_proof_auto post_proof_manual.

Module VC_Correctness : VC_Correct.
  Include post_proof_auto.
  Include post_proof_manual.
End VC_Correctness.
