From Ucos2Verify.VC.code.mbox Require Import mbox_create_goal mbox_create_proof_auto mbox_create_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mbox_create_proof_auto.
  Include mbox_create_proof_manual.
End VC_Correctness.
