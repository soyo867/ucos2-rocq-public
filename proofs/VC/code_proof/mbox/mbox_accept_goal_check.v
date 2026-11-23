From Ucos2Verify.VC.code.mbox Require Import mbox_accept_goal mbox_accept_proof_auto mbox_accept_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mbox_accept_proof_auto.
  Include mbox_accept_proof_manual.
End VC_Correctness.
