From Ucos2Verify.VC.code.mbox Require Import mbox_pend_goal mbox_pend_proof_auto mbox_pend_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mbox_pend_proof_auto.
  Include mbox_pend_proof_manual.
End VC_Correctness.
