From Ucos2Verify.VC.code.mbox Require Import mbox_del_goal mbox_del_proof_auto mbox_del_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mbox_del_proof_auto.
  Include mbox_del_proof_manual.
End VC_Correctness.
