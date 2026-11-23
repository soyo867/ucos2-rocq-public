From Ucos2Verify.VC.code.queue Require Import q_del_goal q_del_proof_auto q_del_proof_manual.

Module VC_Correctness : VC_Correct.
  Include q_del_proof_auto.
  Include q_del_proof_manual.
End VC_Correctness.
