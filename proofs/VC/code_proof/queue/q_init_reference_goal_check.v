From Ucos2Verify.VC.code.queue Require Import q_init_reference_goal q_init_reference_proof_auto q_init_reference_proof_manual.

Module VC_Correctness : VC_Correct.
  Include q_init_reference_proof_auto.
  Include q_init_reference_proof_manual.
End VC_Correctness.
