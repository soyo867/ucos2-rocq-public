From Ucos2Verify.VC.code.queue Require Import q_flush_source_goal q_flush_source_proof_auto q_flush_source_proof_manual.

Module VC_Correctness : VC_Correct.
  Include q_flush_source_proof_auto.
  Include q_flush_source_proof_manual.
End VC_Correctness.
