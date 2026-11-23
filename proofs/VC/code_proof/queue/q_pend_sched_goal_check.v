From Ucos2Verify.VC.code.queue Require Import q_pend_sched_goal q_pend_sched_proof_auto q_pend_sched_proof_manual.

Module VC_Correctness : VC_Correct.
  Include q_pend_sched_proof_auto.
  Include q_pend_sched_proof_manual.
End VC_Correctness.
