From Ucos2Verify.VC.code.sched Require Import mutex_pend_sched_goal mutex_pend_sched_proof_auto mutex_pend_sched_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mutex_pend_sched_proof_auto.
  Include mutex_pend_sched_proof_manual.
End VC_Correctness.
