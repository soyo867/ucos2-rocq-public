From Ucos2Verify.VC.code.sched Require Import sem_sched_continuation_goal sem_sched_continuation_proof_auto sem_sched_continuation_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sem_sched_continuation_proof_auto.
  Include sem_sched_continuation_proof_manual.
End VC_Correctness.
