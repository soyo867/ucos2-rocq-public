From Ucos2Verify.VC.code.sched Require Import sem_client_sched_goal sem_client_sched_proof_auto sem_client_sched_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sem_client_sched_proof_auto.
  Include sem_client_sched_proof_manual.
End VC_Correctness.
