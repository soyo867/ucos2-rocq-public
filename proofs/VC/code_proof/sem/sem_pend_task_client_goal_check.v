From Ucos2Verify.VC.code.sem Require Import sem_pend_task_client_goal sem_pend_task_client_proof_auto sem_pend_task_client_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sem_pend_task_client_proof_auto.
  Include sem_pend_task_client_proof_manual.
End VC_Correctness.
