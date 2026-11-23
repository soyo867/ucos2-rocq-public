From Ucos2Verify.VC.code.sched Require Import tmr_task_unlock_entry_goal tmr_task_unlock_entry_proof_auto tmr_task_unlock_entry_proof_manual.

Module VC_Correctness : VC_Correct.
  Include tmr_task_unlock_entry_proof_auto.
  Include tmr_task_unlock_entry_proof_manual.
End VC_Correctness.
