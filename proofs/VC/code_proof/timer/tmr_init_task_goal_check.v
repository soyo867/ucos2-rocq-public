From Ucos2Verify.VC.code.timer Require Import tmr_init_task_goal tmr_init_task_proof_auto tmr_init_task_proof_manual.

Module VC_Correctness : VC_Correct.
  Include tmr_init_task_proof_auto.
  Include tmr_init_task_proof_manual.
End VC_Correctness.
