From Ucos2Verify.VC.code.event Require Import event_task_rdy_goal event_task_rdy_proof_auto_checked event_task_rdy_proof_manual.

Module VC_Correctness : VC_Correct.
  Include event_task_rdy_proof_auto_checked.
  Include event_task_rdy_proof_manual.
End VC_Correctness.
