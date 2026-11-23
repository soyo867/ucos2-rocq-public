From Ucos2Verify.VC.code.event Require Import event_task_remove_multi_goal event_task_remove_multi_proof_auto event_task_remove_multi_proof_manual.

Module VC_Correctness : VC_Correct.
  Include event_task_remove_multi_proof_auto.
  Include event_task_remove_multi_proof_manual.
End VC_Correctness.
