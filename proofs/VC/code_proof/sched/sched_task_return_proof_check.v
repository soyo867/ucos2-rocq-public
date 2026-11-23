(** Complete current VC interface instance; prepared, not yet checked. *)
Require Import Ucos2Verify.VC.code.sched.sched_task_return_goal.
Require Import Ucos2Verify.VC.code.sched.sched_task_return_proof_auto.
Require Import Ucos2Verify.VC.code.sched.sched_task_return_proof_manual.

Module VC_Correctness <: Ucos2Verify.VC.code.sched.sched_task_return_goal.VC_Correct.
  Include Ucos2Verify.VC.code.sched.sched_task_return_proof_auto.
  Include Ucos2Verify.VC.code.sched.sched_task_return_proof_manual.
End VC_Correctness.
