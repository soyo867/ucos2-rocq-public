Require Import Ucos2Verify.VC.code.interrupt.int_exit_goal.
Require Import Ucos2Verify.VC.code.interrupt.int_exit_goal_check.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_api_completion_spec.

(** The current C interface proves the OSIntCtxSw call precondition and the
    ordinary returns. Its nonlocal completion consumes the original platform
    output at the same call, then delivers the same public continuation. *)
Module OSIntExitAPI.
  Include int_exit_goal_check.VC_Correctness.
  Include int_exit_api_completion_spec.
End OSIntExitAPI.

Module OSIntExitCInterface : VC_Correct := OSIntExitAPI.
