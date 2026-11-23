(** Integration entry for the functions that consume the shared
    Save/Restore and resumption interface.  Each imported goal_check checks
    its complete canonical obligation interface against the actual auto and
    manual modules.  This entry adds no specification or proof assumptions. *)
Require Import Ucos2Verify.VC.code.sched.sched_lock_call_goal_check.
Require Import Ucos2Verify.VC.code.sched.sched_unlock_call_goal_check.
Require Import Ucos2Verify.VC.code.sched.sched_goal_check.
Require Import Ucos2Verify.VC.code.interrupt.int_exit_goal_check.
Require Import Ucos2Verify.VC.code.task.task_tcb_init_goal_check.
Require Import Ucos2Verify.VC.code.timer.tmr_del_goal_check.
Require Import Ucos2Verify.VC.code.core.spec.kernel_client_resumption.
