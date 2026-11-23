(** Regression entry for shared model changes.  These imports compile the
    model proofs and the complete obligation interfaces of the affected
    existing clients; they do not prove all kernel APIs or discharge the
    fixed QCP/architecture trust boundary. *)
Require Import Ucos2Verify.VC.code.core.kernel_state_machine_check.
Require Import Ucos2Verify.VC.code.core.critical_region_clients_check.
Require Import Ucos2Verify.VC.code.timer.tmr_alloc_goal_check.
Require Import Ucos2Verify.VC.code.timer.tmr_free_goal_check.
Require Import Ucos2Verify.VC.code.timer.tmr_link_goal_check.
Require Import Ucos2Verify.VC.code.timer.tmr_unlink_goal_check.
Require Import Ucos2Verify.VC.code.core.kernel_borrowing_check.
Require Import Ucos2Verify.lib.statistics_execution.
Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_start_stack_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.tick.time_tick_goal_check.
Require Import Ucos2Verify.VC.code.tick.time_tick_complement_goal_check.
