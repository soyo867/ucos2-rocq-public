#ifndef TMR_TASK_VERIFICATION_H
#define TMR_TASK_VERIFICATION_H

/* Pinned V2.93.01 / ILP32 declaration recipe. Insert common annotations
 * after original types/globals and replace the five original prototype
 * sites with the declarations below. The single-function input is
 * task-client-input-candidate/uC-OS2_verify/annotated_C/src/timer/OSTmr_Task.c.
 * No C typedef or ABI changes.
 * Scheduler wrappers are exact lifts of scheduler-fields-candidate.
 * Pend wrappers lift the Task-specific client contract. Its ordered
 * C-address guard uses the actual object layout and global field addresses.
 */
#include "verification_stdlib.h"
/*@ Import Coq From SimpleC.CoreLang Require Import CTypes */
/*@ Import Coq Import SimpleCtypeNotations */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.timer_callback_semantics */
/*@ Import Coq Import TimerCallback_C_Rules */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_call_adapter_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_witness_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_iteration_entry_spec */
/*@ Import Coq Require Import Ucos2Verify.lib.event */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_verify_inv */
/*@ Import Coq Require Import Ucos2Verify.VC.code.task.spec.task_sw_hook_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_source_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_fields_resource_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_fields_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_return_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_pend_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_pend_adapter_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_call_layout_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_progress_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_callback_registry_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_scan_unlock_entry_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_clear_status_pend_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_callback_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_iteration_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_entry_return_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_unlock_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_vc_spec */
/*@ Import Coq Import TimerCallback_C_Rules TimerCallback_C_Rules.Rules */
/*@ Import Coq Local Open Scope Z_scope */
/*@ Import Coq Local Open Scope sac */
/*@ Extern Coq EventID := Z */
/*@ Extern Coq
    (StableGlobVars :: *) (UCOS2_Verify_State :: *) (GlobTimerState :: *)
    (OSEventAbstractState :: *) (TimerImage :: *) (TimerScanState :: *)
    (InterruptPlatformResources :: *) (CriticalRegionResources :: *)
    (OsSchedExternalResources :: *) (OsSchedCallContext :: *)
    (TaskStackCallEnvironment :: *) (Armv7aContinuation :: *) (TmrTaskLegacyAssertion :: *)
    (tmr_task_scan_world :: * => *) (TmrTaskEffects :: * => *)
    (TmrTaskContinuationHistory :: * => *) (TmrTaskIterationObservation :: *)
    (tmr_task_scan_event :: *) (TmrTaskCellKind :: *) (TmrTaskImageField :: *)
    (nat :: *) (unit :: *) (prod :: * => * => *)
    (list :: * => *) (option :: * => *) (program :: * => * => *) */
/*@ Extern Coq (UCOS2_state_inv : StableGlobVars -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq
    (tt : unit) (nil : {A} -> list A) (cons : {A} -> A -> list A -> list A)
    (app : {A} -> list A -> list A -> list A)
    (Some : {A} -> A -> option A)
    (pair : {A} {B} -> A -> B -> prod A B) (Z_of_nat : nat -> Z)
    (TaskNextField : TmrTaskImageField) (TaskMatchField : TmrTaskImageField)
    (TaskOptionField : TmrTaskImageField) (TaskCallbackField : TmrTaskImageField)
    (TaskArgumentField : TmrTaskImageField) (TaskStateField : TmrTaskImageField) */
/*@ Printing Coq Name program := StateRelMonad.M */
/*@ Printing Strategy Name program := StateRelMonad.M */
/*@ Printing Coq Name Z_of_nat := Z.of_nat */

/*@ Extern Coq
    (tmr_task_kernel : {A} -> tmr_task_scan_world A -> UCOS2_Verify_State)
    (tmr_task_application : {A} -> tmr_task_scan_world A -> A)
    (tmr_task_timers : {A} -> tmr_task_scan_world A -> GlobTimerState)
    (timerTime : GlobTimerState -> Z) (timerSignalSem : GlobTimerState -> Z)
    (timer_api_initialized : GlobTimerState -> Prop)
    (valid_timer_state : StableGlobVars -> GlobTimerState -> Prop)
    (timer_pool_addr : StableGlobVars -> Z -> Z)
    (timer_scan_next_pointer : StableGlobVars -> TimerScanState -> Z)
    (timerScanRemaining : TimerScanState -> list Z)
    (timer_scan_advance : GlobTimerState -> TimerScanState -> option TimerScanState)
    (tmr_task_head : StableGlobVars -> nat -> GlobTimerState -> Z)
    (tmr_task_spoke_in_range : StableGlobVars -> nat -> Prop)
    (tmr_unlink_running : GlobTimerState -> Z -> Prop)
    (tmr_link_eligible : GlobTimerState -> Z -> Prop)
    (tmr_task_profile : StableGlobVars -> Prop)
    (event_table_layout_prop : StableGlobVars -> Prop)
    (task_stack_call_external : TaskStackCallEnvironment -> OsSchedExternalResources)
    (tmr_task_registered_source_coverage : OsSchedExternalResources -> CriticalRegionResources -> Prop)
    (task_sw_hook_source_binding : OsSchedExternalResources -> Prop)
    (tmr_task_signal_lifetime : CriticalRegionResources -> StableGlobVars -> nat -> UCOS2_Verify_State -> Prop)
    (tmr_task_callback_signal_lifetime : {A} -> StableGlobVars -> (prod (prod Z Z) Z -> OsSchedCallContext -> program (tmr_task_scan_world A) OsSchedCallContext) -> Prop)
    (tmr_task_fields_iteration_entry : CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> UCOS2_Verify_State -> Prop)
    (tmr_create_c_bindings : StableGlobVars -> Prop)
    (tmr_task_global_addresses : StableGlobVars -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
    (tmr_task_framed_effects : {A} -> (prod (prod Z Z) Z -> OsSchedCallContext -> program (tmr_task_scan_world A) OsSchedCallContext) -> TmrTaskEffects A)
    (tmr_task_fields_index_valid : StableGlobVars -> Z -> Prop)
    (tmr_task_fields_image_at : {A} -> tmr_task_scan_world A -> Z -> TimerImage -> Prop)
    (tmr_task_image_value : TmrTaskImageField -> TimerImage -> Z)
    (tmr_task_image_read : {A} -> tmr_task_scan_world A -> Z -> TmrTaskImageField -> Z -> Prop)
    (tmr_task_unlink_world : {A} -> StableGlobVars -> tmr_task_scan_world A -> Z -> tmr_task_scan_world A -> Prop)
    (tmr_task_link_world : {A} -> StableGlobVars -> tmr_task_scan_world A -> Z -> tmr_task_scan_world A -> Prop)
    (tmr_task_complete_world : {A} -> tmr_task_scan_world A -> Z -> tmr_task_scan_world A -> Prop)
    (tmr_task_dispatch_prepared : {A} -> StableGlobVars -> tmr_task_scan_world A -> Z -> Z -> tmr_task_scan_world A -> Prop)
    (tmr_task_scan_step : {A} -> StableGlobVars -> (prod (prod Z Z) Z -> OsSchedCallContext -> program (tmr_task_scan_world A) OsSchedCallContext) -> nat -> tmr_task_scan_world A -> OsSchedCallContext -> TimerScanState -> tmr_task_scan_event -> tmr_task_scan_world A -> OsSchedCallContext -> TimerScanState -> Prop)
*/
/*@ Extern Coq
    (tmr_task_client_loop_safe : {A} -> TaskStackCallEnvironment -> CriticalRegionResources -> StableGlobVars -> Z -> TmrTaskEffects A -> OsSchedCallContext -> list TmrTaskIterationObservation -> tmr_task_scan_world A -> (prod (list TmrTaskIterationObservation) OsSchedCallContext -> tmr_task_scan_world A -> Prop) -> Prop)
    (tmr_task_client_outer_facts : {A} -> TaskStackCallEnvironment -> CriticalRegionResources -> StableGlobVars -> Z -> TmrTaskEffects A -> OsSchedCallContext -> tmr_task_scan_world A -> OsSchedCallContext -> list TmrTaskIterationObservation -> tmr_task_scan_world A -> (prod (list TmrTaskIterationObservation) OsSchedCallContext -> tmr_task_scan_world A -> Prop) -> Prop)
    (tmr_task_client_history : {A} -> TaskStackCallEnvironment -> CriticalRegionResources -> StableGlobVars -> Z -> TmrTaskEffects A -> OsSchedCallContext -> tmr_task_scan_world A -> TmrTaskContinuationHistory A -> Prop)
    (tmr_task_client_scan_facts : {A} -> TaskStackCallEnvironment -> CriticalRegionResources -> StableGlobVars -> Z -> TmrTaskEffects A -> OsSchedCallContext -> tmr_task_scan_world A -> TmrTaskContinuationHistory A -> list tmr_task_scan_event -> OsSchedCallContext -> tmr_task_scan_world A -> TimerScanState -> (prod (list TmrTaskIterationObservation) OsSchedCallContext -> tmr_task_scan_world A -> Prop) -> Prop)
    (tmr_task_client_pend_program : {A} -> TaskStackCallEnvironment -> CriticalRegionResources -> StableGlobVars -> TmrTaskEffects A -> OsSchedCallContext -> Z -> tmr_task_scan_world A -> prod Z OsSchedCallContext -> tmr_task_scan_world A -> Prop)
    (tmr_task_continuation_unlock_program : {A} -> TaskStackCallEnvironment -> CriticalRegionResources -> StableGlobVars -> Z -> TmrTaskEffects A -> OsSchedCallContext -> tmr_task_scan_world A -> OsSchedCallContext -> tmr_task_scan_world A -> Prop)
    (tmr_task_continuation_before : {A} -> TmrTaskContinuationHistory A -> tmr_task_scan_world A)
    (tmr_task_continuation_context : {A} -> TmrTaskContinuationHistory A -> OsSchedCallContext)
    (tmr_task_continuation_completed : {A} -> TmrTaskContinuationHistory A -> list TmrTaskIterationObservation)
    (tmr_task_continuation_error : {A} -> TmrTaskContinuationHistory A -> Z)
    (tmr_task_continuation_waited : {A} -> TmrTaskContinuationHistory A -> tmr_task_scan_world A)
    (tmr_task_continuation_wait_context : {A} -> TmrTaskContinuationHistory A -> OsSchedCallContext)
    (tmr_task_continuation_locked : {A} -> TmrTaskContinuationHistory A -> tmr_task_scan_world A)
    (tmr_task_continuation_lock_context : {A} -> TmrTaskContinuationHistory A -> OsSchedCallContext)
    (tmr_task_continuation_start : {A} -> TmrTaskContinuationHistory A -> tmr_task_scan_world A)
    (tmr_task_continuation_spoke : {A} -> StableGlobVars -> TmrTaskContinuationHistory A -> nat)
    (tmr_task_continuation_scan : {A} -> StableGlobVars -> TmrTaskContinuationHistory A -> TimerScanState)
*/
/*@ Extern Coq
    (tmr_task_fields_base_owned : {A} -> (A -> Assertion) -> TaskStackCallEnvironment -> StableGlobVars -> Z -> OsSchedCallContext -> tmr_task_scan_world A -> Assertion)
    (tmr_task_fields_owned : {A} -> (A -> Assertion) -> TaskStackCallEnvironment -> StableGlobVars -> Z -> Z -> (Armv7aContinuation -> TmrTaskLegacyAssertion) -> OsSchedCallContext -> tmr_task_scan_world A -> Assertion)
    (tmr_task_current_fields_owned : {A} -> (A -> Assertion) -> TaskStackCallEnvironment -> StableGlobVars -> Z -> Z -> OsSchedCallContext -> tmr_task_scan_world A -> Assertion)
    (tmr_task_fields_client : {A} -> (A -> Assertion) -> Z -> tmr_task_scan_world A -> Assertion)
    (tmr_task_fields_time_rest : {A} -> (A -> Assertion) -> TaskStackCallEnvironment -> StableGlobVars -> Z -> Z -> OsSchedCallContext -> tmr_task_scan_world A -> Assertion)
    (tmr_task_fields_image_rest : {A} -> (A -> Assertion) -> TaskStackCallEnvironment -> StableGlobVars -> Z -> Z -> OsSchedCallContext -> tmr_task_scan_world A -> Z -> TimerImage -> TmrTaskImageField -> Assertion)
    (tmr_task_fields_match_rest : {A} -> (A -> Assertion) -> TaskStackCallEnvironment -> StableGlobVars -> Z -> Z -> OsSchedCallContext -> tmr_task_scan_world A -> Z -> TimerImage -> Assertion)
    (tmr_task_fields_head_rest : {A} -> (A -> Assertion) -> TaskStackCallEnvironment -> StableGlobVars -> Z -> Z -> OsSchedCallContext -> tmr_task_scan_world A -> nat -> Assertion)
    (tmr_task_fields_complete_rest : {A} -> (A -> Assertion) -> TaskStackCallEnvironment -> StableGlobVars -> Z -> Z -> OsSchedCallContext -> tmr_task_scan_world A -> Z -> TimerImage -> Assertion)
    (tmr_task_fields_unlink_rest : {A} -> (A -> Assertion) -> TaskStackCallEnvironment -> StableGlobVars -> Z -> Z -> (Armv7aContinuation -> TmrTaskLegacyAssertion) -> OsSchedCallContext -> tmr_task_scan_world A -> Z -> Z -> Z -> Z -> Z -> Z -> TmrTaskLegacyAssertion -> Assertion)
    (tmr_task_fields_link_rest : {A} -> (A -> Assertion) -> TaskStackCallEnvironment -> StableGlobVars -> Z -> Z -> (Armv7aContinuation -> TmrTaskLegacyAssertion) -> OsSchedCallContext -> tmr_task_scan_world A -> Z -> Z -> Z -> Z -> Z -> TmrTaskLegacyAssertion -> Assertion)
    (tmr_task_call_residual : Assertion)
*/
/*@ Extern Coq
    (os_sched_call_invocation : OsSchedCallContext -> nat)
    (sem_pend_call_input : CriticalRegionResources -> StableGlobVars -> nat -> Z -> UCOS2_Verify_State -> EventID -> OSEventAbstractState -> Prop)
    (sem_pend_runtime_nonblocking : CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> option TaskStackCallEnvironment -> Z -> UCOS2_Verify_State -> EventID -> Prop)
    (sem_pend_observed_admission : option TaskStackCallEnvironment -> CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> EventID -> Prop)
    (sem_pend_fields_call_domain : TaskStackCallEnvironment -> CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> EventID -> OSEventAbstractState -> Prop)
    (kernel_sched_ready_clients : CriticalRegionResources -> Prop)
    (kernel_tcb_stack_field_layout : StableGlobVars -> Prop)
    (tmr_task_fields_pend_blocking_layout : TaskStackCallEnvironment -> CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> EventID -> Prop)
    (tmr_task_client_pend_address_guard : StableGlobVars -> UCOS2_Verify_State -> Z -> EventID -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
    (os_sched_global_addresses : StableGlobVars -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
    (os_sched_lock_global_addresses : StableGlobVars -> Z -> Z -> Z -> Prop)
    (os_sched_unlock_global_addresses : StableGlobVars -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
    (tmr_task_legacy_any : Z -> (UCOS2_Verify_State -> Prop) -> Prop)
    (tmr_task_fields_kernel_any : OsSchedCallContext -> UCOS2_Verify_State -> Prop)
    (os_sched_lock_fields_return_sources : TaskStackCallEnvironment -> CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> OsSchedCallContext -> UCOS2_Verify_State -> Prop)
    (os_sched_unlock_fields_return_sources : TaskStackCallEnvironment -> CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> OsSchedCallContext -> UCOS2_Verify_State -> Prop)
    (tmr_task_fields_lock_pre : TaskStackCallEnvironment -> CriticalRegionResources -> (Armv7aContinuation -> TmrTaskLegacyAssertion) -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> (OsSchedCallContext -> UCOS2_Verify_State -> Prop) -> Assertion)
    (tmr_task_fields_lock_post : TaskStackCallEnvironment -> CriticalRegionResources -> (Armv7aContinuation -> TmrTaskLegacyAssertion) -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> (OsSchedCallContext -> UCOS2_Verify_State -> Prop) -> Assertion)
    (tmr_task_fields_unlock_pre : TaskStackCallEnvironment -> CriticalRegionResources -> (Armv7aContinuation -> TmrTaskLegacyAssertion) -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> (OsSchedCallContext -> UCOS2_Verify_State -> Prop) -> Assertion)
    (tmr_task_fields_unlock_post : TaskStackCallEnvironment -> CriticalRegionResources -> (Armv7aContinuation -> TmrTaskLegacyAssertion) -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> (OsSchedCallContext -> UCOS2_Verify_State -> Prop) -> Assertion)
    (tmr_task_fields_pend_pre : TaskStackCallEnvironment -> (Armv7aContinuation -> TmrTaskLegacyAssertion) -> CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> Z -> Z -> Z -> Z -> UCOS2_Verify_State -> EventID -> OSEventAbstractState -> (Z -> (UCOS2_Verify_State -> Prop) -> Prop) -> Assertion)
    (tmr_task_client_clear_status_pend_lifted_post : TaskStackCallEnvironment -> CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> Z -> Z -> Z -> Z -> UCOS2_Verify_State -> (Z -> (UCOS2_Verify_State -> Prop) -> Prop) -> Assertion)
    (tmr_task_client_clear_status_pend_argument_rest : TaskStackCallEnvironment -> (Armv7aContinuation -> TmrTaskLegacyAssertion) -> CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> Z -> Z -> Z -> Z -> UCOS2_Verify_State -> EventID -> OSEventAbstractState -> (Z -> (UCOS2_Verify_State -> Prop) -> Prop) -> Z -> Assertion)
    (tmr_task_fields_unlink_pre : Z -> Z -> Z -> Z -> Z -> Z -> Z -> TmrTaskLegacyAssertion -> Assertion)
    (tmr_task_fields_unlink_post : Z -> Z -> Z -> Z -> Z -> Z -> Z -> TmrTaskLegacyAssertion -> Assertion)
    (tmr_task_fields_link_pre : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> TmrTaskLegacyAssertion -> Assertion)
    (tmr_task_fields_link_post : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> TmrTaskLegacyAssertion -> Assertion)
*/
/*@ Printing Coq Name tmr_task_fields_lock_pre := TmrTaskFieldsCallee.lock_pre */
/*@ Printing Coq Name tmr_task_fields_lock_post := TmrTaskFieldsCallee.lock_post */
/*@ Printing Coq Name tmr_task_fields_unlock_pre := TmrTaskFieldsCallee.unlock_pre */
/*@ Printing Coq Name tmr_task_fields_unlock_post := TmrTaskFieldsCallee.unlock_post */
/*@ Printing Coq Name tmr_task_fields_pend_pre := TmrTaskFieldsCallee.pend_pre */
/*@ Printing Coq Name tmr_task_fields_unlink_pre := TmrTaskFieldsCallee.unlink_pre */
/*@ Printing Coq Name tmr_task_fields_unlink_post := TmrTaskFieldsCallee.unlink_post */
/*@ Printing Coq Name tmr_task_fields_link_pre := TmrTaskFieldsCallee.link_pre */
/*@ Printing Coq Name tmr_task_fields_link_post := TmrTaskFieldsCallee.link_post */

/* Source-backed fields contracts for the actual continuation prefixes.
 * Application bodies establish this family at the linking boundary. */
/*@ Extern Coq
    (tmr_task_client_status_callback_capabilities : {A} -> (A -> Assertion) -> TaskStackCallEnvironment -> CriticalRegionResources -> StableGlobVars -> (prod (prod Z Z) Z -> OsSchedCallContext -> program (tmr_task_scan_world A) OsSchedCallContext) -> Z -> OsSchedCallContext -> tmr_task_scan_world A -> Assertion)
    (tmr_task_callback_dispatch_domain : {A} -> StableGlobVars -> Z -> Z -> Z -> tmr_task_scan_world A -> Prop)
    (tmr_task_fields_scan_ready : {A} -> StableGlobVars -> tmr_task_scan_world A -> Prop)
    (tmr_task_client_status_callback_pre : {A} -> (A -> Assertion) -> TaskStackCallEnvironment -> StableGlobVars -> Z -> Z -> Z -> Z -> Z -> OsSchedCallContext -> tmr_task_scan_world A -> prod Z Z -> Assertion)
    (tmr_task_fields_callback_argument_rest : {A} -> (A -> Assertion) -> TaskStackCallEnvironment -> StableGlobVars -> Z -> Z -> Z -> Z -> Z -> OsSchedCallContext -> tmr_task_scan_world A -> prod Z Z -> Z -> Assertion)
    (tmr_task_client_status_callback_post : {A} -> (A -> Assertion) -> TaskStackCallEnvironment -> StableGlobVars -> (prod (prod Z Z) Z -> OsSchedCallContext -> program (tmr_task_scan_world A) OsSchedCallContext) -> Z -> Z -> Z -> Z -> Z -> OsSchedCallContext -> tmr_task_scan_world A -> prod Z Z -> unit -> Assertion)
    (tmr_task_client_status_callback_return_facts : {A} -> StableGlobVars -> (prod (prod Z Z) Z -> OsSchedCallContext -> program (tmr_task_scan_world A) OsSchedCallContext) -> Z -> Z -> Z -> OsSchedCallContext -> tmr_task_scan_world A -> OsSchedCallContext -> tmr_task_scan_world A -> Prop)
*/

/* Readable argument view. tmr_task_fields_pend_argument_pre_closed restores
 * the actual clear-status Pend pre and retains its same-X returned post. */
/*@ Extern Coq
    (tmr_task_client_clear_status_pend_entry : StableGlobVars -> OsSchedCallContext -> UCOS2_Verify_State -> Prop)
    (tmr_task_unlock_entry : StableGlobVars -> OsSchedCallContext -> UCOS2_Verify_State -> Prop)
*/
/*@ Extern Coq
    (tmr_task_client_status_iteration_entry : CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> UCOS2_Verify_State -> Prop)
    (tmr_task_client_clear_status_pend_domain : CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> EventID -> OSEventAbstractState -> Prop)
    (tmr_task_caller_wait_status_clear : OsSchedCallContext -> UCOS2_Verify_State -> Prop)
    (tmr_task_unlock_return_branch : TaskStackCallEnvironment -> CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> OsSchedCallContext -> UCOS2_Verify_State -> Prop)
*/
void OSSemPend(OS_EVENT *pevent, INT32U timeout, INT8U *perr)
/*@ timer_task_client_pend_spec
    With (environment : TaskStackCallEnvironment) (local : Armv7aContinuation -> TmrTaskLegacyAssertion)
         (critical : CriticalRegionResources) (sg : StableGlobVars) (context : OsSchedCallContext)
         (mask pe ticks pd signal_address : Z) (before : UCOS2_Verify_State)
         (eid : EventID) (observed : OSEventAbstractState) (Xk : Z -> (UCOS2_Verify_State -> Prop) -> Prop)
    Require pevent == pe && timeout == ticks && perr == pd &&
      tmr_task_client_pend_address_guard(sg, before, pe, eid,
        &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventCnt,
        &OSIntNesting, &OSLockNesting, &OSTCBCur, &OSRdyGrp, &OSRdyTbl) &&
      os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
        &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
      data_at(signal_address, OS_EVENT *, pe) *
      tmr_task_client_clear_status_pend_argument_rest(environment, local, critical, sg, context, mask,
        pe, ticks, pd, before, eid, observed, Xk, signal_address)
    Ensure tmr_task_client_clear_status_pend_lifted_post(environment, critical, sg, context, mask, pe, ticks, pd, before, Xk)
*/;

void OSSchedLock(void)
/*@ timer_task_lock_fields_spec
    With (environment : TaskStackCallEnvironment) (local : Armv7aContinuation -> TmrTaskLegacyAssertion)
         (critical : CriticalRegionResources) (sg : StableGlobVars) (context : OsSchedCallContext)
         (mask : Z) (before : UCOS2_Verify_State) (Xk : OsSchedCallContext -> UCOS2_Verify_State -> Prop)
    Require os_sched_lock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting) &&
      tmr_task_fields_lock_pre(environment, critical, local, sg, context, mask, before, Xk)
    Ensure tmr_task_fields_lock_post(environment, critical, local, sg, context, mask, before, Xk)
*/;

/* The existing product-heap lift preserves the actual callback environment.
 * These are exact existing legacy predicates, not new kernel guarantees. */
/*@ Extern Coq
    (tmr_task_fields_lift : TmrTaskLegacyAssertion -> Assertion)
    (tmr_task_unlock_fields_pre : TaskStackCallEnvironment -> CriticalRegionResources -> (Armv7aContinuation -> TmrTaskLegacyAssertion) -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> (OsSchedCallContext -> UCOS2_Verify_State -> Prop) -> TmrTaskLegacyAssertion)
    (tmr_task_unlock_fields_entry_post : TaskStackCallEnvironment -> CriticalRegionResources -> (Armv7aContinuation -> TmrTaskLegacyAssertion) -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> (OsSchedCallContext -> UCOS2_Verify_State -> Prop) -> TmrTaskLegacyAssertion)
    (os_sched_unlock_continuation_return_facts : TaskStackCallEnvironment -> CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> (OsSchedCallContext -> UCOS2_Verify_State -> Prop) -> OsSchedCallContext -> UCOS2_Verify_State -> Prop)
    (os_sched_unlock_fields_return_world : TaskStackCallEnvironment -> (Armv7aContinuation -> TmrTaskLegacyAssertion) -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> TmrTaskLegacyAssertion)
*/
/*@ Printing Coq Name tmr_task_fields_lift := TmrTaskFieldsRules.lift */

void OSSchedUnlock(void)
/*@ timer_task_unlock_fields_spec
    With (environment : TaskStackCallEnvironment) (local : Armv7aContinuation -> TmrTaskLegacyAssertion)
         (critical : CriticalRegionResources) (sg : StableGlobVars) (context : OsSchedCallContext)
         (mask : Z) (before : UCOS2_Verify_State) (Xk : OsSchedCallContext -> UCOS2_Verify_State -> Prop)
    Require tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
      tmr_task_caller_wait_status_clear(context, before) &&
      tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(context), before) &&
      os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
      &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
      tmr_task_fields_lift(tmr_task_unlock_fields_pre(environment, critical, local, sg, context, mask, before, Xk))
    Ensure tmr_task_fields_lift(tmr_task_unlock_fields_entry_post(environment, critical, local, sg, context, mask, before, Xk))
*/;

static void OSTmr_Link(OS_TMR *ptmr, INT8U type)
/*@ timer_task_link_fields_spec
    With (p base clock kind time delay period first entries : Z) (R : TmrTaskLegacyAssertion)
    Require ptmr == p && type == kind && OSTmrWheelTbl == base && &OSTmrTime == clock &&
      tmr_task_fields_link_pre(p, base, clock, kind, time, delay, period, first, entries, R)
    Ensure tmr_task_fields_link_post(p, base, clock, kind, time, delay, period, first, entries, R)
*/;

static void OSTmr_Unlink(OS_TMR *ptmr)
/*@ timer_task_unlink_fields_spec
    With (p base match_time next prev first entries : Z) (R : TmrTaskLegacyAssertion)
    Require ptmr == p && OSTmrWheelTbl == base &&
      tmr_task_fields_unlink_pre(p, base, match_time, next, prev, first, entries, R)
    Ensure tmr_task_fields_unlink_post(p, base, match_time, next, prev, first, entries, R)
*/;
#endif

