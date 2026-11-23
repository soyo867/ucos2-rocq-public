/*@ Extern Coq (program :: * => * => *) */
/*@ Extern Coq (unit :: *) */
/*@ Extern Coq (safeExec : {Sigma} {A} -> (Sigma -> Prop) -> program Sigma A -> (A -> Sigma -> Prop) -> Prop) */
/*@ Extern Coq (bind: {Sigma} {A} {B} ->  program Sigma A -> (A -> program Sigma B) -> program Sigma B) */
/*@ Extern Coq (return : {Sigma} {A} -> A -> program Sigma A) */
/*@ Extern Coq (tt: unit) */
/*@ Extern Coq (ATrue: {A} -> A -> Prop) */
/*@ Extern Coq (equiv: {T} -> T -> T -> Prop) */

/*@ Extern Coq (cons : {A} -> A -> list A -> list A) */
/*@ Extern Coq (app : {A} -> list A -> list A -> list A) */
/*@ Extern Coq (length : {A} -> list A -> Z) */
/*@ Extern Coq (Znth: {A} -> Z -> list A -> A -> A) */
/*@ Extern Coq (replace_Znth: {A} -> Z -> A -> list A -> list A) */
/*@ Extern Coq (pair : {A} {B} -> A -> B -> A * B) */
/*@ Extern Coq (fst: {A} {B} -> A * B -> A) */
/*@ Extern Coq (snd: {A} {B} -> A * B -> B) */
/*@ Extern Coq (Some: {A} -> A -> option A) */
/*@ Extern Coq (None: {A} -> option A) */
/*@ Extern Coq (In:{A}-> A -> list A -> Prop) */
/*@ Extern Coq (true : bool) */
/*@ Extern Coq (false : bool) */
/*@ Extern Coq (option :: * => *) */
/*@ Extern Coq (bool :: *) */
/*@ Extern Coq (list :: * => *) */

/*@ Extern Coq addr := Z */
/*@ Extern Coq TaskID := Z */
/*@ Extern Coq EventID := Z */
/*@ Extern Coq Priority := Z */
/*@ Extern Coq (StableGlobVars :: *) */
/*@ Extern Coq (UCOS2_Verify_State :: *) */
/*@ Extern Coq (Glob_EventAbstractState :: *) */
/*@ Extern Coq (Glob_TaskAbstractState :: *) */
/*@ Extern Coq (Glob_InterruptAbstractState :: *) */
/*@ Extern Coq (PrioTblEntry :: *) */
/*@ Extern Coq (TaskAbstractState :: *) */

/*@ Extern Coq (SchedAbstractState :: *) */
/*@ Extern Coq (TickAbstractState :: *) */
/*@ Extern Coq Record UCOS2_Verify_State {
  IntrState  : Glob_InterruptAbstractState;
  TskState   : Glob_TaskAbstractState;
  SchedState : SchedAbstractState;
  EventState : Glob_EventAbstractState;
  TickState  : TickAbstractState;
} */

/*@ Extern Coq (replace_IntrS  : Glob_InterruptAbstractState -> UCOS2_Verify_State -> UCOS2_Verify_State) */
/*@ Extern Coq (replace_TskS   : Glob_TaskAbstractState -> UCOS2_Verify_State -> UCOS2_Verify_State) */
/*@ Extern Coq (replace_EventS : Glob_EventAbstractState -> UCOS2_Verify_State -> UCOS2_Verify_State) */

/*@ Extern Coq (intNesting : Glob_InterruptAbstractState -> Z) */
/*@ Extern Coq (lockNesting : Glob_InterruptAbstractState -> Z) */

/*@ Extern Coq (OSEventType :: *) */
/*@ Extern Coq (OS_EVENT_TYPE_UNUSED : OSEventType) */
/*@ Extern Coq (OS_EVENT_TYPE_SEM    : OSEventType) */
/*@ Extern Coq (OS_EVENT_TYPE_MUTEX  : OSEventType) */
/*@ Extern Coq (OS_EVENT_TYPE_MBOX   : OSEventType) */
/*@ Extern Coq (OS_EVENT_TYPE_Q      : OSEventType) */
/*@ Extern Coq (OS_EVENT_TYPE_FLAG   : OSEventType) */
/*@ Extern Coq (encode_event_type : OSEventType -> Z) */
/*@ Extern Coq (sizeof_OS_EVENT : Z) */
/*@ Extern Coq (event_addr : StableGlobVars -> EventID -> addr) */
/*@ Extern Coq (OSEventType_off : Z) */
/*@ Extern Coq (OSEventPtr_off  : Z) */
/*@ Extern Coq (OSEventCnt_off  : Z) */
/*@ Extern Coq (OSEventGrp_off  : Z) */

/*@ Extern Coq (MutexFields :: *) */
/*@ Extern Coq (SemFields :: *) */
/*@ Extern Coq (MboxFields :: *) */
/*@ Extern Coq (QueueFields :: *) */
/*@ Extern Coq (FlagFields :: *) */
/*@ Extern Coq (OSErrCode :: *) */
/*@ Extern Coq Record OSEventAbstractState {
  eventType   : OSEventType;
  mutexFields : option MutexFields;
  semFields   : option SemFields;
  mboxFields  : option MboxFields;
  queueFields : option QueueFields;
  flagFields  : option FlagFields;
  waitList    : list TaskID;
} */
/*@ Extern Coq Record Glob_EventAbstractState {
  inUsedEventStates : EventID -> option OSEventAbstractState;
  unUsedEventStates : list EventID;
} */
/*@ Extern Coq Record Glob_TaskAbstractState {
  inUsedTaskStates : TaskID -> option TaskAbstractState;
  unUsedTaskStates : list TaskID;
  tcbListHead      : option TaskID;
  prioTbl          : Priority -> PrioTblEntry;
  taskCount        : Z;
} */
/*@ Extern Coq (PTFree : PrioTblEntry) */
/*@ Extern Coq (PTReserved : PrioTblEntry) */
/*@ Extern Coq (PTFree : PrioTblEntry) */
/*@ Extern Coq (PTTask : TaskID -> PrioTblEntry) */
/*@ Extern Coq (mfPCP           : MutexFields -> Priority) */
/*@ Extern Coq (mfOwner         : MutexFields -> option TaskID) */
/*@ Extern Coq (mfOwnerOrigPrio : MutexFields -> option Priority) */

/*@ Extern Coq (MutexDelOpt :: *) */
/*@ Extern Coq (mutex_del_spec::MutexDelNoPend : MutexDelOpt) */
/*@ Extern Coq (mutex_del_spec::MutexDelAlways : MutexDelOpt) */
/*@ Extern Coq (mutex_del_spec::MutexDelInvalid : MutexDelOpt) */

/*@ Extern Coq (OS_ERR_NONE         : OSErrCode) */
/*@ Extern Coq (OS_ERR_PEVENT_NULL  : OSErrCode) */
/*@ Extern Coq (OS_ERR_EVENT_TYPE   : OSErrCode) */
/*@ Extern Coq (OS_ERR_DEL_ISR      : OSErrCode) */
/*@ Extern Coq (OS_ERR_TASK_WAITING : OSErrCode) */
/*@ Extern Coq (OS_ERR_INVALID_OPT  : OSErrCode) */
/*@ Extern Coq (OS_TRUE  : Z) */
/*@ Extern Coq (OS_FALSE : Z) */
/*@ Extern Coq (store_priotbl_list : StableGlobVars -> list addr -> Assertion) */
/*@ Extern Coq (store_priotbl_list_missing_i : StableGlobVars -> list addr -> Z -> Assertion) */
/*@ Extern Coq (store_osrdytbl : StableGlobVars -> list Z -> Assertion) */
/*@ Extern Coq (store_osrdytbl_missing_i : StableGlobVars -> list Z -> Z -> Assertion) */
/*@ Extern Coq (prio_tbl_list_rel : StableGlobVars -> Glob_TaskAbstractState -> list addr -> Prop) */
/*@ Extern Coq (prio_tbl_entry_prop : Glob_TaskAbstractState -> Priority -> PrioTblEntry -> Prop) */
/*@ Extern Coq (event_snapshot_of_prop : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> EventID -> OSEventAbstractState -> Z -> Z -> addr -> Z -> list Z -> Prop) */
/*@ Extern Coq (event_free_list_head_prop : StableGlobVars -> Glob_EventAbstractState -> addr -> Prop) */
/*@ Extern Coq (event_deleted_snapshot_prop : Glob_EventAbstractState -> Glob_EventAbstractState -> EventID -> OSEventAbstractState -> Prop) */
/*@ Extern Coq (mutex_del_owner_restored_prop : OSEventAbstractState -> Glob_TaskAbstractState -> Prop) */
/*@ Extern Coq (mutex_del_waiters_aborted_effective_prop : OSEventAbstractState -> Glob_TaskAbstractState -> SchedAbstractState -> Prop) */
/*@ Extern Coq (decode_PCP_from_cnt : Z -> Z) */
/*@ Extern Coq (decode_OwnerPrio_from_cnt : Z -> Z) */
/*@ Extern Coq (event_core_fields_layout_prop : StableGlobVars -> EventID -> addr -> addr -> addr -> Prop) */
/*@ Extern Coq (event_wait_fields_layout_prop : StableGlobVars -> EventID -> addr -> addr -> Prop) */
/*@ Extern Coq (task_prio_snapshot_of_prop : StableGlobVars -> Glob_TaskAbstractState -> TaskID -> TaskAbstractState -> addr -> Z -> Prop) */
/*@ Extern Coq (task_prio_field_layout_prop : addr -> addr -> Prop) */

/*@ Extern Coq (coq_prop : Prop -> Assertion) */
/*@ Extern Coq (unsigned_last_nbits : Z -> Z -> Z) */
/*@ Extern Coq (valid_stable_glob_vars : StableGlobVars -> Prop) */
/*@ Extern Coq (valid_event_id : StableGlobVars -> EventID -> Prop) */
/*@ Extern Coq (store_used_event_map_missing_i : StableGlobVars -> (EventID -> option OSEventAbstractState) -> EventID -> Assertion) */
/*@ Extern Coq (used_complete_event : StableGlobVars -> addr -> EventID -> OSEventAbstractState -> Assertion) */
/*@ Extern Coq (unused_complete_event : StableGlobVars -> addr -> EventID -> Assertion) */
/*@ Extern Coq (store_free_event_list : StableGlobVars -> list EventID -> Assertion) */
/*@ Extern Coq (store_int_state : StableGlobVars -> Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (interrupt_inv : StableGlobVars -> Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (interrupt_inv_no_int_nesting : StableGlobVars -> Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (task_inv : StableGlobVars -> Glob_TaskAbstractState -> Assertion) */
/*@ Extern Coq (task_inv_missing_priotbl : StableGlobVars -> Glob_TaskAbstractState -> Priority -> Assertion) */
/*@ Extern Coq (sched_inv : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> Assertion) */
/*@ Extern Coq (sched_raw_ready_prio_stage : StableGlobVars -> SchedAbstractState -> SchedAbstractState -> Glob_TaskAbstractState -> Assertion) */
/*@ Extern Coq (sched_in_range : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> Prop) */
/*@ Extern Coq (event_inv : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> Assertion) */
/*@ Extern Coq (event_inv_no_eid : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> EventID -> Assertion) */
/*@ Extern Coq (used_event_wait_table_storage : Glob_TaskAbstractState -> addr -> OSEventAbstractState -> Assertion) */
/*@ Extern Coq (tick_inv : StableGlobVars -> TickAbstractState -> Assertion) */
/*@ Extern Coq (cross_module_consistency : StableGlobVars -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (event_inv_missing_usedevent : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> EventID -> OSEventAbstractState -> Assertion) */
/*@ Extern Coq (event_vaild_cond_prop : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> Prop) */
/*@ Extern Coq (interrupt_in_range : Glob_InterruptAbstractState -> Prop) */
/*@ Extern Coq (tcb_addr : StableGlobVars -> TaskID -> addr) */

/*@ Extern Coq (InsideCritical  : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (OutsideCritical : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (RTrans_C : StableGlobVars -> UCOS2_Verify_State -> StableGlobVars -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (GTrans_C : StableGlobVars -> UCOS2_Verify_State -> StableGlobVars -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (RTrans_Abs : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (GTrans_Abs : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (LastSeen : UCOS2_Verify_State -> (UCOS2_Verify_State -> Prop) -> Prop) */
/*@ Extern Coq (should_be_equal: {A} -> A -> A -> Prop) */
/*@ Extern Coq (crit_rel_no_os_state_change : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (crit_rel_task_event_sched : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (UCOS2_Verify_inv : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (UCOS2_state_inv : StableGlobVars -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (os_int_nesting_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_event_free_list_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_tcb_prio_tbl_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (atomic_cmd : {A} -> program UCOS2_Verify_State A -> program (UCOS2_Verify_State -> Prop) A) */
/*@ Extern Coq (mutex_del_observe_ptr : addr -> OSErrCode * option addr -> program (UCOS2_Verify_State -> Prop) Z) */
/*@ Extern Coq (mutex_del_observe_unit : unit -> program (UCOS2_Verify_State -> Prop) unit) */
/*@ Extern Coq (OSMutexDel_full_sem : StableGlobVars -> addr -> MutexDelOpt -> program UCOS2_Verify_State (OSErrCode * option addr)) */
/*@ Extern Coq (mutex_del_owner_ready_call_sem : StableGlobVars -> TaskID -> addr -> Priority -> program UCOS2_Verify_State unit) */
/*@ Extern Coq (mutex_del_owner_ready_call_prop : StableGlobVars -> TaskID -> addr -> Priority -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_del_selected_event_noninterference_prop : EventID -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_del_owner_snapshot_prop : StableGlobVars -> UCOS2_Verify_State -> OSEventAbstractState -> addr -> TaskID -> TaskAbstractState -> Z -> Z -> Prop) */
/*@ Extern Coq (mutex_del_owner_value_lineage_prop : OSEventAbstractState -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (mutex_del_open_inv : StableGlobVars -> UCOS2_Verify_State -> TaskID -> TaskAbstractState -> Assertion) */
/*@ Extern Coq (mutex_del_event_focus_inv : StableGlobVars -> UCOS2_Verify_State -> EventID -> Assertion) */
/*@ Extern Coq (mutex_del_event_focus_no_interrupt_inv : StableGlobVars -> UCOS2_Verify_State -> EventID -> Assertion) */
/*@ Extern Coq (mutex_del_event_owner_open_inv : StableGlobVars -> UCOS2_Verify_State -> EventID -> TaskID -> TaskAbstractState -> Assertion) */
/*@ Extern Coq (mutex_del_rdyatprio_stage_prop : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_del_owner_stage_focus : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> Assertion) */
/*@ Extern Coq (mutex_del_event_missing_priotbl_focus : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> EventID -> Priority -> Assertion) */
/*@ Extern Coq (mutex_del_pcp_release_focus : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> EventID -> Priority -> Assertion) */
/*@ Extern Coq (mutex_del_owner_release_stage_focus : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> Priority -> Assertion) */
/*@ Extern Coq (mutex_del_no_pend_pcp_release_residual : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> addr -> Z -> Z -> Z -> Priority -> addr -> Assertion) */
/*@ Extern Coq (mutex_del_event_ready_focus_inv : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> EventID -> Assertion) */
/*@ Extern Coq (mutex_del_wake_step : StableGlobVars -> EventID -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_del_wake_steps : StableGlobVars -> EventID -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_del_abort_loop_residual : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> addr -> Z -> Z -> Z -> addr -> Assertion) */
/*@ Extern Coq (mutex_del_abort_loop_missing_priotbl_residual : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> addr -> Z -> Z -> Z -> Priority -> addr -> Assertion) */
/*@ Extern Coq (mutex_del_abort_loop_pcp_release_residual : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> addr -> Z -> Z -> Z -> Priority -> addr -> Assertion) */
/*@ Extern Coq (priotbl_element_store : addr -> Z -> addr -> Assertion) */
/*@ Extern Coq (mutex_del_abort_loop_stage_prop : StableGlobVars -> EventID -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_del_no_pend_prepare_stage_prop : EventID -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_del_free_stage_prop : StableGlobVars -> EventID -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_del_sched_stage_prop : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_del_source_entry_prop : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> addr -> Z -> Prop) */
/*@ Extern Coq (mutex_del_input_classification_prop : StableGlobVars -> UCOS2_Verify_State -> EventID -> OSEventAbstractState -> addr -> Z -> Z -> Z -> Z -> list Z -> addr -> addr -> addr -> addr -> addr -> TaskID -> TaskAbstractState -> Z -> addr -> Z -> Z -> Prop) */
/*@ Extern Coq (mutex_del_return_lineage_prop : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> addr -> addr -> addr -> addr -> addr -> addr -> Z -> Z -> Z -> MutexDelOpt -> Z -> addr -> Z -> list Z -> Prop) */
/*@ Extern Coq (mutex_del_option_decode_prop : Z -> MutexDelOpt -> Prop) */
/*@ Extern Coq (mutex_del_success_mode_prop : MutexDelOpt -> Z -> Prop) */
/*@ Extern Coq (mutex_del_no_pend_mode_prop : MutexDelOpt -> Z -> Prop) */
/*@ Extern Coq (mutex_del_always_mode_prop : MutexDelOpt -> Z -> Prop) */
/*@ Extern Coq (mutex_del_error_mode_prop : MutexDelOpt -> Z -> Z -> Prop) */
/*@ Extern Coq (mutex_del_success_commit_inv : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> MutexDelOpt -> addr -> Z -> (Z -> (UCOS2_Verify_State -> Prop) -> Prop) -> Assertion) */
/*@ Extern Coq (mutex_del_success_refreshed_commit_inv : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> MutexDelOpt -> addr -> Z -> (Z -> (UCOS2_Verify_State -> Prop) -> Prop) -> Assertion) */
/*@ Extern Coq (mutex_del_success_exit_inv : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> MutexDelOpt -> addr -> Z -> (Z -> (UCOS2_Verify_State -> Prop) -> Prop) -> Assertion) */
/*@ Extern Coq (mutex_del_no_pend_exit_inv : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> MutexDelOpt -> addr -> Z -> (Z -> (UCOS2_Verify_State -> Prop) -> Prop) -> Assertion) */
/*@ Extern Coq (mutex_del_success_out_inv : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> MutexDelOpt -> addr -> Z -> (Z -> (UCOS2_Verify_State -> Prop) -> Prop) -> Assertion) */
/*@ Extern Coq (mutex_del_transition_rep : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (mutex_del_restore_rep : bool -> StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (mutex_del_refresh_layout_prop : StableGlobVars -> addr -> addr -> addr -> addr -> addr -> Prop) */
/*@ Extern Coq (mutex_del_refresh_context_prop : StableGlobVars -> addr -> addr -> addr -> addr -> addr -> Prop) */
/*@ Extern Coq (mutex_del_first_set8 : Z -> Z) */
/*@ Extern Coq (mutex_del_refresh_grp_value : UCOS2_Verify_State -> Z) */
/*@ Extern Coq (mutex_del_refresh_ready_tbl_values : UCOS2_Verify_State -> list Z) */
/*@ Extern Coq (mutex_del_refresh_prio_tbl_values : StableGlobVars -> UCOS2_Verify_State -> list addr) */
/*@ Extern Coq (mutex_del_refresh_snapshot_prop : StableGlobVars -> UCOS2_Verify_State -> Z -> list Z -> list addr -> Prop) */
/*@ Extern Coq (mutex_del_refresh_choice_prop : StableGlobVars -> UCOS2_Verify_State -> Z -> Z -> Prop) */
/*@ Extern Coq (mutex_del_refresh_residual : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (mutex_del_refresh_closed_inv : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (mutex_del_unchanged_inside_inv : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> addr -> MutexDelOpt -> Z -> Z -> (Z -> (UCOS2_Verify_State -> Prop) -> Prop) -> Assertion) */
/*@ Extern Coq (mutex_del_unchanged_exit_inv : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> addr -> MutexDelOpt -> Z -> Z -> (Z -> (UCOS2_Verify_State -> Prop) -> Prop) -> Assertion) */
/*@ Extern Coq (mutex_del_success_commit_prop : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> MutexDelOpt -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_del_success_commit_anchor_prop : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> MutexDelOpt -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_del_success_post_refinement_prop : StableGlobVars -> OSEventAbstractState -> UCOS2_Verify_State -> EventID -> MutexDelOpt -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_del_enter_critical_call_prop : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_del_exit_critical_call_prop : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_del_exit_critical_anchored_call_prop : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_del_no_pend_prepare : EventID -> UCOS2_Verify_State -> unit -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (atomic_event_free_with_priotbl_free : StableGlobVars -> EventID -> UCOS2_Verify_State -> unit -> UCOS2_Verify_State -> Prop) */

/*@ Import Coq Local Open Scope Z_scope */
/*@ Import Coq Local Open Scope sac */

/*@ Import Coq From MonadLib Require Import Monad */
/*@ Import Coq From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib */
/*@ Import Coq Import Monad MonadNotation */
/*@ Import Coq Local Open Scope monad_scope */
/*@ Import Coq Require Import Ucos2Verify.lib.stable_glob_vars */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_verify_state_def */
/*@ Import Coq Require Import Ucos2Verify.lib.task */
/*@ Import Coq Require Import Ucos2Verify.lib.interrupt */
/*@ Import Coq Require Import Ucos2Verify.lib.sched */
/*@ Import Coq Require Import Ucos2Verify.lib.event */
/*@ Import Coq Require Import Ucos2Verify.lib.mutex */
/*@ Import Coq Require Import Ucos2Verify.lib.error_codes */
/*@ Import Coq Require Import Ucos2Verify.lib.atomic_ops_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_rules_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_verify_inv */
/*@ Import Coq Require Import Ucos2Verify.lib.mutex_del_spec */
/*@ Import Coq Require Import Ucos2Verify.lib.array_abstraction */
/*@ Import Coq Require Import Ucos2Verify.lib.tick */
/*@ Import Coq Require Import Ucos2Verify.lib.cross_module_invariants */

typedef unsigned int OS_CPU_SR;

unsigned int OS_CPU_SR_Save()
/*@ With (sg: StableGlobVars) (ls0: UCOS2_Verify_State) (eid: EventID)
    Require OutsideCritical(sg, ls0) &&
            mutex_del_event_focus_inv(sg, ls0, eid)
    Ensure  RTrans_C(sg, ls0, sg, ls0) &&
            InsideCritical(sg, ls0) &&
            mutex_del_event_focus_inv(sg, ls0, eid) &&
            coq_prop(mutex_del_enter_critical_call_prop(sg, ls0, ls0)) &&
            __return == __return
*/
;

void OS_CPU_SR_Restore(unsigned int cpu_sr)
/*@ With (sg: StableGlobVars) (entry: UCOS2_Verify_State)
           (raw_stage: bool)
           (critical_anchor: UCOS2_Verify_State)
           (logical_post: UCOS2_Verify_State)
    Require InsideCritical(sg, critical_anchor) &&
            mutex_del_restore_rep(raw_stage, sg, entry, logical_post)
    Ensure  exists ls2,
            OutsideCritical(sg, ls2) &&
            mutex_del_restore_rep(raw_stage, sg, entry, ls2) &&
            coq_prop(mutex_del_exit_critical_anchored_call_prop(
              sg, critical_anchor, logical_post, ls2))
*/
;

#define OS_ENTER_CRITICAL() cpu_sr = OS_CPU_SR_Save()
#define OS_EXIT_CRITICAL()  OS_CPU_SR_Restore(cpu_sr)

typedef unsigned char  INT8U;
typedef unsigned short INT16U;
typedef unsigned int   INT32U;
typedef unsigned char  OS_PRIO;
typedef unsigned char  BOOLEAN;
#define  OS_FALSE                       0u
#define  OS_TRUE                        1u
#define  OS_LOWEST_PRIO                 63u
#define  OS_EVENT_TYPE_UNUSED           0u
#define  OS_EVENT_TYPE_MUTEX            4u
#define  OS_ERR_NONE                    0u
#define  OS_ERR_EVENT_TYPE              1u
#define  OS_ERR_PEVENT_NULL             4u
#define  OS_ERR_INVALID_OPT             7u
#define  OS_ERR_DEL_ISR                 15u
#define  OS_ERR_TASK_WAITING            73u
#define  OS_DEL_NO_PEND                 0u
#define  OS_DEL_ALWAYS                  1u
#define  OS_MUTEX_KEEP_LOWER_8          0x00FFu
#define  OS_MUTEX_KEEP_UPPER_8          0xFF00u
#define  OS_PRIO_MUTEX_CEIL_DIS         0xFFu
#define  OS_STAT_MUTEX                  0x10u
#define  OS_STAT_PEND_ABORT             2u

typedef struct os_tcb {
    INT8U         OSTCBPrio;
    INT8U         OSTCBStat;
    INT8U         OSTCBStatPend;
    INT8U         OSTCBPad0;
    INT32U        OSTCBDly;
    INT8U         OSTCBX;
    INT8U         OSTCBY;
    OS_PRIO       OSTCBBitX;
    OS_PRIO       OSTCBBitY;
    void         *OSTCBEventPtr;
    void        **OSTCBEventMultiPtr;
    void         *OSTCBEventMultiRdy;
    void         *OSTCBMsg;
    struct os_tcb *OSTCBNext;
    struct os_tcb *OSTCBPrev;
    INT8U         OSTCBDelReq;
    INT8U         OSTCBVerifyTail[31];
} OS_TCB;

typedef struct os_event {
    INT8U    OSEventType;
    void    *OSEventPtr;
    INT16U   OSEventCnt;
    OS_PRIO  OSEventGrp;
    OS_PRIO  OSEventTbl[8];
} OS_EVENT;

extern  INT8U     OSIntNesting;
extern  INT8U     OSLockNesting;
extern  OS_EVENT *OSEventFreeList;
extern  OS_PRIO    OSRdyGrp;
extern  OS_PRIO    OSRdyTbl[8];
extern  OS_PRIO    OSPrioHighRdy;
extern  OS_TCB    *OSTCBHighRdy;
extern  OS_TCB   *OSTCBPrioTbl[64];

INT8U OSMutexDel_FirstSet8(INT8U bits)
/*@ With (bits_in: Z)
    Require bits == bits_in &&
            0 <= bits_in && bits_in <= 255 && emp
    Ensure  __return == mutex_del_first_set8(bits_in) &&
            0 <= __return && __return < 8 && emp
*/
{
    if ((bits & 0x01u) != 0u) return 0u;
    if ((bits & 0x02u) != 0u) return 1u;
    if ((bits & 0x04u) != 0u) return 2u;
    if ((bits & 0x08u) != 0u) return 3u;
    if ((bits & 0x10u) != 0u) return 4u;
    if ((bits & 0x20u) != 0u) return 5u;
    if ((bits & 0x40u) != 0u) return 6u;
    return 7u;
}

void OSMutexDel_RefreshHighReady(void)
/*@ With (sg: StableGlobVars) (entry: UCOS2_Verify_State)
           (critical_anchor: UCOS2_Verify_State)
           (post: UCOS2_Verify_State)
    Require InsideCritical(sg, critical_anchor) &&
            mutex_del_transition_rep(sg, entry, post) &&
            coq_prop(mutex_del_refresh_context_prop(
              sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy,
              &OSTCBHighRdy, OSTCBPrioTbl))
    Ensure  InsideCritical(sg, critical_anchor) &&
            mutex_del_restore_rep(false, sg, entry, post) &&
            coq_prop(mutex_del_refresh_context_prop(
              sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy,
              &OSTCBHighRdy, OSTCBPrioTbl))
*/
{
    INT8U  grp;
    INT8U  y;
    INT8U  row;
    INT8U  x;
    INT8U  high_prio;
    OS_TCB *high_tcb;

    /*@
        InsideCritical(sg, critical_anchor) *
        mutex_del_transition_rep(sg, entry, post) *
        coq_prop(mutex_del_refresh_context_prop(
          sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy,
          &OSTCBHighRdy, OSTCBPrioTbl))
        which implies
        exists (old_high_prio: Z) (old_high_tcb: Z),
          InsideCritical(sg, critical_anchor) *
          data_at(&OSRdyGrp, unsigned char,
                  mutex_del_refresh_grp_value(post)) *
          store_osrdytbl(
            sg, mutex_del_refresh_ready_tbl_values(post)) *
          data_at(&OSPrioHighRdy, unsigned char, old_high_prio) *
          data_at(&OSTCBHighRdy, struct os_tcb *, old_high_tcb) *
          store_priotbl_list(
            sg, mutex_del_refresh_prio_tbl_values(sg, post)) *
          mutex_del_refresh_residual(sg, post) *
          coq_prop(mutex_del_refresh_snapshot_prop(
            sg, post, mutex_del_refresh_grp_value(post),
            mutex_del_refresh_ready_tbl_values(post),
            mutex_del_refresh_prio_tbl_values(sg, post))) *
          coq_prop(UCOS2_state_inv(sg, post)) *
          coq_prop(mutex_del_refresh_context_prop(
            sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy,
            &OSTCBHighRdy, OSTCBPrioTbl))
    */
    grp = OSRdyGrp;
    if (grp == 0u) {
        /*@
            mutex_del_refresh_grp_value(post) == 0 &&
            coq_prop(mutex_del_refresh_snapshot_prop(
              sg, post, mutex_del_refresh_grp_value(post),
              mutex_del_refresh_ready_tbl_values(post),
              mutex_del_refresh_prio_tbl_values(sg, post)))
            which implies
            coq_prop(mutex_del_refresh_choice_prop(sg, post, 255, 0))
        */
        OSPrioHighRdy = 0xFFu;
        OSTCBHighRdy  = (OS_TCB *)0;
        /*@
            InsideCritical(sg, critical_anchor) *
            data_at(&OSRdyGrp, unsigned char,
                    mutex_del_refresh_grp_value(post)) *
            store_osrdytbl(
              sg, mutex_del_refresh_ready_tbl_values(post)) *
            data_at(&OSPrioHighRdy, unsigned char, 255) *
            data_at(&OSTCBHighRdy, struct os_tcb *, 0) *
            store_priotbl_list(
              sg, mutex_del_refresh_prio_tbl_values(sg, post)) *
            mutex_del_refresh_residual(sg, post) *
            coq_prop(mutex_del_refresh_choice_prop(sg, post, 255, 0)) *
            coq_prop(UCOS2_state_inv(sg, post)) *
            coq_prop(mutex_del_refresh_context_prop(
              sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy,
              &OSTCBHighRdy, OSTCBPrioTbl))
            which implies
            InsideCritical(sg, critical_anchor) *
            mutex_del_refresh_closed_inv(sg, post) *
            coq_prop(mutex_del_refresh_context_prop(
              sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy,
              &OSTCBHighRdy, OSTCBPrioTbl))
        */
        /*@ mutex_del_refresh_closed_inv(sg, post)
            which implies mutex_del_restore_rep(false, sg, entry, post)
        */
    } else {
        y = OSMutexDel_FirstSet8(grp)/*@ where bits_in = grp */;
        /*@
            y == mutex_del_first_set8(
                   mutex_del_refresh_grp_value(post)) &&
            0 <= y && y < 8 &&
            store_osrdytbl(
              sg, mutex_del_refresh_ready_tbl_values(post)) *
            coq_prop(mutex_del_refresh_context_prop(
              sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy,
              &OSTCBHighRdy, OSTCBPrioTbl))
            which implies
            data_at(&y, unsigned char,
                    mutex_del_first_set8(
                      mutex_del_refresh_grp_value(post))) *
            data_at(pointer_offset(OSRdyTbl, y, unsigned char),
                    unsigned char,
                    Znth(y, mutex_del_refresh_ready_tbl_values(post), 0)) *
            store_osrdytbl_missing_i(
              sg, mutex_del_refresh_ready_tbl_values(post), y) *
            coq_prop(mutex_del_refresh_context_prop(
              sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy,
              &OSTCBHighRdy, OSTCBPrioTbl))
        */
        row = OSRdyTbl[y];
        /*@
            y == mutex_del_first_set8(
                   mutex_del_refresh_grp_value(post)) &&
            row == Znth(
              mutex_del_first_set8(mutex_del_refresh_grp_value(post)),
              mutex_del_refresh_ready_tbl_values(post), 0) &&
            data_at(pointer_offset(OSRdyTbl, y, unsigned char),
                    unsigned char, row) *
            store_osrdytbl_missing_i(
              sg, mutex_del_refresh_ready_tbl_values(post), y) *
            coq_prop(mutex_del_refresh_context_prop(
              sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy,
              &OSTCBHighRdy, OSTCBPrioTbl))
            which implies
            data_at(&y, unsigned char,
                    mutex_del_first_set8(
                      mutex_del_refresh_grp_value(post))) *
            data_at(&row, unsigned char,
                    Znth(
                      mutex_del_first_set8(
                        mutex_del_refresh_grp_value(post)),
                      mutex_del_refresh_ready_tbl_values(post), 0)) *
            store_osrdytbl(
              sg, mutex_del_refresh_ready_tbl_values(post)) *
            coq_prop(mutex_del_refresh_context_prop(
              sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy,
              &OSTCBHighRdy, OSTCBPrioTbl))
        */
        x = OSMutexDel_FirstSet8(row)/*@ where bits_in = row */;
        high_prio = (INT8U)(y * 8u + x);
        /*@
            high_prio ==
              mutex_del_first_set8(mutex_del_refresh_grp_value(post)) * 8 +
              mutex_del_first_set8(Znth(
                mutex_del_first_set8(mutex_del_refresh_grp_value(post)),
                mutex_del_refresh_ready_tbl_values(post), 0)) &&
            0 <= high_prio && high_prio < 64 &&
            store_priotbl_list(
              sg, mutex_del_refresh_prio_tbl_values(sg, post)) *
            coq_prop(mutex_del_refresh_context_prop(
              sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy,
              &OSTCBHighRdy, OSTCBPrioTbl))
            which implies
            data_at(&high_prio, unsigned char,
              mutex_del_first_set8(mutex_del_refresh_grp_value(post)) * 8 +
              mutex_del_first_set8(Znth(
                mutex_del_first_set8(mutex_del_refresh_grp_value(post)),
                mutex_del_refresh_ready_tbl_values(post), 0))) *
            data_at(pointer_offset(
                      OSTCBPrioTbl, high_prio, OS_TCB *), OS_TCB *,
                    Znth(high_prio,
                         mutex_del_refresh_prio_tbl_values(sg, post), 0)) *
            store_priotbl_list_missing_i(
              sg, mutex_del_refresh_prio_tbl_values(sg, post),
              high_prio) *
            coq_prop(mutex_del_refresh_context_prop(
              sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy,
              &OSTCBHighRdy, OSTCBPrioTbl))
        */
        high_tcb = OSTCBPrioTbl[high_prio];
        /*@
            high_prio ==
              mutex_del_first_set8(mutex_del_refresh_grp_value(post)) * 8 +
              mutex_del_first_set8(Znth(
                mutex_del_first_set8(mutex_del_refresh_grp_value(post)),
                mutex_del_refresh_ready_tbl_values(post), 0)) &&
            high_tcb == Znth(
              high_prio,
              mutex_del_refresh_prio_tbl_values(sg, post), 0) &&
            data_at(pointer_offset(
                      OSTCBPrioTbl, high_prio, OS_TCB *),
                    OS_TCB *, high_tcb) *
            store_priotbl_list_missing_i(
              sg, mutex_del_refresh_prio_tbl_values(sg, post),
              high_prio) *
            coq_prop(mutex_del_refresh_context_prop(
              sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy,
              &OSTCBHighRdy, OSTCBPrioTbl))
            which implies
            data_at(&high_prio, unsigned char,
              mutex_del_first_set8(mutex_del_refresh_grp_value(post)) * 8 +
              mutex_del_first_set8(Znth(
                mutex_del_first_set8(mutex_del_refresh_grp_value(post)),
                mutex_del_refresh_ready_tbl_values(post), 0))) *
            data_at(&high_tcb, OS_TCB *,
              Znth(
                mutex_del_first_set8(mutex_del_refresh_grp_value(post)) * 8 +
                mutex_del_first_set8(Znth(
                  mutex_del_first_set8(mutex_del_refresh_grp_value(post)),
                  mutex_del_refresh_ready_tbl_values(post), 0)),
                mutex_del_refresh_prio_tbl_values(sg, post), 0)) *
            store_priotbl_list(
              sg, mutex_del_refresh_prio_tbl_values(sg, post)) *
            coq_prop(mutex_del_refresh_context_prop(
              sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy,
              &OSTCBHighRdy, OSTCBPrioTbl))
        */
        /*@
            mutex_del_refresh_grp_value(post) != 0 &&
            coq_prop(mutex_del_refresh_snapshot_prop(
              sg, post, mutex_del_refresh_grp_value(post),
              mutex_del_refresh_ready_tbl_values(post),
              mutex_del_refresh_prio_tbl_values(sg, post)))
            which implies
            coq_prop(mutex_del_refresh_choice_prop(
              sg, post,
              mutex_del_first_set8(mutex_del_refresh_grp_value(post)) * 8 +
              mutex_del_first_set8(Znth(
                mutex_del_first_set8(mutex_del_refresh_grp_value(post)),
                mutex_del_refresh_ready_tbl_values(post), 0)),
              Znth(
                mutex_del_first_set8(mutex_del_refresh_grp_value(post)) * 8 +
                mutex_del_first_set8(Znth(
                  mutex_del_first_set8(mutex_del_refresh_grp_value(post)),
                  mutex_del_refresh_ready_tbl_values(post), 0)),
                mutex_del_refresh_prio_tbl_values(sg, post), 0)))
        */
        OSPrioHighRdy = high_prio;
        OSTCBHighRdy  = high_tcb;
        /*@
            InsideCritical(sg, critical_anchor) *
            data_at(&OSRdyGrp, unsigned char,
                    mutex_del_refresh_grp_value(post)) *
            store_osrdytbl(
              sg, mutex_del_refresh_ready_tbl_values(post)) *
            data_at(&OSPrioHighRdy, unsigned char,
              mutex_del_first_set8(mutex_del_refresh_grp_value(post)) * 8 +
              mutex_del_first_set8(Znth(
                mutex_del_first_set8(mutex_del_refresh_grp_value(post)),
                mutex_del_refresh_ready_tbl_values(post), 0))) *
            data_at(&OSTCBHighRdy, struct os_tcb *,
              Znth(
                mutex_del_first_set8(mutex_del_refresh_grp_value(post)) * 8 +
                mutex_del_first_set8(Znth(
                  mutex_del_first_set8(mutex_del_refresh_grp_value(post)),
                  mutex_del_refresh_ready_tbl_values(post), 0)),
                mutex_del_refresh_prio_tbl_values(sg, post), 0)) *
            store_priotbl_list(
              sg, mutex_del_refresh_prio_tbl_values(sg, post)) *
            mutex_del_refresh_residual(sg, post) *
            coq_prop(mutex_del_refresh_choice_prop(
              sg, post,
              mutex_del_first_set8(mutex_del_refresh_grp_value(post)) * 8 +
              mutex_del_first_set8(Znth(
                mutex_del_first_set8(mutex_del_refresh_grp_value(post)),
                mutex_del_refresh_ready_tbl_values(post), 0)),
              Znth(
                mutex_del_first_set8(mutex_del_refresh_grp_value(post)) * 8 +
                mutex_del_first_set8(Znth(
                  mutex_del_first_set8(mutex_del_refresh_grp_value(post)),
                  mutex_del_refresh_ready_tbl_values(post), 0)),
                mutex_del_refresh_prio_tbl_values(sg, post), 0))) *
            coq_prop(UCOS2_state_inv(sg, post)) *
            coq_prop(mutex_del_refresh_context_prop(
              sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy,
              &OSTCBHighRdy, OSTCBPrioTbl))
            which implies
            InsideCritical(sg, critical_anchor) *
            mutex_del_refresh_closed_inv(sg, post) *
            coq_prop(mutex_del_refresh_context_prop(
              sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy,
              &OSTCBHighRdy, OSTCBPrioTbl))
        */
        /*@ mutex_del_refresh_closed_inv(sg, post)
            which implies mutex_del_restore_rep(false, sg, entry, post)
        */
    }
}

void OSMutex_RdyAtPrio(OS_TCB *ptcb, INT8U prio)
/*@ With (sg: StableGlobVars) (ls: UCOS2_Verify_State)
           (eid: EventID)
           (owner_tid: TaskID) (owner_t_abs: TaskAbstractState)
           (e_abs: OSEventAbstractState)
           (owner_prio_abs: Z) (ecnt_abs: Z) (pcp_abs: Z)
    Require InsideCritical(sg, ls) &&
            mutex_del_event_focus_inv(sg, ls, eid) &&
            ptcb != 0 &&
            owner_prio_abs == pcp_abs &&
            pcp_abs != 255 &&
            coq_prop(mutex_del_owner_snapshot_prop(
              sg, ls, e_abs, ptcb, owner_tid, owner_t_abs, owner_prio_abs,
              &ptcb->OSTCBPrio)) &&
            coq_prop(mutex_del_owner_value_lineage_prop(
              e_abs, ecnt_abs, pcp_abs, prio))
    Ensure  exists ls_rdy,
            InsideCritical(sg, ls_rdy) &&
            mutex_del_event_ready_focus_inv(sg, ls, ls_rdy, eid) &&
            ptcb != 0 &&
            owner_prio_abs == pcp_abs &&
            pcp_abs != 255 &&
            coq_prop(mutex_del_owner_snapshot_prop(
              sg, ls, e_abs, ptcb, owner_tid, owner_t_abs, owner_prio_abs,
              &ptcb->OSTCBPrio)) &&
            coq_prop(mutex_del_owner_value_lineage_prop(
              e_abs, ecnt_abs, pcp_abs, prio)) &&
            coq_prop(mutex_del_owner_ready_call_prop(
              sg, owner_tid, ptcb, prio, ls, ls_rdy)) &&
            coq_prop(mutex_del_selected_event_noninterference_prop(
              eid, ls, ls_rdy))
*/
;

INT8U OS_EventTaskRdy(OS_EVENT *pevent, void *msg, INT8U msk, INT8U pend_stat)
/*@ With (sg: StableGlobVars) (eid: EventID)
           (anchor: UCOS2_Verify_State) (ls: UCOS2_Verify_State)
           (e_abs: OSEventAbstractState)
           (etype_abs: Z) (ecnt_abs: Z) (eptr_abs: Z)
           (egrp_in: Z) (evtL_abs: list Z)
    Require InsideCritical(sg, ls) &&
            mutex_del_event_ready_focus_inv(sg, anchor, ls, eid) &&
            pevent == event_addr(sg, eid) &&
            coq_prop(valid_event_id(sg, eid)) &&
            coq_prop(event_snapshot_of_prop(
              sg, ls.TskState, ls.EventState, eid, e_abs,
              etype_abs, ecnt_abs, eptr_abs, egrp_in, evtL_abs)) &&
            data_at(&pevent->OSEventGrp, egrp_in) &&
            used_event_wait_table_storage(ls.TskState, pevent, e_abs) &&
            egrp_in != 0
    Ensure  exists (ls_r: UCOS2_Verify_State)
                   (e_r: OSEventAbstractState)
                   (egrp_out: Z) (evtL_out: list Z),
            InsideCritical(sg, ls_r) &&
            mutex_del_event_ready_focus_inv(
              sg, anchor, ls_r, eid) &&
            pevent == event_addr(sg, eid) &&
            coq_prop(valid_event_id(sg, eid)) &&
            coq_prop(event_snapshot_of_prop(
              sg, ls_r.TskState, ls_r.EventState, eid, e_r,
              etype_abs, ecnt_abs, eptr_abs, egrp_out, evtL_out)) &&
            data_at(&pevent->OSEventGrp, egrp_out) &&
            used_event_wait_table_storage(ls_r.TskState, pevent, e_r) &&
            coq_prop(mutex_del_wake_step(sg, eid, ls, ls_r))
*/
;

void OS_Sched()
/*@ With (sg: StableGlobVars) (entry: UCOS2_Verify_State)
           (ls: UCOS2_Verify_State)
    Require OutsideCritical(sg, ls) &&
            mutex_del_transition_rep(sg, entry, ls)
    Ensure  exists ls_sched,
            OutsideCritical(sg, ls_sched) &&
            mutex_del_transition_rep(sg, entry, ls_sched) &&
            coq_prop(mutex_del_sched_stage_prop(ls, ls_sched))
*/
;

/* ============================================================ */
/* OSMutexDel_full: µC/OS-II os_mutex.c 字面实现.               */
/*                                                              */
/* 目标(纯 list + 字面变下标):                                  */
/*   - PRE/POST 数组资源只用 list 谓词,不罗列 cell              */
/*   - body 还原源码字面 OSTCBPrioTbl[pcp] = 0                 */
/*   - 不用 helper 包装、不用指针算术别名                        */
/*                                                              */
/* 字面 body 中的变下标访问点(共 2 处,分布于 NO_PEND/ALWAYS):  */
/*   (1) OSTCBPrioTbl[pcp] = 0  (NO_PEND 分支,释放 ceiling)    */
/*   (2) OSTCBPrioTbl[pcp] = 0  (ALWAYS 分支,释放 ceiling)     */
/*                                                              */
/* which implies 在每个变下标点把整体 list 拆为 missing_i + cell.*/
/* ============================================================ */
OS_EVENT *OSMutexDel_full (OS_EVENT *pevent, INT8U opt, INT8U *perr)
/*@ With (sg: StableGlobVars) (ls0: UCOS2_Verify_State) X
           (opt_abs: MutexDelOpt) (eid: EventID) (e: OSEventAbstractState)
           (owner_tid: TaskID) (owner_t: TaskAbstractState)
           (isr: Z) (pe: addr) (pd: addr) (perr_in: Z) (opt_in: Z)
           (etype: Z) (ecnt_in: Z) (eptr_in: Z) (egrp_in: Z)
           (evtL_in: list Z)
           (freelist_in: Z) (owner_prio: Z) (owner_orig: Z)
           (prioL_in: list addr)
           (pcp_idx: Z) (prio_tbl_pcp: Z)
    Require
        data_at(perr, unsigned char, perr_in) &&
        perr != 0 &&
        isr == intNesting(ls0.IntrState) &&
        coq_prop(event_free_list_head_prop(sg, ls0.EventState,
                                           freelist_in)) &&
        coq_prop(prio_tbl_list_rel(sg, ls0.TskState, prioL_in)) &&
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
        coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
        coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
        pe == pevent &&
        pd == perr &&
        opt == opt_in &&
        coq_prop(mutex_del_option_decode_prop(opt_in, opt_abs)) &&
        safeExec(LastSeen(ls0),
                 bind(atomic_cmd(OSMutexDel_full_sem(sg, pevent, opt_abs)),
                      mutex_del_observe_ptr(pevent)), X) &&
        OutsideCritical(sg, ls0) &&
        UCOS2_Verify_inv(sg, ls0) &&
        coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) &&
        pcp_idx == decode_PCP_from_cnt(ecnt_in) &&
        Znth(pcp_idx, prioL_in, 0) == prio_tbl_pcp &&
        coq_prop(mutex_del_input_classification_prop(
          sg, ls0, eid, e, pevent, etype, ecnt_in, eptr_in,
          egrp_in, evtL_in, &pevent->OSEventType,
          &pevent->OSEventPtr, &pevent->OSEventCnt,
          &pevent->OSEventGrp, pevent->OSEventTbl,
          owner_tid, owner_t, owner_prio,
          &((OS_TCB *)eptr_in)->OSTCBPrio, owner_orig, pcp_idx))
    Ensure
        exists (ls_post : UCOS2_Verify_State) (retv : Z),
        safeExec(LastSeen(ls_post), return(retv), X) &&
        OutsideCritical(sg, ls_post) &&
        __return == retv &&
        pe == pevent &&
        pd == perr &&
        (
            (__return == pe &&
             pevent == 0 &&
             UCOS2_Verify_inv(sg, ls_post) &&
             data_at(perr, unsigned char, 4) &&
             coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) &&
             coq_prop(event_free_list_head_prop(
               sg, ls0.EventState, freelist_in)) &&
             coq_prop(prio_tbl_list_rel(
               sg, ls0.TskState, prioL_in)) &&
             coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
             coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
             coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
             coq_prop(mutex_del_option_decode_prop(opt_in, opt_abs)) &&
             coq_prop(mutex_del_input_classification_prop(
               sg, ls0, eid, e, pevent, etype, ecnt_in, eptr_in,
               egrp_in, evtL_in, &pevent->OSEventType,
               &pevent->OSEventPtr, &pevent->OSEventCnt,
               &pevent->OSEventGrp, pevent->OSEventTbl,
               owner_tid, owner_t, owner_prio,
               &((OS_TCB *)eptr_in)->OSTCBPrio,
               owner_orig, pcp_idx))) ||
            (__return == pe &&
             pevent != 0 &&
             etype != 4 &&
             UCOS2_Verify_inv(sg, ls_post) &&
             coq_prop(event_snapshot_of_prop(
               sg, ls_post.TskState, ls_post.EventState, eid, e, etype,
               ecnt_in, eptr_in, egrp_in, evtL_in)) &&
             data_at(perr, unsigned char, 1)) ||
            (__return == pe &&
             pevent != 0 &&
             etype == 4 &&
             isr > 0 &&
             UCOS2_Verify_inv(sg, ls_post) &&
             coq_prop(event_snapshot_of_prop(
               sg, ls_post.TskState, ls_post.EventState, eid, e, 4,
               ecnt_in, eptr_in, egrp_in, evtL_in)) &&
             data_at(perr, unsigned char, 15)) ||
            (__return == pe &&
             pevent != 0 &&
             etype == 4 &&
             isr <= 0 &&
             opt_in == 0 &&
             egrp_in != 0 &&
             UCOS2_Verify_inv(sg, ls_post) &&
             coq_prop(event_snapshot_of_prop(
               sg, ls_post.TskState, ls_post.EventState, eid, e, 4,
               ecnt_in, eptr_in, egrp_in, evtL_in)) &&
             data_at(perr, unsigned char, 73)) ||
            (__return == pe &&
             pevent != 0 &&
             etype == 4 &&
             isr <= 0 &&
             opt_in != 0 &&
             opt_in != 1 &&
             UCOS2_Verify_inv(sg, ls_post) &&
             coq_prop(event_snapshot_of_prop(
               sg, ls_post.TskState, ls_post.EventState, eid, e, 4,
               ecnt_in, eptr_in, egrp_in, evtL_in)) &&
             data_at(perr, unsigned char, 7)) ||
            (__return == 0 &&
             pevent != 0 &&
             etype == 4 &&
             isr <= 0 &&
             opt_in == 0 &&
             egrp_in == 0 &&
             UCOS2_Verify_inv(sg, ls_post) &&
             coq_prop(mutex_del_success_post_refinement_prop(
               sg, e, ls0, eid, opt_abs, ls_post)) &&
             coq_prop(mutex_del_owner_restored_prop(e, ls_post.TskState)) &&
             (decode_PCP_from_cnt(ecnt_in) == 255 ||
              coq_prop(prio_tbl_entry_prop(
                ls_post.TskState, decode_PCP_from_cnt(ecnt_in), PTFree))) &&
             data_at(perr, unsigned char, 0)) ||
            (__return == 0 &&
             pevent != 0 &&
             etype == 4 &&
             isr <= 0 &&
             opt_in == 1 &&
             UCOS2_Verify_inv(sg, ls_post) &&
             coq_prop(mutex_del_success_post_refinement_prop(
               sg, e, ls0, eid, opt_abs, ls_post)) &&
             coq_prop(mutex_del_owner_restored_prop(e, ls_post.TskState)) &&
             coq_prop(mutex_del_waiters_aborted_effective_prop(
               e, ls_post.TskState, ls_post.SchedState)) &&
             (decode_PCP_from_cnt(ecnt_in) == 255 ||
              coq_prop(prio_tbl_entry_prop(
                ls_post.TskState, decode_PCP_from_cnt(ecnt_in), PTFree))) &&
             data_at(perr, unsigned char, 0))
        )
*/
{
    BOOLEAN    tasks_waiting;
    OS_EVENT  *pevent_return;
    INT8U      pcp;
    INT8U      prio;
    OS_TCB    *ptcb;
    OS_CPU_SR  cpu_sr;

    if (pevent == (OS_EVENT *)0) {
        *perr = OS_ERR_PEVENT_NULL;
        return (pevent);
    }
    /*@ exists (pevent_v: Z),
        pevent_v == pe &&
        pevent_v == pevent@pre &&
        pevent_v != 0 &&
        coq_prop(mutex_del_input_classification_prop(
          sg, ls0, eid, e, pevent_v, etype, ecnt_in, eptr_in,
          egrp_in, evtL_in, &((OS_EVENT *)pevent_v)->OSEventType,
          &((OS_EVENT *)pevent_v)->OSEventPtr,
          &((OS_EVENT *)pevent_v)->OSEventCnt,
          &((OS_EVENT *)pevent_v)->OSEventGrp,
          ((OS_EVENT *)pevent_v)->OSEventTbl,
          owner_tid, owner_t, owner_prio,
          &((OS_TCB *)eptr_in)->OSTCBPrio, owner_orig, pcp_idx)) &&
        coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
        coq_prop(event_free_list_head_prop(
          sg, ls0.EventState, freelist_in)) &&
        coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) &&
        data_at(&pevent, struct os_event *, pevent_v) *
        UCOS2_Verify_inv(sg, ls0)
        which implies
        pevent_v == pe &&
        pevent_v == pevent@pre &&
        pevent_v != 0 &&
        pevent_v == event_addr(sg, eid) &&
        coq_prop(valid_event_id(sg, eid)) &&
        0 <= etype && etype <= 255 &&
        (etype != 4 ||
         (coq_prop(mutex_del_owner_snapshot_prop(
            sg, ls0, e, eptr_in, owner_tid, owner_t,
            owner_prio, &((OS_TCB *)eptr_in)->OSTCBPrio)) &&
          coq_prop(mutex_del_owner_value_lineage_prop(
            e, ecnt_in, pcp_idx, owner_orig)))) &&
        data_at(&pevent, struct os_event *, pevent_v) *
        data_at(&((OS_EVENT *)pevent_v)->OSEventType, unsigned char, etype) *
        data_at(&((OS_EVENT *)pevent_v)->OSEventPtr, void *, eptr_in) *
        data_at(&((OS_EVENT *)pevent_v)->OSEventCnt, unsigned short, ecnt_in) *
        data_at(&((OS_EVENT *)pevent_v)->OSEventGrp, unsigned char, egrp_in) *
        used_event_wait_table_storage(ls0.TskState, pevent_v, e) *
        data_at(&OSEventFreeList, struct os_event *, freelist_in) *
        mutex_del_event_focus_inv(sg, ls0, eid) *
        coq_prop(event_snapshot_of_prop(
          sg, ls0.TskState, ls0.EventState, eid, e, etype,
          ecnt_in, eptr_in, egrp_in, evtL_in)) *
        coq_prop(event_core_fields_layout_prop(
          sg, eid, &((OS_EVENT *)pevent_v)->OSEventType,
          &((OS_EVENT *)pevent_v)->OSEventPtr,
          &((OS_EVENT *)pevent_v)->OSEventCnt)) *
        coq_prop(event_wait_fields_layout_prop(
          sg, eid, &((OS_EVENT *)pevent_v)->OSEventGrp,
          ((OS_EVENT *)pevent_v)->OSEventTbl)) *
        coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) *
        coq_prop(event_free_list_head_prop(
          sg, ls0.EventState, freelist_in)) *
        coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl))
    */
    if (pevent->OSEventType != OS_EVENT_TYPE_MUTEX) {
        *perr = OS_ERR_EVENT_TYPE;
        return (pevent);
    }
    /*@ mutex_del_event_focus_inv(sg, ls0, eid)
        which implies
        interrupt_inv(sg, ls0.IntrState) *
        mutex_del_event_focus_no_interrupt_inv(sg, ls0, eid)
    */
    /*@ isr == intNesting(ls0.IntrState) &&
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
        interrupt_inv(sg, ls0.IntrState)
        which implies
        isr == intNesting(ls0.IntrState) &&
        data_at(&OSIntNesting, unsigned char, isr) *
        interrupt_inv_no_int_nesting(sg, ls0.IntrState) *
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
    */
    if (OSIntNesting > 0u) {
        *perr = OS_ERR_DEL_ISR;
        /*@ isr == intNesting(ls0.IntrState) &&
            data_at(&OSIntNesting, unsigned char, isr) *
            interrupt_inv_no_int_nesting(sg, ls0.IntrState) *
            coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
            which implies
            isr == intNesting(ls0.IntrState) &&
            interrupt_inv(sg, ls0.IntrState) *
            coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
        */
        /*@ isr == intNesting(ls0.IntrState) &&
            interrupt_inv(sg, ls0.IntrState) *
            mutex_del_event_focus_no_interrupt_inv(sg, ls0, eid) *
            coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
            which implies
            isr == intNesting(ls0.IntrState) &&
            mutex_del_event_focus_inv(sg, ls0, eid) *
            coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
        */
        return (pevent);
    }
    /*@ isr == intNesting(ls0.IntrState) && isr <= 0 &&
        data_at(&OSIntNesting, unsigned char, isr) *
        interrupt_inv_no_int_nesting(sg, ls0.IntrState) *
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
        which implies
        isr == intNesting(ls0.IntrState) && isr <= 0 &&
        interrupt_inv(sg, ls0.IntrState) *
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
    */
    /*@ isr == intNesting(ls0.IntrState) && isr <= 0 &&
        interrupt_inv(sg, ls0.IntrState) *
        mutex_del_event_focus_no_interrupt_inv(sg, ls0, eid) *
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
        which implies
        isr == intNesting(ls0.IntrState) && isr <= 0 &&
        mutex_del_event_focus_inv(sg, ls0, eid) *
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
    */
    /*@ Assert
        coq_prop(mutex_del_return_lineage_prop(
          sg, e, ls0, eid, pe, pd, pevent, perr,
          pevent@pre, perr@pre, etype, isr, opt_in, opt_abs,
          ecnt_in, eptr_in, egrp_in, evtL_in)) *
        coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) *
        undef_data_at(&tasks_waiting, unsigned char) *
        undef_data_at(&pevent_return, struct os_event *) *
        undef_data_at(&pcp, unsigned char) *
        undef_data_at(&prio, unsigned char) *
        undef_data_at(&ptcb, struct os_tcb *) *
        undef_data_at(&cpu_sr, unsigned int) *
        data_at(perr, unsigned char, perr_in) *
        data_at(&pevent->OSEventType, unsigned char, etype) *
        data_at(&pevent->OSEventPtr, void *, eptr_in) *
        data_at(&pevent->OSEventCnt, unsigned short, ecnt_in) *
        data_at(&pevent->OSEventGrp, unsigned char, egrp_in) *
        used_event_wait_table_storage(ls0.TskState, pevent, e) *
        data_at(&OSEventFreeList, struct os_event *, freelist_in) *
        mutex_del_event_focus_inv(sg, ls0, eid) *
        coq_prop(event_snapshot_of_prop(
          sg, ls0.TskState, ls0.EventState, eid, e, 4,
          ecnt_in, eptr_in, egrp_in, evtL_in)) *
        coq_prop(event_core_fields_layout_prop(
          sg, eid, &pevent->OSEventType,
          &pevent->OSEventPtr, &pevent->OSEventCnt)) *
        coq_prop(event_wait_fields_layout_prop(
          sg, eid, &pevent->OSEventGrp, pevent->OSEventTbl)) *
        coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) *
        coq_prop(event_free_list_head_prop(
          sg, ls0.EventState, freelist_in)) *
        coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) *
        coq_prop(valid_event_id(sg, eid)) *
        coq_prop(mutex_del_owner_snapshot_prop(
          sg, ls0, e, eptr_in, owner_tid, owner_t, owner_prio,
          &((OS_TCB *)eptr_in)->OSTCBPrio)) *
        coq_prop(mutex_del_owner_value_lineage_prop(
          e, ecnt_in, pcp_idx, owner_orig)) *
        coq_prop(prio_tbl_list_rel(sg, ls0.TskState, prioL_in)) *
        OutsideCritical(sg, ls0) &&
        isr == intNesting(ls0.IntrState) && isr <= 0 &&
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
        Znth(pcp_idx, prioL_in, 0) == prio_tbl_pcp &&
        pe == pevent && pevent == event_addr(sg, eid) &&
        pd == perr && opt == opt_in && etype == 4 &&
        coq_prop(mutex_del_option_decode_prop(opt_in, opt_abs)) &&
        safeExec(LastSeen(ls0),
                 bind(atomic_cmd(OSMutexDel_full_sem(sg, pevent, opt_abs)),
                      mutex_del_observe_ptr(pevent)), X)
    */
    OS_ENTER_CRITICAL()/*@ where sg = sg, ls0 = ls0, eid = eid */;
    if (pevent->OSEventGrp != 0u) {
        tasks_waiting = OS_TRUE;
    } else {
        tasks_waiting = OS_FALSE;
    }
    /*@ Assert
        exists (cpu_sr_v: Z) (tasks_v: Z),
          coq_prop(mutex_del_return_lineage_prop(
            sg, e, ls0, eid, pe, pd, pevent, perr,
            pevent@pre, perr@pre, etype, isr, opt_in, opt_abs,
            ecnt_in, eptr_in, egrp_in, evtL_in)) &&
          coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) &&
          safeExec(LastSeen(ls0),
                   bind(atomic_cmd(OSMutexDel_full_sem(sg, pevent, opt_abs)),
                        mutex_del_observe_ptr(pevent)), X) &&
          InsideCritical(sg, ls0) &&
          isr == intNesting(ls0.IntrState) && isr <= 0 &&
          coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
          mutex_del_event_focus_inv(sg, ls0, eid) &&
          pevent == event_addr(sg, eid) &&
          coq_prop(valid_event_id(sg, eid)) &&
          coq_prop(event_snapshot_of_prop(
            sg, ls0.TskState, ls0.EventState, eid, e, 4,
            ecnt_in, eptr_in, egrp_in, evtL_in)) &&
          coq_prop(event_core_fields_layout_prop(
            sg, eid, &pevent->OSEventType,
            &pevent->OSEventPtr, &pevent->OSEventCnt)) &&
          coq_prop(event_wait_fields_layout_prop(
            sg, eid, &pevent->OSEventGrp, pevent->OSEventTbl)) &&
          coq_prop(mutex_del_source_entry_prop(
            sg, e, ls0, eid, pevent, tasks_v)) &&
          coq_prop(mutex_del_owner_snapshot_prop(
            sg, ls0, e, eptr_in, owner_tid, owner_t, owner_prio,
            &((OS_TCB *)eptr_in)->OSTCBPrio)) &&
          coq_prop(mutex_del_owner_value_lineage_prop(
            e, ecnt_in, pcp_idx, owner_orig)) &&
          coq_prop(mutex_del_owner_value_lineage_prop(
            e, ecnt_in,
            unsigned_last_nbits(ecnt_in >> 8u, 8),
            ecnt_in & OS_MUTEX_KEEP_LOWER_8)) &&
          pcp_idx == unsigned_last_nbits(ecnt_in >> 8u, 8) &&
          owner_orig ==
            (INT8U)(ecnt_in & OS_MUTEX_KEEP_LOWER_8) &&
          data_at(&OSEventFreeList, struct os_event *, freelist_in) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          coq_prop(event_free_list_head_prop(
            sg, ls0.EventState, freelist_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          opt == opt_in &&
          coq_prop(mutex_del_option_decode_prop(opt_in, opt_abs)) &&
          data_at(perr, unsigned char, perr_in) &&
          data_at(&pevent->OSEventType, 4) &&
          data_at(&pevent->OSEventCnt, ecnt_in) &&
          data_at(&pevent->OSEventPtr, eptr_in) &&
          data_at(&pevent->OSEventGrp, egrp_in) &&
          used_event_wait_table_storage(ls0.TskState, pevent, e) &&
          data_at(&tasks_waiting, unsigned char, tasks_v) &&
          undef_data_at(&pevent_return, struct os_event *) &&
          data_at(&cpu_sr, unsigned int, cpu_sr_v) &&
          undef_data_at(&pcp, unsigned char) &&
          undef_data_at(&prio, unsigned char) &&
          undef_data_at(&ptcb, struct os_tcb *) &&
          coq_prop(prio_tbl_list_rel(sg, ls0.TskState, prioL_in)) &&
          Znth(pcp_idx, prioL_in, 0) == prio_tbl_pcp
    */
    switch (opt) {
        case OS_DEL_NO_PEND:
             if (tasks_waiting == OS_FALSE) {
                  pcp = (INT8U)(pevent->OSEventCnt >> 8u);
                  if (pcp != OS_PRIO_MUTEX_CEIL_DIS) {
                      prio = (INT8U)(pevent->OSEventCnt & OS_MUTEX_KEEP_LOWER_8);
                      ptcb = (OS_TCB *)pevent->OSEventPtr;
                      if (ptcb != (OS_TCB *)0) {
                          /*@
                              eptr_in != 0 &&
                              pcp != 255 &&
                              mutex_del_event_focus_inv(sg, ls0, eid) &&
                              coq_prop(mutex_del_owner_snapshot_prop(
                                sg, ls0, e, eptr_in, owner_tid, owner_t,
                                owner_prio,
                                &((OS_TCB *)eptr_in)->OSTCBPrio)) &&
                              eptr_in != 0
                              which implies
                              data_at(&((OS_TCB *)eptr_in)->OSTCBPrio,
                                      unsigned char, owner_prio) *
                              mutex_del_event_owner_open_inv(
                                sg, ls0, eid, owner_tid, owner_t) *
                              coq_prop(mutex_del_owner_snapshot_prop(
                                sg, ls0, e, eptr_in, owner_tid, owner_t,
                                owner_prio,
                                &((OS_TCB *)eptr_in)->OSTCBPrio)) &&
                              pcp != 255
                          */
                          if (ptcb->OSTCBPrio == pcp) {
                              /*@
                                  data_at(&((OS_TCB *)eptr_in)->OSTCBPrio,
                                          unsigned char, owner_prio) *
                                  mutex_del_event_owner_open_inv(
                                    sg, ls0, eid, owner_tid, owner_t) *
                                  coq_prop(mutex_del_owner_snapshot_prop(
                                    sg, ls0, e, eptr_in, owner_tid, owner_t,
                                    owner_prio,
                                    &((OS_TCB *)eptr_in)->OSTCBPrio)) &&
                                  eptr_in != 0 && pcp != 255
                                  which implies
                                  mutex_del_event_focus_inv(sg, ls0, eid) *
                                  coq_prop(mutex_del_owner_snapshot_prop(
                                    sg, ls0, e, eptr_in, owner_tid, owner_t,
                                    owner_prio,
                                    &((OS_TCB *)eptr_in)->OSTCBPrio)) &&
                                  eptr_in != 0 && pcp != 255
                              */
                              OSMutex_RdyAtPrio(ptcb, prio)
                              /*@ where sg = sg, ls = ls0, eid = eid,
                                        owner_tid = owner_tid,
                                        owner_t_abs = owner_t, e_abs = e,
                                        owner_prio_abs = owner_prio,
                                        ecnt_abs = ecnt_in, pcp_abs = pcp */;
                          }
                      }
                      /*@ Assert
                          exists (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z)
                                 (prio_v: Z) (ptcb_v: Z),
                            coq_prop(mutex_del_return_lineage_prop(
                              sg, e, ls0, eid, pe, pd, pevent, perr,
                              pevent@pre, perr@pre, etype, isr,
                              opt_in, opt_abs, ecnt_in, eptr_in,
                              egrp_in, evtL_in)) &&
                            coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) &&
                            pcp_v != 255 &&
                            coq_prop(mutex_del_owner_value_lineage_prop(
                              e, ecnt_in, pcp_v, prio_v)) &&
                            mutex_del_owner_stage_focus(
                              sg, e, ls0, eid) &&
                            coq_prop(mutex_del_source_entry_prop(
                              sg, e, ls0, eid, pevent, tasks_v)) &&
                            coq_prop(mutex_del_success_mode_prop(
                              opt_abs, tasks_v)) &&
                            coq_prop(mutex_del_no_pend_mode_prop(
                              opt_abs, tasks_v)) &&
                            pevent == event_addr(sg, eid) &&
                            coq_prop(valid_event_id(sg, eid)) &&
                            coq_prop(event_snapshot_of_prop(
                              sg, ls0.TskState, ls0.EventState, eid, e, 4,
                              ecnt_in, eptr_in, 0, evtL_in)) &&
                            coq_prop(event_core_fields_layout_prop(
                              sg, eid, &pevent->OSEventType,
                              &pevent->OSEventPtr,
                              &pevent->OSEventCnt)) &&
                            coq_prop(event_wait_fields_layout_prop(
                              sg, eid, &pevent->OSEventGrp,
                              pevent->OSEventTbl)) &&
                            coq_prop(os_event_free_list_addr(
                              sg, &OSEventFreeList)) &&
                            coq_prop(os_tcb_prio_tbl_addr(
                              sg, OSTCBPrioTbl)) &&
                            coq_prop(event_free_list_head_prop(
                              sg, ls0.EventState, freelist_in)) &&
                            data_at(&pevent->OSEventType, 4) &&
                            data_at(&pevent->OSEventCnt, ecnt_in) &&
                            data_at(&pevent->OSEventPtr, eptr_in) &&
                            data_at(&pevent->OSEventGrp, 0) &&
                            used_event_wait_table_storage(
                              ls0.TskState, pevent, e) &&
                            data_at(&OSEventFreeList,
                                    struct os_event *, freelist_in) &&
                            data_at(perr, unsigned char, perr_in) &&
                            data_at(&cpu_sr, unsigned int, cpu_sr_v) &&
                            data_at(&tasks_waiting,
                                    unsigned char, tasks_v) &&
                            data_at(&opt, unsigned char, opt_in) &&
                            undef_data_at(&pevent_return,
                                          struct os_event *) &&
                            data_at(&pcp, unsigned char, pcp_v) &&
                            data_at(&prio, unsigned char, prio_v) &&
                            data_at(&ptcb, struct os_tcb *, ptcb_v) &&
                            safeExec(LastSeen(ls0),
                              bind(atomic_cmd(OSMutexDel_full_sem(
                                     sg, pevent, opt_abs)),
                                   mutex_del_observe_ptr(pevent)), X)
                      */
                      /*@
                          0 <= pcp && pcp < 64 &&
                      coq_prop(event_core_fields_layout_prop(
                        sg, eid, &pevent->OSEventType,
                        &pevent->OSEventPtr,
                        &pevent->OSEventCnt)) *
                      coq_prop(event_wait_fields_layout_prop(
                        sg, eid, &pevent->OSEventGrp,
                        pevent->OSEventTbl)) *
                      coq_prop(os_event_free_list_addr(
                        sg, &OSEventFreeList)) *
                      coq_prop(os_tcb_prio_tbl_addr(
                        sg, OSTCBPrioTbl)) *
                      coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) *
                      mutex_del_owner_stage_focus(sg, e, ls0, eid) *
                      data_at(&opt, unsigned char, opt_in)
                      which implies
                          exists (owner_post: UCOS2_Verify_State)
                                 (old_pcp_cell: Z),
                          InsideCritical(sg, owner_post) *
                          data_at(pointer_offset(
                                    OSTCBPrioTbl, pcp, OS_TCB *),
                                  OS_TCB *, old_pcp_cell) *
                          mutex_del_event_missing_priotbl_focus(
                            sg, ls0, owner_post, eid, pcp) *
                          coq_prop(mutex_del_rdyatprio_stage_prop(
                            sg, e, ls0, owner_post)) *
                          coq_prop(event_core_fields_layout_prop(
                            sg, eid, &pevent->OSEventType,
                            &pevent->OSEventPtr,
                            &pevent->OSEventCnt)) *
                          coq_prop(event_wait_fields_layout_prop(
                            sg, eid, &pevent->OSEventGrp,
                            pevent->OSEventTbl)) *
                          coq_prop(os_event_free_list_addr(
                            sg, &OSEventFreeList)) *
                          coq_prop(os_tcb_prio_tbl_addr(
                            sg, OSTCBPrioTbl)) *
                          coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) *
                          data_at(&opt, unsigned char, opt_in)
                      */
                      OSTCBPrioTbl[pcp] = (OS_TCB *)0;
                  }
                  /*@ Assert
                      exists (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z),
                        coq_prop(mutex_del_return_lineage_prop(
                          sg, e, ls0, eid, pe, pd, pevent, perr,
                          pevent@pre, perr@pre, etype, isr,
                          opt_in, opt_abs, ecnt_in, eptr_in,
                          egrp_in, evtL_in)) &&
                        coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) &&
                        mutex_del_no_pend_pcp_release_residual(
                          sg, e, ls0, eid, pevent,
                          ecnt_in, eptr_in, 0, pcp_v, freelist_in) &&
                        coq_prop(mutex_del_source_entry_prop(
                          sg, e, ls0, eid, pevent, tasks_v)) &&
                        coq_prop(mutex_del_success_mode_prop(
                          opt_abs, tasks_v)) &&
                        coq_prop(mutex_del_no_pend_mode_prop(
                          opt_abs, tasks_v)) &&
                        coq_prop(event_core_fields_layout_prop(
                          sg, eid, &pevent->OSEventType,
                          &pevent->OSEventPtr,
                          &pevent->OSEventCnt)) &&
                        coq_prop(event_wait_fields_layout_prop(
                          sg, eid, &pevent->OSEventGrp,
                          pevent->OSEventTbl)) &&
                        coq_prop(os_event_free_list_addr(
                          sg, &OSEventFreeList)) &&
                        coq_prop(os_tcb_prio_tbl_addr(
                          sg, OSTCBPrioTbl)) &&
                        data_at(&opt, unsigned char, opt_in) &&
                        data_at(&pevent->OSEventCnt, ecnt_in) &&
                        data_at(&pevent->OSEventGrp, 0) &&
                        data_at(&OSEventFreeList,
                                struct os_event *, freelist_in) &&
                        data_at(&cpu_sr, unsigned int, cpu_sr_v) &&
                        data_at(&tasks_waiting,
                                unsigned char, tasks_v) &&
                        undef_data_at(&pevent_return,
                                      struct os_event *) &&
                        data_at(&pcp, unsigned char, pcp_v) &&
                        undef_data_at(&prio, unsigned char) &&
                        undef_data_at(&ptcb, struct os_tcb *) &&
                        data_at(perr, unsigned char, perr_in) &&
                        safeExec(LastSeen(ls0),
                          bind(atomic_cmd(OSMutexDel_full_sem(
                                 sg, pevent, opt_abs)),
                               mutex_del_observe_ptr(pevent)), X)
                  */
                  /*@
                      exists (tasks_v: Z),
                      coq_prop(mutex_del_source_entry_prop(
                        sg, e, ls0, eid, pevent, tasks_v)) *
                      coq_prop(mutex_del_no_pend_mode_prop(
                        opt_abs, tasks_v)) *
                      coq_prop(event_core_fields_layout_prop(
                        sg, eid, &pevent->OSEventType,
                        &pevent->OSEventPtr,
                        &pevent->OSEventCnt)) *
                      coq_prop(event_wait_fields_layout_prop(
                        sg, eid, &pevent->OSEventGrp,
                        pevent->OSEventTbl)) *
                      coq_prop(os_event_free_list_addr(
                        sg, &OSEventFreeList)) *
                      mutex_del_no_pend_pcp_release_residual(
                        sg, e, ls0, eid, pevent,
                        ecnt_in, eptr_in, 0, pcp, freelist_in) &&
                      coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) *
                      data_at(&tasks_waiting,
                              unsigned char, tasks_v) *
                      data_at(&opt, unsigned char, opt_in) *
                      safeExec(LastSeen(ls0),
                        bind(atomic_cmd(OSMutexDel_full_sem(
                               sg, pevent, opt_abs)),
                             mutex_del_observe_ptr(pevent)), X)
                      which implies
                      exists (owner_post: UCOS2_Verify_State)
                             (current_event: OSEventAbstractState)
                             (current_tbl: list Z) (old_type: Z)
                             (tasks_v: Z),
                        pcp == decode_PCP_from_cnt(ecnt_in) &&
                        InsideCritical(sg, owner_post) *
                        mutex_del_pcp_release_focus(
                          sg, ls0, owner_post, eid, pcp) *
                        data_at(&pevent->OSEventType,
                                unsigned char, old_type) *
                        data_at(&pevent->OSEventPtr,
                                void *, eptr_in) *
                        used_event_wait_table_storage(
                          owner_post.TskState, pevent, current_event) *
                        coq_prop(mutex_del_rdyatprio_stage_prop(
                          sg, e, ls0, owner_post)) *
                        coq_prop(event_free_list_head_prop(
                          sg, owner_post.EventState, freelist_in)) *
                        coq_prop(event_snapshot_of_prop(
                          sg, owner_post.TskState, owner_post.EventState,
                          eid, current_event, old_type,
                          ecnt_in, eptr_in, 0, current_tbl)) *
                        coq_prop(mutex_del_source_entry_prop(
                          sg, e, ls0, eid, pevent, tasks_v)) *
                        coq_prop(mutex_del_no_pend_mode_prop(
                          opt_abs, tasks_v)) *
                        coq_prop(event_core_fields_layout_prop(
                          sg, eid, &pevent->OSEventType,
                          &pevent->OSEventPtr,
                          &pevent->OSEventCnt)) *
                        coq_prop(event_wait_fields_layout_prop(
                          sg, eid, &pevent->OSEventGrp,
                          pevent->OSEventTbl)) *
                        coq_prop(os_event_free_list_addr(
                          sg, &OSEventFreeList)) *
                        coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) *
                        data_at(&tasks_waiting,
                                unsigned char, tasks_v) *
                        data_at(&opt, unsigned char, opt_in) *
                        coq_prop(safeExec(
                          LastSeen(ls0),
                          bind(atomic_cmd(OSMutexDel_full_sem(
                                 sg, pevent, opt_abs)),
                               mutex_del_observe_ptr(pevent)), X))
                  */
                  pevent->OSEventType = OS_EVENT_TYPE_UNUSED;
                  pevent->OSEventPtr  = OSEventFreeList;
                  pevent->OSEventCnt  = 0u;
                  OSEventFreeList     = pevent;
                  /*@ Assert
                      exists (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z),
                        coq_prop(mutex_del_return_lineage_prop(
                          sg, e, ls0, eid, pe, pd, pevent, perr,
                          pevent@pre, perr@pre, etype, isr,
                          opt_in, opt_abs, ecnt_in, eptr_in,
                          egrp_in, evtL_in)) &&
                        coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) &&
                        mutex_del_success_commit_inv(
                          sg, e, ls0, eid, opt_abs,
                          pevent, tasks_v, X) &&
                        coq_prop(mutex_del_no_pend_mode_prop(
                          opt_abs, tasks_v)) &&
                        data_at(&opt, unsigned char, opt_in) &&
                        data_at(&cpu_sr, unsigned int, cpu_sr_v) &&
                        data_at(&tasks_waiting,
                                unsigned char, tasks_v) &&
                        undef_data_at(&pevent_return,
                                      struct os_event *) &&
                        data_at(&pcp, unsigned char, pcp_v) &&
                        undef_data_at(&prio, unsigned char) &&
                        undef_data_at(&ptcb, struct os_tcb *) &&
                        data_at(perr, unsigned char, perr_in)
                 */
                 /*@
                     coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) *
                     mutex_del_success_commit_inv(
                       sg, e, ls0, eid, opt_abs,
                       pevent, tasks_waiting, X)
                     which implies
                     exists (critical_anchor: UCOS2_Verify_State)
                            (ls_commit: UCOS2_Verify_State),
                       InsideCritical(sg, critical_anchor) *
                       mutex_del_transition_rep(sg, ls0, ls_commit) *
                       coq_prop(mutex_del_success_commit_anchor_prop(
                         sg, e, ls0, eid, opt_abs,
                         critical_anchor, ls_commit)) *
                       coq_prop(mutex_del_source_entry_prop(
                         sg, e, ls0, eid, pevent, tasks_waiting)) *
                       coq_prop(mutex_del_success_mode_prop(
                         opt_abs, tasks_waiting)) *
                       coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) *
                       coq_prop(safeExec(
                         LastSeen(ls0),
                         bind(atomic_cmd(OSMutexDel_full_sem(
                                sg, pevent, opt_abs)),
                              mutex_del_observe_ptr(pevent)), X))
                 */
                 OSMutexDel_RefreshHighReady()
                   /*@ where sg = sg, entry = ls0 */;
                 OS_EXIT_CRITICAL()
                   /*@ where sg = sg, entry = ls0,
                              raw_stage = false */;
                 /*@ Assert
                     exists (perr_v: Z) (tasks_v: Z) (pcp_v: Z)
                            (cpu_sr_v: Z),
                       coq_prop(mutex_del_return_lineage_prop(
                         sg, e, ls0, eid, pe, pd, pevent, perr,
                         pevent@pre, perr@pre, etype, isr,
                         opt_in, opt_abs, ecnt_in, eptr_in,
                         egrp_in, evtL_in)) &&
                       mutex_del_no_pend_exit_inv(
                         sg, e, ls0, eid, opt_abs,
                         pevent, tasks_v, X) &&
                       data_at(perr, unsigned char, perr_v) &&
                       undef_data_at(&pevent_return, struct os_event *) &&
                       data_at(&tasks_waiting,
                               unsigned char, tasks_v) &&
                       data_at(&opt, unsigned char, opt_in) &&
                       data_at(&pcp, unsigned char, pcp_v) &&
                       undef_data_at(&prio, unsigned char) &&
                       undef_data_at(&ptcb, struct os_tcb *) &&
                       data_at(&cpu_sr, unsigned int, cpu_sr_v)
                 */
                *perr                 = OS_ERR_NONE;
                 pevent_return        = (OS_EVENT *)0;
             } else {
                 /*@ Assert
                     exists (cpu_sr_v: Z) (tasks_v: Z),
                       coq_prop(mutex_del_return_lineage_prop(
                         sg, e, ls0, eid, pe, pd, pevent, perr,
                         pevent@pre, perr@pre, etype, isr,
                         opt_in, opt_abs, ecnt_in, eptr_in,
                         egrp_in, evtL_in)) &&
                       mutex_del_unchanged_inside_inv(
                         sg, e, ls0, eid, pevent, opt_abs,
                         tasks_v, 73, X) &&
                       data_at(&cpu_sr, unsigned int, cpu_sr_v) &&
                       data_at(&tasks_waiting,
                               unsigned char, tasks_v) &&
                       undef_data_at(&pevent_return,
                                     struct os_event *) &&
                       undef_data_at(&pcp, unsigned char) &&
                       undef_data_at(&prio, unsigned char) &&
                       undef_data_at(&ptcb, struct os_tcb *) &&
                       data_at(perr, unsigned char, perr_in)
                 */
                 /*@
                     mutex_del_unchanged_inside_inv(
                       sg, e, ls0, eid, pevent, opt_abs,
                       tasks_waiting, 73, X)
                     which implies
                       InsideCritical(sg, ls0) *
                       mutex_del_restore_rep(false, sg, ls0, ls0) *
                       coq_prop(mutex_del_source_entry_prop(
                         sg, e, ls0, eid, pevent, tasks_waiting)) *
                       coq_prop(mutex_del_error_mode_prop(
                         opt_abs, tasks_waiting, 73)) *
                       coq_prop(safeExec(
                         LastSeen(ls0),
                         bind(atomic_cmd(OSMutexDel_full_sem(
                                sg, pevent, opt_abs)),
                              mutex_del_observe_ptr(pevent)), X))
                 */
                 OS_EXIT_CRITICAL()/*@ where sg = sg, entry = ls0,
                                              raw_stage = false,
                                              critical_anchor = ls0,
                                              logical_post = ls0 */;
                 /*@ Assert
                     exists (perr_v: Z) (tasks_v: Z) (cpu_sr_v: Z),
                       coq_prop(mutex_del_return_lineage_prop(
                         sg, e, ls0, eid, pe, pd, pevent, perr,
                         pevent@pre, perr@pre, etype, isr,
                         opt_in, opt_abs, ecnt_in, eptr_in,
                         egrp_in, evtL_in)) &&
                       mutex_del_unchanged_exit_inv(
                         sg, e, ls0, eid, pevent, opt_abs,
                         tasks_v, 73, X) &&
                       data_at(perr, unsigned char, perr_v) &&
                       undef_data_at(&pevent_return, struct os_event *) &&
                       data_at(&tasks_waiting,
                               unsigned char, tasks_v) &&
                       undef_data_at(&pcp, unsigned char) &&
                       undef_data_at(&prio, unsigned char) &&
                       undef_data_at(&ptcb, struct os_tcb *) &&
                       data_at(&cpu_sr, unsigned int, cpu_sr_v)
                 */
                *perr                 = OS_ERR_TASK_WAITING;
                 pevent_return        = pevent;
             }
             break;

        case OS_DEL_ALWAYS:
             pcp  = (INT8U)(pevent->OSEventCnt >> 8u);
             if (pcp != OS_PRIO_MUTEX_CEIL_DIS) {
                 prio = (INT8U)(pevent->OSEventCnt & OS_MUTEX_KEEP_LOWER_8);
                 ptcb = (OS_TCB *)pevent->OSEventPtr;
                 if (ptcb != (OS_TCB *)0) {
                     /*@
                         eptr_in != 0 &&
                         pcp != 255 &&
                         mutex_del_event_focus_inv(sg, ls0, eid) &&
                         coq_prop(mutex_del_owner_snapshot_prop(
                           sg, ls0, e, eptr_in, owner_tid, owner_t,
                           owner_prio,
                           &((OS_TCB *)eptr_in)->OSTCBPrio)) &&
                         eptr_in != 0
                         which implies
                         data_at(&((OS_TCB *)eptr_in)->OSTCBPrio,
                                 unsigned char, owner_prio) *
                         mutex_del_event_owner_open_inv(
                           sg, ls0, eid, owner_tid, owner_t) *
                         coq_prop(mutex_del_owner_snapshot_prop(
                           sg, ls0, e, eptr_in, owner_tid, owner_t,
                           owner_prio,
                           &((OS_TCB *)eptr_in)->OSTCBPrio)) &&
                         pcp != 255
                     */
                     if (ptcb->OSTCBPrio == pcp) {
                         /*@
                             data_at(&((OS_TCB *)eptr_in)->OSTCBPrio,
                                     unsigned char, owner_prio) *
                             mutex_del_event_owner_open_inv(
                               sg, ls0, eid, owner_tid, owner_t) *
                             coq_prop(mutex_del_owner_snapshot_prop(
                               sg, ls0, e, eptr_in, owner_tid, owner_t,
                               owner_prio,
                               &((OS_TCB *)eptr_in)->OSTCBPrio)) &&
                             eptr_in != 0 && pcp != 255
                             which implies
                             mutex_del_event_focus_inv(sg, ls0, eid) *
                             coq_prop(mutex_del_owner_snapshot_prop(
                               sg, ls0, e, eptr_in, owner_tid, owner_t,
                               owner_prio,
                               &((OS_TCB *)eptr_in)->OSTCBPrio)) &&
                             eptr_in != 0 && pcp != 255
                         */
                         OSMutex_RdyAtPrio(ptcb, prio)
                         /*@ where sg = sg, ls = ls0, eid = eid,
                                   owner_tid = owner_tid,
                                   owner_t_abs = owner_t, e_abs = e,
                                   owner_prio_abs = owner_prio,
                                   ecnt_abs = ecnt_in, pcp_abs = pcp */;
                     }
                 }
             }
             /*@ Assert
                 exists (ls_owner_cur: UCOS2_Verify_State)
                        (ls_loop: UCOS2_Verify_State)
                        (e_loop: OSEventAbstractState)
                        (evtL_loop: list Z)
                        (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z),
                   coq_prop(mutex_del_return_lineage_prop(
                     sg, e, ls0, eid, pe, pd, pevent, perr,
                     pevent@pre, perr@pre, etype, isr,
                     opt_in, opt_abs, ecnt_in, eptr_in,
                     egrp_in, evtL_in)) &&
                   coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) &&
                   InsideCritical(sg, ls_loop) &&
                   mutex_del_event_ready_focus_inv(
                     sg, ls0, ls_loop, eid) &&
                   coq_prop(mutex_del_rdyatprio_stage_prop(
                     sg, e, ls0, ls_owner_cur)) &&
                   coq_prop(mutex_del_wake_steps(
                     sg, eid, ls_owner_cur, ls_loop)) &&
                   coq_prop(event_free_list_head_prop(
                     sg, ls_loop.EventState, freelist_in)) &&
                   coq_prop(mutex_del_source_entry_prop(
                     sg, e, ls0, eid, pevent, tasks_v)) &&
                   coq_prop(mutex_del_success_mode_prop(
                     opt_abs, tasks_v)) &&
                   coq_prop(mutex_del_always_mode_prop(
                     opt_abs, tasks_v)) &&
                   pevent == event_addr(sg, eid) &&
                   coq_prop(valid_event_id(sg, eid)) &&
                   coq_prop(event_snapshot_of_prop(
                     sg, ls_loop.TskState, ls_loop.EventState,
                     eid, e_loop, 4, ecnt_in, eptr_in,
                     egrp_in, evtL_loop)) &&
                   coq_prop(event_core_fields_layout_prop(
                     sg, eid, &pevent->OSEventType,
                     &pevent->OSEventPtr,
                     &pevent->OSEventCnt)) &&
                   coq_prop(event_wait_fields_layout_prop(
                     sg, eid, &pevent->OSEventGrp,
                     pevent->OSEventTbl)) &&
                   coq_prop(os_event_free_list_addr(
                     sg, &OSEventFreeList)) &&
                   coq_prop(os_tcb_prio_tbl_addr(
                     sg, OSTCBPrioTbl)) &&
                   data_at(&pevent->OSEventType, 4) &&
                   data_at(&pevent->OSEventCnt, ecnt_in) &&
                   data_at(&pevent->OSEventPtr, eptr_in) &&
                   data_at(&pevent->OSEventGrp, egrp_in) &&
                   used_event_wait_table_storage(
                     ls_loop.TskState, pevent, e_loop) &&
                   data_at(&cpu_sr, unsigned int, cpu_sr_v) &&
                   data_at(&tasks_waiting, unsigned char, tasks_v) &&
                   data_at(&opt, unsigned char, opt_in) &&
                   undef_data_at(&pevent_return, struct os_event *) &&
                   data_at(&pcp, unsigned char, pcp_v) &&
                   undef_data_at(&prio, unsigned char) &&
                   undef_data_at(&ptcb, struct os_tcb *) &&
                   data_at(perr, unsigned char, perr_in) &&
                   data_at(&OSEventFreeList, struct os_event *, freelist_in) &&
                   safeExec(LastSeen(ls0),
                     bind(atomic_cmd(OSMutexDel_full_sem(
                            sg, pevent, opt_abs)),
                          mutex_del_observe_ptr(pevent)), X)
             */
             /*@ Inv Assert
                 exists (ls_owner_cur: UCOS2_Verify_State)
                        (ls_loop: UCOS2_Verify_State)
                        (e_loop: OSEventAbstractState)
                        (evtL_loop: list Z) (egrp_loop: Z)
                        (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z),
                   coq_prop(mutex_del_return_lineage_prop(
                     sg, e, ls0, eid, pe, pd, pevent, perr,
                     pevent@pre, perr@pre, etype, isr,
                     opt_in, opt_abs, ecnt_in, eptr_in,
                     egrp_in, evtL_in)) &&
                   coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) &&
                   InsideCritical(sg, ls_loop) &&
                   mutex_del_event_ready_focus_inv(
                     sg, ls0, ls_loop, eid) &&
                   coq_prop(mutex_del_rdyatprio_stage_prop(
                     sg, e, ls0, ls_owner_cur)) &&
                   coq_prop(mutex_del_wake_steps(
                     sg, eid, ls_owner_cur, ls_loop)) &&
                   coq_prop(event_free_list_head_prop(
                     sg, ls_loop.EventState, freelist_in)) &&
                   coq_prop(mutex_del_source_entry_prop(
                     sg, e, ls0, eid, pevent, tasks_v)) &&
                   coq_prop(mutex_del_success_mode_prop(
                     opt_abs, tasks_v)) &&
                   coq_prop(mutex_del_always_mode_prop(
                     opt_abs, tasks_v)) &&
                   pevent == event_addr(sg, eid) &&
                   coq_prop(valid_event_id(sg, eid)) &&
                   coq_prop(event_snapshot_of_prop(
                     sg, ls_loop.TskState, ls_loop.EventState,
                     eid, e_loop, 4, ecnt_in, eptr_in,
                     egrp_loop, evtL_loop)) &&
                   coq_prop(event_core_fields_layout_prop(
                     sg, eid, &pevent->OSEventType,
                     &pevent->OSEventPtr,
                     &pevent->OSEventCnt)) &&
                   coq_prop(event_wait_fields_layout_prop(
                     sg, eid, &pevent->OSEventGrp,
                     pevent->OSEventTbl)) &&
                   coq_prop(os_event_free_list_addr(
                     sg, &OSEventFreeList)) &&
                   coq_prop(os_tcb_prio_tbl_addr(
                     sg, OSTCBPrioTbl)) &&
                   data_at(&pevent->OSEventType, 4) &&
                   data_at(&pevent->OSEventCnt, ecnt_in) &&
                   data_at(&pevent->OSEventPtr, eptr_in) &&
                   data_at(&pevent->OSEventGrp, egrp_loop) &&
                   used_event_wait_table_storage(
                     ls_loop.TskState, pevent, e_loop) &&
                   data_at(&cpu_sr, unsigned int, cpu_sr_v) &&
                   data_at(&tasks_waiting, unsigned char, tasks_v) &&
                   data_at(&opt, unsigned char, opt_in) &&
                   undef_data_at(&pevent_return, struct os_event *) &&
                   data_at(&pcp, unsigned char, pcp_v) &&
                   undef_data_at(&prio, unsigned char) &&
                   undef_data_at(&ptcb, struct os_tcb *) &&
                   data_at(perr, unsigned char, perr_in) &&
                   data_at(&OSEventFreeList, struct os_event *, freelist_in) &&
                   safeExec(LastSeen(ls0),
                     bind(atomic_cmd(OSMutexDel_full_sem(
                            sg, pevent, opt_abs)),
                          mutex_del_observe_ptr(pevent)), X)
             */
             while (pevent->OSEventGrp != 0u) {
                 (void)OS_EventTaskRdy(pevent, (void *)0, OS_STAT_MUTEX, OS_STAT_PEND_ABORT)
                 /*@ where sg = sg, eid = eid, anchor = ls0,
                           etype_abs = 4, ecnt_abs = ecnt_in,
                           eptr_abs = eptr_in */;
             }
             /*@ Assert
                 exists (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z),
                   coq_prop(mutex_del_return_lineage_prop(
                     sg, e, ls0, eid, pe, pd, pevent, perr,
                     pevent@pre, perr@pre, etype, isr,
                     opt_in, opt_abs, ecnt_in, eptr_in,
                     egrp_in, evtL_in)) &&
                   coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) &&
                   mutex_del_abort_loop_residual(
                     sg, e, ls0, eid, pevent,
                     ecnt_in, eptr_in, 0, freelist_in) &&
                   coq_prop(mutex_del_source_entry_prop(
                     sg, e, ls0, eid, pevent, tasks_v)) &&
                   coq_prop(mutex_del_success_mode_prop(
                     opt_abs, tasks_v)) &&
                   coq_prop(mutex_del_always_mode_prop(
                     opt_abs, tasks_v)) &&
                   pevent == event_addr(sg, eid) &&
                   coq_prop(valid_event_id(sg, eid)) &&
                   coq_prop(event_core_fields_layout_prop(
                     sg, eid, &pevent->OSEventType,
                     &pevent->OSEventPtr,
                     &pevent->OSEventCnt)) &&
                   coq_prop(event_wait_fields_layout_prop(
                     sg, eid, &pevent->OSEventGrp,
                     pevent->OSEventTbl)) &&
                   coq_prop(os_event_free_list_addr(
                     sg, &OSEventFreeList)) &&
                   coq_prop(os_tcb_prio_tbl_addr(
                     sg, OSTCBPrioTbl)) &&
                   data_at(&pevent->OSEventCnt, ecnt_in) &&
                   data_at(&pevent->OSEventGrp, 0) &&
                   data_at(&cpu_sr, unsigned int, cpu_sr_v) &&
                   data_at(&tasks_waiting, unsigned char, tasks_v) &&
                   data_at(&opt, unsigned char, opt_in) &&
                   undef_data_at(&pevent_return, struct os_event *) &&
                   data_at(&pcp, unsigned char, pcp_v) &&
                   undef_data_at(&prio, unsigned char) &&
                   undef_data_at(&ptcb, struct os_tcb *) &&
                   data_at(perr, unsigned char, perr_in) &&
                   data_at(&OSEventFreeList, struct os_event *, freelist_in) &&
                   safeExec(LastSeen(ls0),
                     bind(atomic_cmd(OSMutexDel_full_sem(
                            sg, pevent, opt_abs)),
                          mutex_del_observe_ptr(pevent)), X)
             */
              pcp = (INT8U)(pevent->OSEventCnt >> 8u);
              if (pcp != OS_PRIO_MUTEX_CEIL_DIS) {
                  /*@
                      0 <= pcp && pcp < 64 &&
                      coq_prop(event_core_fields_layout_prop(
                        sg, eid, &pevent->OSEventType,
                        &pevent->OSEventPtr,
                        &pevent->OSEventCnt)) *
                      coq_prop(event_wait_fields_layout_prop(
                        sg, eid, &pevent->OSEventGrp,
                        pevent->OSEventTbl)) *
                      coq_prop(os_event_free_list_addr(
                        sg, &OSEventFreeList)) *
                      coq_prop(os_tcb_prio_tbl_addr(
                        sg, OSTCBPrioTbl)) *
                      coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) *
                      mutex_del_abort_loop_residual(
                        sg, e, ls0, eid, pevent,
                        ecnt_in, eptr_in, 0, freelist_in)
                      which implies
                      exists (old_pcp_cell: Z),
                      data_at(pointer_offset(
                                OSTCBPrioTbl, pcp, OS_TCB *),
                              OS_TCB *, old_pcp_cell) *
                      mutex_del_abort_loop_missing_priotbl_residual(
                        sg, e, ls0, eid, pevent,
                        ecnt_in, eptr_in, 0, pcp, freelist_in) *
                      coq_prop(event_core_fields_layout_prop(
                        sg, eid, &pevent->OSEventType,
                        &pevent->OSEventPtr,
                        &pevent->OSEventCnt)) *
                      coq_prop(event_wait_fields_layout_prop(
                        sg, eid, &pevent->OSEventGrp,
                        pevent->OSEventTbl)) *
                      coq_prop(os_event_free_list_addr(
                        sg, &OSEventFreeList)) *
                      coq_prop(os_tcb_prio_tbl_addr(
                        sg, OSTCBPrioTbl)) *
                      coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl))
                  */
                  OSTCBPrioTbl[pcp] = (OS_TCB *)0;
              }
             /*@ Assert
                 exists (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z),
                   coq_prop(mutex_del_return_lineage_prop(
                     sg, e, ls0, eid, pe, pd, pevent, perr,
                     pevent@pre, perr@pre, etype, isr,
                     opt_in, opt_abs, ecnt_in, eptr_in,
                     egrp_in, evtL_in)) &&
                   coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) &&
                   mutex_del_abort_loop_pcp_release_residual(
                     sg, e, ls0, eid, pevent,
                     ecnt_in, eptr_in, 0, pcp_v, freelist_in) &&
                   pcp_v == decode_PCP_from_cnt(ecnt_in) &&
                   coq_prop(mutex_del_source_entry_prop(
                     sg, e, ls0, eid, pevent, tasks_v)) &&
                   coq_prop(mutex_del_success_mode_prop(
                     opt_abs, tasks_v)) &&
                   coq_prop(mutex_del_always_mode_prop(
                     opt_abs, tasks_v)) &&
                   pevent == event_addr(sg, eid) &&
                   coq_prop(valid_event_id(sg, eid)) &&
                   coq_prop(event_core_fields_layout_prop(
                     sg, eid, &pevent->OSEventType,
                     &pevent->OSEventPtr,
                     &pevent->OSEventCnt)) &&
                   coq_prop(event_wait_fields_layout_prop(
                     sg, eid, &pevent->OSEventGrp,
                     pevent->OSEventTbl)) &&
                   coq_prop(os_event_free_list_addr(
                     sg, &OSEventFreeList)) &&
                   coq_prop(os_tcb_prio_tbl_addr(
                     sg, OSTCBPrioTbl)) &&
                   data_at(&OSEventFreeList, struct os_event *, freelist_in) &&
                   data_at(&pevent->OSEventCnt, ecnt_in) &&
                   data_at(&pevent->OSEventGrp, 0) &&
                   data_at(&cpu_sr, unsigned int, cpu_sr_v) &&
                   data_at(&tasks_waiting, unsigned char, tasks_v) &&
                   data_at(&opt, unsigned char, opt_in) &&
                   undef_data_at(&pevent_return, struct os_event *) &&
                   data_at(&pcp, unsigned char, pcp_v) &&
                   undef_data_at(&prio, unsigned char) &&
                   undef_data_at(&ptcb, struct os_tcb *) &&
                   data_at(perr, unsigned char, perr_in) &&
                   safeExec(LastSeen(ls0),
                     bind(atomic_cmd(OSMutexDel_full_sem(
                            sg, pevent, opt_abs)),
                          mutex_del_observe_ptr(pevent)), X)
             */
             /*@
                 exists (tasks_v: Z),
                 coq_prop(mutex_del_source_entry_prop(
                   sg, e, ls0, eid, pevent, tasks_v)) *
                 coq_prop(mutex_del_always_mode_prop(
                   opt_abs, tasks_v)) *
                 coq_prop(event_core_fields_layout_prop(
                   sg, eid, &pevent->OSEventType,
                   &pevent->OSEventPtr,
                   &pevent->OSEventCnt)) *
                 coq_prop(event_wait_fields_layout_prop(
                   sg, eid, &pevent->OSEventGrp,
                   pevent->OSEventTbl)) *
                 coq_prop(os_event_free_list_addr(
                   sg, &OSEventFreeList)) *
                 mutex_del_abort_loop_pcp_release_residual(
                   sg, e, ls0, eid, pevent,
                   ecnt_in, eptr_in, 0, pcp, freelist_in) &&
                 coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) *
                 data_at(&tasks_waiting,
                         unsigned char, tasks_v) *
                 data_at(&opt, unsigned char, opt_in) *
                 safeExec(LastSeen(ls0),
                   bind(atomic_cmd(OSMutexDel_full_sem(
                          sg, pevent, opt_abs)),
                        mutex_del_observe_ptr(pevent)), X)
                 which implies
                 exists (owner_post: UCOS2_Verify_State)
                        (current: UCOS2_Verify_State)
                        (current_event: OSEventAbstractState)
                        (current_tbl: list Z) (old_type: Z)
                        (tasks_v: Z),
                   pcp == decode_PCP_from_cnt(ecnt_in) &&
                   InsideCritical(sg, current) *
                   mutex_del_pcp_release_focus(
                     sg, ls0, current, eid, pcp) *
                   data_at(&pevent->OSEventType,
                           unsigned char, old_type) *
                   data_at(&pevent->OSEventPtr,
                           void *, eptr_in) *
                   used_event_wait_table_storage(
                     current.TskState, pevent, current_event) *
                   coq_prop(mutex_del_rdyatprio_stage_prop(
                     sg, e, ls0, owner_post)) *
                   coq_prop(mutex_del_wake_steps(
                     sg, eid, owner_post, current)) *
                   coq_prop(event_free_list_head_prop(
                     sg, current.EventState, freelist_in)) *
                   coq_prop(event_snapshot_of_prop(
                     sg, current.TskState, current.EventState,
                     eid, current_event, old_type,
                     ecnt_in, eptr_in, 0, current_tbl)) *
                   coq_prop(mutex_del_source_entry_prop(
                     sg, e, ls0, eid, pevent, tasks_v)) *
                   coq_prop(mutex_del_success_mode_prop(
                     opt_abs, tasks_v)) *
                   coq_prop(mutex_del_always_mode_prop(
                     opt_abs, tasks_v)) *
                   coq_prop(event_core_fields_layout_prop(
                     sg, eid, &pevent->OSEventType,
                     &pevent->OSEventPtr,
                     &pevent->OSEventCnt)) *
                   coq_prop(event_wait_fields_layout_prop(
                     sg, eid, &pevent->OSEventGrp,
                     pevent->OSEventTbl)) *
                   coq_prop(os_event_free_list_addr(
                     sg, &OSEventFreeList)) *
                   coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) *
                   data_at(&tasks_waiting,
                           unsigned char, tasks_v) *
                   data_at(&opt, unsigned char, opt_in) *
                   coq_prop(safeExec(
                     LastSeen(ls0),
                     bind(atomic_cmd(OSMutexDel_full_sem(
                            sg, pevent, opt_abs)),
                          mutex_del_observe_ptr(pevent)), X))
             */
             pevent->OSEventType = OS_EVENT_TYPE_UNUSED;
             pevent->OSEventPtr  = OSEventFreeList;
             pevent->OSEventCnt  = 0u;
             OSEventFreeList     = pevent;
             /*@ Assert
                 exists (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z),
                   coq_prop(mutex_del_return_lineage_prop(
                     sg, e, ls0, eid, pe, pd, pevent, perr,
                     pevent@pre, perr@pre, etype, isr,
                     opt_in, opt_abs, ecnt_in, eptr_in,
                     egrp_in, evtL_in)) &&
                   coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) &&
                   mutex_del_success_commit_inv(
                     sg, e, ls0, eid, opt_abs,
                     pevent, tasks_v, X) &&
                   coq_prop(mutex_del_always_mode_prop(
                     opt_abs, tasks_v)) &&
                   data_at(&opt, unsigned char, opt_in) &&
                   data_at(&cpu_sr, unsigned int, cpu_sr_v) &&
                   data_at(&tasks_waiting, unsigned char, tasks_v) &&
                   undef_data_at(&pevent_return, struct os_event *) &&
                   data_at(&pcp, unsigned char, pcp_v) &&
                   undef_data_at(&prio, unsigned char) &&
                   undef_data_at(&ptcb, struct os_tcb *) &&
                   data_at(perr, unsigned char, perr_in)
             */
             /*@
                 coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) *
                 mutex_del_success_commit_inv(
                   sg, e, ls0, eid, opt_abs,
                   pevent, tasks_waiting, X)
                 which implies
                 exists (critical_anchor: UCOS2_Verify_State)
                        (ls_commit: UCOS2_Verify_State),
                   InsideCritical(sg, critical_anchor) *
                   mutex_del_transition_rep(sg, ls0, ls_commit) *
                   coq_prop(mutex_del_success_commit_anchor_prop(
                     sg, e, ls0, eid, opt_abs,
                     critical_anchor, ls_commit)) *
                   coq_prop(mutex_del_source_entry_prop(
                     sg, e, ls0, eid, pevent, tasks_waiting)) *
                   coq_prop(mutex_del_success_mode_prop(
                     opt_abs, tasks_waiting)) *
                   coq_prop(mutex_del_refresh_context_prop(sg, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy, &OSTCBHighRdy, OSTCBPrioTbl)) *
                   coq_prop(safeExec(
                     LastSeen(ls0),
                     bind(atomic_cmd(OSMutexDel_full_sem(
                            sg, pevent, opt_abs)),
                          mutex_del_observe_ptr(pevent)), X))
             */
             OSMutexDel_RefreshHighReady()
               /*@ where sg = sg, entry = ls0 */;
             OS_EXIT_CRITICAL()
               /*@ where sg = sg, entry = ls0,
                          raw_stage = false */;
             /*@ Assert
                 exists (perr_v: Z) (tasks_v: Z) (pcp_v: Z)
                        (cpu_sr_v: Z),
                   coq_prop(mutex_del_return_lineage_prop(
                     sg, e, ls0, eid, pe, pd, pevent, perr,
                     pevent@pre, perr@pre, etype, isr,
                     opt_in, opt_abs, ecnt_in, eptr_in,
                     egrp_in, evtL_in)) &&
                   mutex_del_success_exit_inv(
                     sg, e, ls0, eid, opt_abs,
                     pevent, tasks_v, X) &&
                   data_at(perr, unsigned char, perr_v) &&
                   undef_data_at(&pevent_return, struct os_event *) &&
                   data_at(&tasks_waiting, unsigned char, tasks_v) &&
                   data_at(&opt, unsigned char, opt_in) &&
                   data_at(&pcp, unsigned char, pcp_v) &&
                   undef_data_at(&prio, unsigned char) &&
                   undef_data_at(&ptcb, struct os_tcb *) &&
                   data_at(&cpu_sr, unsigned int, cpu_sr_v)
             */
             if (tasks_waiting == OS_TRUE) {
                 /*@
                     mutex_del_success_exit_inv(
                       sg, e, ls0, eid, opt_abs,
                       pevent, tasks_waiting, X)
                     which implies
                     exists (critical_anchor: UCOS2_Verify_State)
                            (ls_commit: UCOS2_Verify_State)
                            (ls_exited: UCOS2_Verify_State),
                       OutsideCritical(sg, ls_exited) *
                       mutex_del_transition_rep(
                         sg, ls_exited, ls_exited) *
                       coq_prop(mutex_del_success_commit_anchor_prop(
                         sg, e, ls0, eid, opt_abs,
                         critical_anchor, ls_commit)) *
                       coq_prop(mutex_del_source_entry_prop(
                         sg, e, ls0, eid, pevent, tasks_waiting)) *
                       coq_prop(mutex_del_success_mode_prop(
                         opt_abs, tasks_waiting)) *
                       coq_prop(mutex_del_exit_critical_anchored_call_prop(
                         sg, critical_anchor, ls_commit, ls_exited)) *
                       coq_prop(UCOS2_state_inv(sg, ls_exited)) *
                       coq_prop(valid_stable_glob_vars(sg)) *
                       coq_prop(safeExec(
                         LastSeen(ls0),
                         bind(atomic_cmd(OSMutexDel_full_sem(
                                sg, pevent, opt_abs)),
                              mutex_del_observe_ptr(pevent)), X))
                 */
                 OS_Sched()/*@ where sg = sg */;
             }
             /*@ Assert
                 exists (perr_v: Z) (tasks_v: Z) (pcp_v: Z)
                        (cpu_sr_v: Z),
                   coq_prop(mutex_del_return_lineage_prop(
                     sg, e, ls0, eid, pe, pd, pevent, perr,
                     pevent@pre, perr@pre, etype, isr,
                     opt_in, opt_abs, ecnt_in, eptr_in,
                     egrp_in, evtL_in)) &&
                   mutex_del_success_out_inv(
                     sg, e, ls0, eid, opt_abs, pevent, tasks_v, X) &&
                   data_at(perr, unsigned char, perr_v) &&
                   undef_data_at(&pevent_return, struct os_event *) &&
                   data_at(&tasks_waiting, unsigned char, tasks_v) &&
                   data_at(&opt, unsigned char, opt_in) &&
                   data_at(&pcp, unsigned char, pcp_v) &&
                   undef_data_at(&prio, unsigned char) &&
                   undef_data_at(&ptcb, struct os_tcb *) &&
                   data_at(&cpu_sr, unsigned int, cpu_sr_v)
             */
            *perr          = OS_ERR_NONE;
             pevent_return = (OS_EVENT *)0;
             break;

        default:
             /*@
                data_at(&pevent->OSEventType, unsigned char, 4) *
                data_at(&pevent->OSEventPtr, void *, eptr_in) *
                data_at(&pevent->OSEventCnt, unsigned short, ecnt_in) *
                data_at(&pevent->OSEventGrp, unsigned char, egrp_in) *
                used_event_wait_table_storage(ls0.TskState, pevent, e) *
                data_at(&OSEventFreeList,
                        struct os_event *, freelist_in) *
                mutex_del_event_focus_inv(sg, ls0, eid) *
                coq_prop(event_snapshot_of_prop(
                  sg, ls0.TskState, ls0.EventState, eid, e, 4,
                  ecnt_in, eptr_in, egrp_in, evtL_in)) *
                coq_prop(event_core_fields_layout_prop(
                  sg, eid, &pevent->OSEventType,
                  &pevent->OSEventPtr, &pevent->OSEventCnt)) *
                coq_prop(event_wait_fields_layout_prop(
                  sg, eid, &pevent->OSEventGrp, pevent->OSEventTbl)) *
                coq_prop(os_event_free_list_addr(
                  sg, &OSEventFreeList)) *
                coq_prop(event_free_list_head_prop(
                  sg, ls0.EventState, freelist_in)) *
                coq_prop(mutex_del_source_entry_prop(
                  sg, e, ls0, eid, pevent, tasks_waiting))
                which implies
                data_at(&pevent, struct os_event *, pevent) *
                data_at(&tasks_waiting,
                        unsigned char, tasks_waiting) *
                UCOS2_Verify_inv(sg, ls0) *
                coq_prop(mutex_del_source_entry_prop(
                  sg, e, ls0, eid, pevent, tasks_waiting))
             */
             /*@ Assert
                exists (cpu_sr_v: Z) (tasks_v: Z),
                   coq_prop(mutex_del_return_lineage_prop(
                     sg, e, ls0, eid, pe, pd, pevent, perr,
                     pevent@pre, perr@pre, etype, isr,
                     opt_in, opt_abs, ecnt_in, eptr_in,
                     egrp_in, evtL_in)) &&
                   mutex_del_unchanged_inside_inv(
                     sg, e, ls0, eid, pevent, opt_abs,
                     tasks_v, 7, X) &&
                   data_at(&cpu_sr, unsigned int, cpu_sr_v) &&
                   data_at(&tasks_waiting, unsigned char, tasks_v) &&
                   undef_data_at(&pevent_return, struct os_event *) &&
                   undef_data_at(&pcp, unsigned char) &&
                   undef_data_at(&prio, unsigned char) &&
                   undef_data_at(&ptcb, struct os_tcb *) &&
                   data_at(perr, unsigned char, perr_in)
             */
             /*@
                mutex_del_unchanged_inside_inv(
                  sg, e, ls0, eid, pevent, opt_abs,
                  tasks_waiting, 7, X)
                which implies
                  InsideCritical(sg, ls0) *
                  mutex_del_restore_rep(false, sg, ls0, ls0) *
                  coq_prop(mutex_del_source_entry_prop(
                    sg, e, ls0, eid, pevent, tasks_waiting)) *
                  coq_prop(mutex_del_error_mode_prop(
                    opt_abs, tasks_waiting, 7)) *
                  coq_prop(safeExec(
                    LastSeen(ls0),
                    bind(atomic_cmd(OSMutexDel_full_sem(
                           sg, pevent, opt_abs)),
                         mutex_del_observe_ptr(pevent)), X))
             */
             OS_EXIT_CRITICAL()/*@ where sg = sg, entry = ls0,
                                          raw_stage = false,
                                          critical_anchor = ls0,
                                          logical_post = ls0 */;
             /*@ Assert
                exists (perr_v: Z) (tasks_v: Z) (cpu_sr_v: Z),
                   coq_prop(mutex_del_return_lineage_prop(
                     sg, e, ls0, eid, pe, pd, pevent, perr,
                     pevent@pre, perr@pre, etype, isr,
                     opt_in, opt_abs, ecnt_in, eptr_in,
                     egrp_in, evtL_in)) &&
                   mutex_del_unchanged_exit_inv(
                     sg, e, ls0, eid, pevent, opt_abs,
                     tasks_v, 7, X) &&
                   data_at(perr, unsigned char, perr_v) &&
                   undef_data_at(&pevent_return, struct os_event *) &&
                   data_at(&tasks_waiting, unsigned char, tasks_v) &&
                   undef_data_at(&pcp, unsigned char) &&
                   undef_data_at(&prio, unsigned char) &&
                   undef_data_at(&ptcb, struct os_tcb *) &&
                   data_at(&cpu_sr, unsigned int, cpu_sr_v)
             */
            *perr          = OS_ERR_INVALID_OPT;
             pevent_return = pevent;
             break;
    }
    return (pevent_return);
}
