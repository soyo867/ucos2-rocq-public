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
/*@ Extern Coq (unsigned_last_nbits: Z -> Z -> Z) */
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
/*@ Extern Coq (PTReserved : PrioTblEntry) */
/*@ Extern Coq (PTTask : TaskID -> PrioTblEntry) */
/*@ Extern Coq (mfPCP           : MutexFields -> Priority) */
/*@ Extern Coq (mfOwner         : MutexFields -> option TaskID) */
/*@ Extern Coq (mfOwnerOrigPrio : MutexFields -> option Priority) */

/*@ Extern Coq (OS_ERR_NONE            : OSErrCode) */
/*@ Extern Coq (OS_ERR_PEVENT_NULL     : OSErrCode) */
/*@ Extern Coq (OS_ERR_EVENT_TYPE      : OSErrCode) */
/*@ Extern Coq (OS_ERR_POST_ISR        : OSErrCode) */
/*@ Extern Coq (OS_ERR_NOT_MUTEX_OWNER : OSErrCode) */
/*@ Extern Coq (OS_ERR_PCP_LOWER       : OSErrCode) */
/*@ Extern Coq (OS_TRUE  : Z) */
/*@ Extern Coq (OS_FALSE : Z) */
/*@ Extern Coq (store_priotbl_list : StableGlobVars -> list addr -> Assertion) */
/*@ Extern Coq (store_priotbl_list_missing_i : StableGlobVars -> list addr -> Z -> Assertion) */
/*@ Extern Coq (store_oseventtbl : StableGlobVars -> addr -> list Z -> Assertion) */
/*@ Extern Coq (prio_tbl_list_rel : StableGlobVars -> Glob_TaskAbstractState -> list addr -> Prop) */
/*@ Extern Coq (valid_mutex_pcp : StableGlobVars -> Priority -> Prop) */
/*@ Extern Coq (event_snapshot_of_prop : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> EventID -> OSEventAbstractState -> Z -> Z -> addr -> Z -> list Z -> Prop) */
/*@ Extern Coq (event_raw_snapshot_of_prop : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> EventID -> OSEventAbstractState -> Z -> Z -> addr -> Z -> list Z -> Prop) */
/*@ Extern Coq (event_core_fields_layout_prop : StableGlobVars -> EventID -> addr -> addr -> addr -> Prop) */
/*@ Extern Coq (event_wait_fields_layout_prop : StableGlobVars -> EventID -> addr -> addr -> Prop) */
/*@ Extern Coq (event_slot_type_value : Glob_EventAbstractState -> EventID -> Z) */
/*@ Extern Coq (event_slot_unused_prop : Glob_EventAbstractState -> EventID -> Prop) */
/*@ Extern Coq (mutex_post_public_event_domain_prop :
      StableGlobVars -> UCOS2_Verify_State ->
      addr -> EventID -> OSEventAbstractState ->
      Z -> Z -> Z -> Z -> list Z ->
      Z -> Z -> Z -> Z -> list addr ->
      TaskID -> TaskAbstractState ->
      addr -> addr -> addr -> Prop) */
/*@ Extern Coq (task_prio_field_layout_prop : addr -> addr -> Prop) */
/*@ Extern Coq (task_prio_snapshot_of_prop : StableGlobVars -> Glob_TaskAbstractState -> TaskID -> TaskAbstractState -> addr -> Z -> Prop) */
/*@ Extern Coq (sched_tcb_cur_snapshot_prop : StableGlobVars -> SchedAbstractState -> addr -> Prop) */
/*@ Extern Coq (mutex_release_event_prop : OSEventAbstractState -> OSEventAbstractState -> Prop) */
/*@ Extern Coq (mutex_handover_event_prop : OSEventAbstractState -> OSEventAbstractState -> TaskID -> Priority -> Prop) */
/*@ Extern Coq (decode_PCP_from_cnt : Z -> Z) */
/*@ Extern Coq (decode_OwnerPrio_from_cnt : Z -> Z) */

/*@ Extern Coq (coq_prop : Prop -> Assertion) */
/*@ Extern Coq (valid_stable_glob_vars : StableGlobVars -> Prop) */
/*@ Extern Coq (valid_event_id : StableGlobVars -> EventID -> Prop) */
/*@ Extern Coq (store_used_event_map_missing_i : StableGlobVars -> (EventID -> option OSEventAbstractState) -> EventID -> Assertion) */
/*@ Extern Coq (used_complete_event : StableGlobVars -> Glob_TaskAbstractState -> addr -> EventID -> OSEventAbstractState -> Assertion) */
/*@ Extern Coq (unused_complete_event : StableGlobVars -> addr -> EventID -> Assertion) */
/*@ Extern Coq (store_free_event_list : StableGlobVars -> list EventID -> Assertion) */
/*@ Extern Coq (store_int_state : StableGlobVars -> Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (interrupt_inv : StableGlobVars -> Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (interrupt_inv_no_int_nesting : StableGlobVars -> Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (task_inv : StableGlobVars -> Glob_TaskAbstractState -> Assertion) */
/*@ Extern Coq (task_inv_no_priotbl : StableGlobVars -> Glob_TaskAbstractState -> Assertion) */
/*@ Extern Coq (task_inv_no_tid_priotbl : StableGlobVars -> Glob_TaskAbstractState -> TaskID -> Assertion) */
/*@ Extern Coq (used_task_no_prio : StableGlobVars -> addr -> TaskID -> TaskAbstractState -> Assertion) */
/*@ Extern Coq (sched_inv : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> Assertion) */
/*@ Extern Coq (sched_inv_no_tcb_cur : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> Assertion) */
/*@ Extern Coq (event_inv : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> Assertion) */
/*@ Extern Coq (event_inv_no_eid : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> EventID -> Assertion) */
/*@ Extern Coq (used_event_rest_no_type_cnt_ptr : StableGlobVars -> Glob_TaskAbstractState -> addr -> EventID -> OSEventAbstractState -> Assertion) */
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
/*@ Extern Coq (LastSeen : UCOS2_Verify_State -> (UCOS2_Verify_State -> Prop) -> Prop) */
/*@ Extern Coq (should_be_equal: {A} -> A -> A -> Prop) */
/*@ Extern Coq (crit_rel_no_os_state_change : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (crit_rel_task_event_sched : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (UCOS2_Verify_inv : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (UCOS2_Verify_inv_no_int_nesting : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (UCOS2_Verify_inv_focus_event_int : StableGlobVars -> UCOS2_Verify_State -> EventID -> Assertion) */
/*@ Extern Coq (UCOS2_Verify_inv_no_event_type : StableGlobVars -> UCOS2_Verify_State -> EventID -> Assertion) */
/*@ Extern Coq (UCOS2_raw_rep : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (UCOS2_raw_ready_prio_stage : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (UCOS2_state_inv : StableGlobVars -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (UCOS2_isr_or_task_call_boundary_prop : UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (encode_os_err_code : OSErrCode -> Z) */
/*@ Extern Coq (observe_os_err_code : OSErrCode -> program (UCOS2_Verify_State -> Prop) Z) */
/*@ Extern Coq (observe_unit_void : unit -> program (UCOS2_Verify_State -> Prop) unit) */
/*@ Extern Coq (OSMutexPost_sem : StableGlobVars -> addr -> program UCOS2_Verify_State OSErrCode) */
/*@ Extern Coq (OSMutex_RdyAtPrio_current_ready_sem : StableGlobVars -> addr -> Priority -> program UCOS2_Verify_State unit) */
/*@ Extern Coq (OSMutexPost_atomic_cmd : StableGlobVars -> UCOS2_Verify_State -> addr -> program (UCOS2_Verify_State -> Prop) OSErrCode) */
/*@ Extern Coq (OSMutexPost_LastSeen : StableGlobVars -> addr -> UCOS2_Verify_State -> OSErrCode -> UCOS2_Verify_State -> (UCOS2_Verify_State -> Prop) -> Prop) */
/*@ Extern Coq (OSMutexPost_RdyAtPrio_atomic_cmd : StableGlobVars -> UCOS2_Verify_State -> addr -> Priority -> program (UCOS2_Verify_State -> Prop) unit) */
/*@ Extern Coq (OSMutexPost_RdyAtPrio_LastSeen : StableGlobVars -> addr -> Priority -> UCOS2_Verify_State -> UCOS2_Verify_State -> (UCOS2_Verify_State -> Prop) -> Prop) */
/*@ Extern Coq (OSMutexPost_RdyAtPrio_guarantee : StableGlobVars -> addr -> Priority -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_post_result_prop : StableGlobVars -> addr -> UCOS2_Verify_State -> UCOS2_Verify_State -> Z -> Prop) */
/*@ Extern Coq (mutex_post_current_ready_step_prop : StableGlobVars -> addr -> Priority -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_post_sched_step_prop : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_post_release_step_prop : StableGlobVars -> EventID -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_post_empty_count_commit_step_prop : EventID -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_post_empty_owner_commit_step_prop : EventID -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_post_checked_entry_prop : UCOS2_Verify_State -> addr -> Prop) */
/*@ Extern Coq (mutex_post_owner_entry_context_prop : StableGlobVars -> addr -> EventID -> UCOS2_Verify_State -> UCOS2_Verify_State -> Priority -> Priority -> addr -> Priority -> Prop) */
/*@ Extern Coq (mutex_post_owner_disinherit_stage_prop : StableGlobVars -> addr -> UCOS2_Verify_State -> Priority -> Priority -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_post_reservation_stage_prop : StableGlobVars -> EventID -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_post_wake_step_prop : StableGlobVars -> EventID -> UCOS2_Verify_State -> Priority -> TaskID -> TaskID -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_post_count_commit_step_prop : EventID -> Priority -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_post_owner_commit_step_prop : EventID -> Priority -> TaskID -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_post_handover_step_prop : StableGlobVars -> EventID -> UCOS2_Verify_State -> Priority -> TaskID -> TaskID -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (mutex_post_rep : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (mutex_post_rep_no_event : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> EventID -> Assertion) */
/*@ Extern Coq (mutex_post_rep_no_priotbl_no_event : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> EventID -> Assertion) */
/*@ Extern Coq (mutex_post_handover_residual : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> EventID -> Assertion) */
/*@ Extern Coq (mutex_post_handover_residual_no_priotbl : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> EventID -> Assertion) */
/*@ Extern Coq (mutex_post_conditional_validity_prop : StableGlobVars -> addr -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (atomic_mutex_release_with_handover : StableGlobVars -> EventID -> UCOS2_Verify_State -> TaskID -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (os_int_nesting_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_tcb_cur_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_tcb_prio_tbl_addr : StableGlobVars -> addr -> Prop) */

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
/*@ Import Coq Require Import Ucos2Verify.lib.mutex_func_sem */
/*@ Import Coq Require Import Ucos2Verify.lib.mutex_rdyatprio_spec */
/*@ Import Coq Require Import Ucos2Verify.lib.array_abstraction */
/*@ Import Coq Require Import Ucos2Verify.lib.tick */
/*@ Import Coq Require Import Ucos2Verify.lib.cross_module_invariants */
/*@ Import Coq Require Import Ucos2Verify.lib.mutex_post_spec */

typedef unsigned int OS_CPU_SR;

unsigned int OS_CPU_SR_Save()
/*@ With (sg: StableGlobVars) (ls0: UCOS2_Verify_State) (eid: EventID)
    Require OutsideCritical(sg, ls0)
    Ensure  exists ls1,
            RTrans_C(sg, ls0, sg, ls1) &&
            InsideCritical(sg, ls1) &&
            coq_prop(crit_rel_no_os_state_change(ls0, ls1)) &&
            __return == __return
*/
;

void OS_CPU_SR_Restore(unsigned int cpu_sr)
/*@ With (sg: StableGlobVars)
           (ls_entry: UCOS2_Verify_State)
           (ls_post: UCOS2_Verify_State) (eid: EventID)
    Require InsideCritical(sg, ls_entry) &&
            coq_prop(crit_rel_task_event_sched(ls_entry, ls_post))
    Ensure  GTrans_C(sg, ls_entry, sg, ls_post) &&
            OutsideCritical(sg, ls_post) &&
            coq_prop(crit_rel_task_event_sched(ls_entry, ls_post))
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
#define  OS_ERR_POST_ISR                5u
#define  OS_ERR_PCP_LOWER               120u
#define  OS_ERR_NOT_MUTEX_OWNER         100u
#define  OS_MUTEX_KEEP_LOWER_8          0x00FFu
#define  OS_MUTEX_KEEP_UPPER_8          0xFF00u
#define  OS_MUTEX_AVAILABLE             0x00FFu
#define  OS_PRIO_MUTEX_CEIL_DIS         0xFFu
#define  OS_STAT_MUTEX                  0x10u
#define  OS_STAT_PEND_OK                0u

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

#define  OS_TCB_RESERVED                ((OS_TCB *)1)

typedef struct os_event {
    INT8U    OSEventType;
    void    *OSEventPtr;
    INT16U   OSEventCnt;
    OS_PRIO  OSEventGrp;
    OS_PRIO  OSEventTbl[8];
} OS_EVENT;

extern  INT8U    OSIntNesting;
extern  INT8U    OSLockNesting;
extern  OS_TCB  *OSTCBCur;
extern  OS_TCB  *OSTCBPrioTbl[64];

void OSMutex_RdyAtPrio(OS_TCB *ptcb, INT8U prio)
/*@ With (sg: StableGlobVars)
           (ls: UCOS2_Verify_State) (ls0: UCOS2_Verify_State)
           (pe0: addr) (eid: EventID) (e0: OSEventAbstractState)
           (cur_tid0: TaskID) (cur_t0: TaskAbstractState)
           (tcbprio0: Z) (ecnt0: Z) (owner_ptr0: addr)
           (egrp0: Z) (evtL0: list Z) (prioL0: list addr)
           (pcp0: Priority) (owner_orig0: Priority) Xr
    Require
            coq_prop(mutex_post_owner_entry_context_prop(
              sg, pe0, eid, ls0, ls, pcp0, owner_orig0,
              ptcb, tcbprio0)) &&
            coq_prop(task_prio_snapshot_of_prop(
              sg, ls.TskState, cur_tid0, cur_t0, ptcb, tcbprio0)) &&
            coq_prop(event_snapshot_of_prop(
              sg, ls.TskState, ls.EventState, eid, e0, 4,
              ecnt0, owner_ptr0, egrp0, evtL0)) &&
            coq_prop(event_core_fields_layout_prop(
              sg, eid,
              &((OS_EVENT *)pe0)->OSEventType,
              &((OS_EVENT *)pe0)->OSEventPtr,
              &((OS_EVENT *)pe0)->OSEventCnt)) &&
            coq_prop(event_wait_fields_layout_prop(
              sg, eid,
              &((OS_EVENT *)pe0)->OSEventGrp,
              &((OS_EVENT *)pe0)->OSEventTbl)) &&
            coq_prop(prio_tbl_list_rel(sg, ls.TskState, prioL0)) &&
            safeExec(LastSeen(ls),
                     bind(OSMutexPost_RdyAtPrio_atomic_cmd(
                            sg, ls, ptcb, prio),
                          observe_unit_void), Xr) &&
            InsideCritical(sg, ls) &&
            interrupt_inv(sg, ls.IntrState) *
            data_at(&ptcb->OSTCBPrio, unsigned char, tcbprio0) *
            used_task_no_prio(sg, ptcb, cur_tid0, cur_t0) *
            task_inv_no_tid_priotbl(sg, ls.TskState, cur_tid0) *
            store_priotbl_list(sg, prioL0) *
            data_at(&OSTCBCur, struct os_tcb *, ptcb) *
            sched_inv_no_tcb_cur(sg, ls.TskState, ls.SchedState) *
            data_at(&((OS_EVENT *)pe0)->OSEventType, unsigned char, 4) *
            data_at(&((OS_EVENT *)pe0)->OSEventCnt, unsigned short, ecnt0) *
            data_at(&((OS_EVENT *)pe0)->OSEventPtr, void *, owner_ptr0) *
            data_at(&((OS_EVENT *)pe0)->OSEventGrp, unsigned char, egrp0) *
            data_at(&((OS_EVENT *)pe0)->OSEventTbl[0], unsigned char, Znth(0, evtL0, 0)) *
            data_at(&((OS_EVENT *)pe0)->OSEventTbl[1], unsigned char, Znth(1, evtL0, 0)) *
            data_at(&((OS_EVENT *)pe0)->OSEventTbl[2], unsigned char, Znth(2, evtL0, 0)) *
            data_at(&((OS_EVENT *)pe0)->OSEventTbl[3], unsigned char, Znth(3, evtL0, 0)) *
            data_at(&((OS_EVENT *)pe0)->OSEventTbl[4], unsigned char, Znth(4, evtL0, 0)) *
            data_at(&((OS_EVENT *)pe0)->OSEventTbl[5], unsigned char, Znth(5, evtL0, 0)) *
            data_at(&((OS_EVENT *)pe0)->OSEventTbl[6], unsigned char, Znth(6, evtL0, 0)) *
            data_at(&((OS_EVENT *)pe0)->OSEventTbl[7], unsigned char, Znth(7, evtL0, 0)) *
            event_inv_no_eid(sg, ls.TskState, ls.EventState, eid) *
            tick_inv(sg, ls.TickState) *
            coq_prop(cross_module_consistency(sg, ls))
    Ensure  exists ls_rdy,
            coq_prop(mutex_post_current_ready_step_prop(
              sg, ptcb, prio, ls, ls_rdy)) &&
            coq_prop(OSMutexPost_RdyAtPrio_guarantee(
              sg, ptcb, prio, ls, ls_rdy)) &&
            coq_prop(mutex_post_owner_entry_context_prop(
              sg, pe0, eid, ls0, ls, pcp0, owner_orig0,
              ptcb, tcbprio0)) &&
            coq_prop(mutex_post_owner_disinherit_stage_prop(
              sg, pe0, ls0, pcp0, owner_orig0, ls_rdy)) &&
            coq_prop(event_raw_snapshot_of_prop(
              sg, ls_rdy.TskState, ls_rdy.EventState, eid, e0, 4,
              ecnt0, owner_ptr0, egrp0, evtL0)) &&
            coq_prop(event_core_fields_layout_prop(
              sg, eid,
              &((OS_EVENT *)pe0)->OSEventType,
              &((OS_EVENT *)pe0)->OSEventPtr,
              &((OS_EVENT *)pe0)->OSEventCnt)) &&
            coq_prop(event_wait_fields_layout_prop(
              sg, eid,
              &((OS_EVENT *)pe0)->OSEventGrp,
              &((OS_EVENT *)pe0)->OSEventTbl)) &&
            safeExec(OSMutexPost_RdyAtPrio_LastSeen(
                       sg, ptcb, prio, ls, ls_rdy),
                     return(tt), Xr) &&
            InsideCritical(sg, ls) &&
            UCOS2_raw_ready_prio_stage(sg, ls, ls_rdy)
*/
;

INT8U OS_EventTaskRdy(OS_EVENT *pevent, void *msg, INT8U msk, INT8U pend_stat)
/*@ With (sg: StableGlobVars) (eid: EventID)
           (ls0_post: UCOS2_Verify_State) (pe0: addr)
           (pcp0: Priority) (owner_orig0: Priority)
           (e0: OSEventAbstractState) (ecnt0: Z) (owner_ptr0: addr)
           (egrp_in: Z) (evtL0: list Z)
    Require exists (ls_d: UCOS2_Verify_State)
                   (ls: UCOS2_Verify_State),
            InsideCritical(sg, ls0_post) &&
            pevent == event_addr(sg, eid) &&
            pe0 == pevent &&
            egrp_in != 0 &&
            coq_prop(valid_event_id(sg, eid)) &&
            coq_prop(mutex_post_owner_disinherit_stage_prop(
              sg, pe0, ls0_post, pcp0, owner_orig0, ls_d)) &&
            coq_prop(mutex_post_reservation_stage_prop(
              sg, eid, ls_d, ls)) &&
            coq_prop(event_raw_snapshot_of_prop(
              sg, ls.TskState, ls.EventState, eid, e0, 4,
              ecnt0, owner_ptr0, egrp_in, evtL0)) &&
            coq_prop(event_core_fields_layout_prop(
              sg, eid,
              &pevent->OSEventType,
              &pevent->OSEventPtr,
              &pevent->OSEventCnt)) &&
            coq_prop(event_wait_fields_layout_prop(
              sg, eid,
              &pevent->OSEventGrp,
              &pevent->OSEventTbl)) &&
            mutex_post_rep_no_event(
              sg, ls0_post, ls, eid) *
            data_at(&pevent->OSEventType, unsigned char, 4) *
            data_at(&pevent->OSEventCnt, unsigned short, ecnt0) *
            data_at(&pevent->OSEventPtr, void *, owner_ptr0) *
            data_at(&pevent->OSEventGrp, unsigned char, egrp_in) *
            data_at(&pevent->OSEventTbl[0], unsigned char,
                    Znth(0, evtL0, 0)) *
            data_at(&pevent->OSEventTbl[1], unsigned char,
                    Znth(1, evtL0, 0)) *
            data_at(&pevent->OSEventTbl[2], unsigned char,
                    Znth(2, evtL0, 0)) *
            data_at(&pevent->OSEventTbl[3], unsigned char,
                    Znth(3, evtL0, 0)) *
            data_at(&pevent->OSEventTbl[4], unsigned char,
                    Znth(4, evtL0, 0)) *
            data_at(&pevent->OSEventTbl[5], unsigned char,
                    Znth(5, evtL0, 0)) *
            data_at(&pevent->OSEventTbl[6], unsigned char,
                    Znth(6, evtL0, 0)) *
            data_at(&pevent->OSEventTbl[7], unsigned char,
                    Znth(7, evtL0, 0))
    Ensure  exists (ls_d: UCOS2_Verify_State)
                   (ls: UCOS2_Verify_State)
                   (ls_wake: UCOS2_Verify_State)
                   (canonical_waiter: TaskID) (table_owner: TaskID)
                   (e_h: OSEventAbstractState)
                   (cnt_out: Z) (ptr_out: addr)
                   (egrp_out: Z) (evtL_out: list Z),
            coq_prop(mutex_post_wake_step_prop(
              sg, eid, ls, __return,
              canonical_waiter, table_owner, ls_wake)) &&
            coq_prop(mutex_post_owner_disinherit_stage_prop(
              sg, pe0, ls0_post, pcp0, owner_orig0, ls_d)) &&
            coq_prop(mutex_post_reservation_stage_prop(
              sg, eid, ls_d, ls)) &&
            coq_prop(event_raw_snapshot_of_prop(
              sg, ls.TskState, ls.EventState, eid, e0, 4,
              ecnt0, owner_ptr0, egrp_in, evtL0)) &&
            coq_prop(event_raw_snapshot_of_prop(
              sg, ls_wake.TskState, ls_wake.EventState, eid, e_h, 4,
              cnt_out, ptr_out, egrp_out, evtL_out)) &&
            coq_prop(event_core_fields_layout_prop(
              sg, eid,
              &pevent->OSEventType,
              &pevent->OSEventPtr,
              &pevent->OSEventCnt)) &&
            coq_prop(event_wait_fields_layout_prop(
              sg, eid,
              &pevent->OSEventGrp,
              &pevent->OSEventTbl)) &&
            coq_prop(should_be_equal(
              ls_wake.TskState.prioTbl(__return), PTTask(table_owner))) &&
            InsideCritical(sg, ls0_post) &&
            pevent == event_addr(sg, eid) &&
            coq_prop(valid_event_id(sg, eid)) &&
            mutex_post_handover_residual(
              sg, ls0_post, ls_wake, eid) *
            data_at(&pevent->OSEventType, unsigned char, 4) *
            data_at(&pevent->OSEventCnt, unsigned short, ecnt0) *
            data_at(&pevent->OSEventPtr, void *, owner_ptr0) *
            data_at(&pevent->OSEventGrp, unsigned char, egrp_out) *
            data_at(&pevent->OSEventTbl[0], unsigned char,
                    Znth(0, evtL_out, 0)) *
            data_at(&pevent->OSEventTbl[1], unsigned char,
                    Znth(1, evtL_out, 0)) *
            data_at(&pevent->OSEventTbl[2], unsigned char,
                    Znth(2, evtL_out, 0)) *
            data_at(&pevent->OSEventTbl[3], unsigned char,
                    Znth(3, evtL_out, 0)) *
            data_at(&pevent->OSEventTbl[4], unsigned char,
                    Znth(4, evtL_out, 0)) *
            data_at(&pevent->OSEventTbl[5], unsigned char,
                    Znth(5, evtL_out, 0)) *
            data_at(&pevent->OSEventTbl[6], unsigned char,
                    Znth(6, evtL_out, 0)) *
            data_at(&pevent->OSEventTbl[7], unsigned char,
                    Znth(7, evtL_out, 0))
*/
;

void OS_Sched()
/*@ With (sg: StableGlobVars)
           (stage_entry: UCOS2_Verify_State)
           (ls: UCOS2_Verify_State) (eid: EventID)
    Require OutsideCritical(sg, ls) &&
            UCOS2_raw_ready_prio_stage(sg, stage_entry, ls)
    Ensure  exists ls_sched,
            coq_prop(mutex_post_sched_step_prop(ls, ls_sched)) &&
            OutsideCritical(sg, ls_sched) &&
            mutex_post_rep(sg, stage_entry, ls_sched)
*/
;

/* ============================================================ */
/* OSMutexPost_full: µC/OS-II os_mutex.c 字面实现.               */
/*                                                              */
/* 目标(纯 list + 字面变下标):                                  */
/*   - PRE/POST 数组资源只用 list 谓词,不罗列 cell              */
/*   - body 还原源码字面 OSTCBPrioTbl[pcp] / OSTCBPrioTbl[prio] */
/*   - 不用 helper 包装                                          */
/*                                                              */
/* 字面 body 中的变下标访问点(共 2 处):                          */
/*   (1) OSTCBPrioTbl[pcp] = OS_TCB_RESERVED (保留 ceiling,写) */
/*   (2) pevent->OSEventPtr = OSTCBPrioTbl[prio]  (新 owner,读)*/
/*                                                              */
/* which implies 在每个变下标点把整体 list 拆为 missing_i + cell.*/
/* ============================================================ */
INT8U  OSMutexPost_full (OS_EVENT *pevent)
/*@ With (sg: StableGlobVars) (ls0: UCOS2_Verify_State) X
           (pevent0: addr)
           (eid: EventID) (e: OSEventAbstractState)
           (cur_tid: TaskID) (cur_t: TaskAbstractState)
           (isr: Z) (etype: Z)
           (ecnt_in: Z) (owner_ptr: addr) (egrp_in: Z)
           (evtL_in: list Z)
           (tcbcur: addr) (tcbprio: Z)
           (pcp_idx: Z) (prio_tbl_pcp: Z)
           (prioL_in: list addr)
    Require
        pevent == pevent0 &&
        isr == intNesting(ls0.IntrState) &&
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
        coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) &&
        coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
        safeExec(LastSeen(ls0),
                 bind(OSMutexPost_atomic_cmd(sg, ls0, pevent0),
                      observe_os_err_code), X) &&
        OutsideCritical(sg, ls0) &&
        UCOS2_Verify_inv(sg, ls0) &&
        coq_prop(valid_stable_glob_vars(sg)) &&
        (
            isr > 0 ||
            (isr <= 0 && pevent0 == 0) ||
            (isr <= 0 && pevent0 != 0 &&
             pevent0 == event_addr(sg, eid) &&
             coq_prop(valid_event_id(sg, eid)) &&
             coq_prop(event_core_fields_layout_prop(
               sg, eid,
               &((OS_EVENT *)event_addr(sg, eid))->OSEventType,
               &((OS_EVENT *)event_addr(sg, eid))->OSEventPtr,
               &((OS_EVENT *)event_addr(sg, eid))->OSEventCnt)) &&
             coq_prop(mutex_post_public_event_domain_prop(
               sg, ls0, pevent, eid, e, etype, ecnt_in, owner_ptr, egrp_in,
               evtL_in, pcp_idx, prio_tbl_pcp, tcbcur, tcbprio,
               prioL_in, cur_tid, cur_t,
               &((OS_EVENT *)event_addr(sg, eid))->OSEventGrp,
               &((OS_EVENT *)event_addr(sg, eid))->OSEventTbl,
               &((OS_TCB *)tcbcur)->OSTCBPrio)))
        )
    Ensure
        exists (ls_post : UCOS2_Verify_State) (err : OSErrCode),
        safeExec(OSMutexPost_LastSeen(
                   sg, pevent0, ls0, err, ls_post),
                 return(encode_os_err_code(err)), X) &&
        OutsideCritical(sg, ls_post) &&
        mutex_post_rep(sg, ls0, ls_post) &&
        __return == encode_os_err_code(err) &&
        coq_prop(mutex_post_result_prop(
          sg, pevent0, ls0, ls_post, __return)) &&
        coq_prop(mutex_post_conditional_validity_prop(
          sg, pevent0, ls0, ls_post))
*/
{
    INT8U      pcp;
    INT8U      prio;
    OS_CPU_SR  cpu_sr = 0u;

    /*@ isr == intNesting(ls0.IntrState) &&
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
        UCOS2_Verify_inv(sg, ls0)
        which implies
        isr == intNesting(ls0.IntrState) &&
        data_at(&OSIntNesting, unsigned char, isr) *
        UCOS2_Verify_inv_no_int_nesting(sg, ls0) *
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
    */
    /*@ 0 <= isr && isr <= 255 by local */
    if (OSIntNesting > 0u) {
        return (OS_ERR_POST_ISR);
    }
    if (pevent == (OS_EVENT *)0) {
        return (OS_ERR_PEVENT_NULL);
    }
    /*@ isr == intNesting(ls0.IntrState) &&
        data_at(&OSIntNesting, unsigned char, isr) *
        UCOS2_Verify_inv_no_int_nesting(sg, ls0) *
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
        which implies
        isr == intNesting(ls0.IntrState) &&
        UCOS2_Verify_inv(sg, ls0) *
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
    */
    /*@ coq_prop(valid_event_id(sg, eid)) &&
        coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventType,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventPtr,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventCnt)) &&
        UCOS2_Verify_inv(sg, ls0)
        which implies
        data_at(&((OS_EVENT *)event_addr(sg, eid))->OSEventType, unsigned char,
                event_slot_type_value(ls0.EventState, eid)) *
        UCOS2_Verify_inv_no_event_type(sg, ls0, eid) *
        coq_prop(valid_event_id(sg, eid)) *
        coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventType,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventPtr,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventCnt))
    */
    if (pevent->OSEventType != OS_EVENT_TYPE_MUTEX) {
        /*@ exists (pevent_v: Z),
            coq_prop(valid_event_id(sg, eid)) &&
            coq_prop(mutex_post_public_event_domain_prop(
              sg, ls0, pevent_v, eid, e, etype, ecnt_in, owner_ptr,
              egrp_in, evtL_in, pcp_idx, prio_tbl_pcp, tcbcur,
              tcbprio, prioL_in, cur_tid, cur_t,
              &((OS_EVENT *)event_addr(sg, eid))->OSEventGrp,
              &((OS_EVENT *)event_addr(sg, eid))->OSEventTbl,
              &((OS_TCB *)tcbcur)->OSTCBPrio)) *
            coq_prop(event_core_fields_layout_prop(
              sg, eid,
              &((OS_EVENT *)event_addr(sg, eid))->OSEventType,
              &((OS_EVENT *)event_addr(sg, eid))->OSEventPtr,
              &((OS_EVENT *)event_addr(sg, eid))->OSEventCnt)) *
            data_at(&pevent, struct os_event *, pevent_v) *
            data_at(&((OS_EVENT *)pevent_v)->OSEventType, unsigned char,
                    event_slot_type_value(ls0.EventState, eid)) *
            UCOS2_Verify_inv_no_event_type(sg, ls0, eid)
            which implies
            coq_prop(mutex_post_public_event_domain_prop(
              sg, ls0, pevent_v, eid, e, etype, ecnt_in, owner_ptr,
              egrp_in, evtL_in, pcp_idx, prio_tbl_pcp, tcbcur,
              tcbprio, prioL_in, cur_tid, cur_t,
              &((OS_EVENT *)event_addr(sg, eid))->OSEventGrp,
              &((OS_EVENT *)event_addr(sg, eid))->OSEventTbl,
              &((OS_TCB *)tcbcur)->OSTCBPrio)) *
            coq_prop(event_core_fields_layout_prop(
              sg, eid,
              &((OS_EVENT *)event_addr(sg, eid))->OSEventType,
              &((OS_EVENT *)event_addr(sg, eid))->OSEventPtr,
              &((OS_EVENT *)event_addr(sg, eid))->OSEventCnt)) *
            data_at(&pevent, struct os_event *, pevent_v) *
            UCOS2_Verify_inv(sg, ls0)
        */
        return (OS_ERR_EVENT_TYPE);
    }
    /*@ exists (pevent_v: Z),
        coq_prop(valid_event_id(sg, eid)) &&
        coq_prop(mutex_post_public_event_domain_prop(
          sg, ls0, pevent_v, eid, e, etype, ecnt_in, owner_ptr,
          egrp_in, evtL_in, pcp_idx, prio_tbl_pcp, tcbcur,
          tcbprio, prioL_in, cur_tid, cur_t,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventGrp,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventTbl,
          &((OS_TCB *)tcbcur)->OSTCBPrio)) *
        coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventType,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventPtr,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventCnt)) *
        data_at(&pevent, struct os_event *, pevent_v) *
        data_at(&((OS_EVENT *)pevent_v)->OSEventType, unsigned char,
                event_slot_type_value(ls0.EventState, eid)) *
        UCOS2_Verify_inv_no_event_type(sg, ls0, eid)
        which implies
        coq_prop(mutex_post_public_event_domain_prop(
          sg, ls0, pevent_v, eid, e, etype, ecnt_in, owner_ptr,
          egrp_in, evtL_in, pcp_idx, prio_tbl_pcp, tcbcur,
          tcbprio, prioL_in, cur_tid, cur_t,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventGrp,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventTbl,
          &((OS_TCB *)tcbcur)->OSTCBPrio)) *
        coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventType,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventPtr,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventCnt)) *
        data_at(&pevent, struct os_event *, pevent_v) *
        UCOS2_Verify_inv(sg, ls0)
    */
    /*@ unsigned_last_nbits(
          event_slot_type_value(ls0.EventState, eid), 32) == 4 &&
        pevent0 == event_addr(sg, eid) &&
        coq_prop(mutex_post_public_event_domain_prop(
          sg, ls0, pevent, eid, e, etype, ecnt_in, owner_ptr, egrp_in,
          evtL_in, pcp_idx, prio_tbl_pcp, tcbcur, tcbprio,
          prioL_in, cur_tid, cur_t,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventGrp,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventTbl,
          &((OS_TCB *)tcbcur)->OSTCBPrio))
        which implies
        etype == 4 && tcbcur != 0 &&
        coq_prop(UCOS2_isr_or_task_call_boundary_prop(ls0)) &&
        pcp_idx == decode_PCP_from_cnt(ecnt_in) &&
        Znth(pcp_idx, prioL_in, 0) == prio_tbl_pcp &&
        data_at(&pevent, struct os_event *, pevent0) *
        coq_prop(event_snapshot_of_prop(
          sg, ls0.TskState, ls0.EventState, eid, e, etype,
          ecnt_in, owner_ptr, egrp_in, evtL_in)) *
        coq_prop(event_wait_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventGrp,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventTbl)) *
        coq_prop(prio_tbl_list_rel(sg, ls0.TskState, prioL_in)) *
        coq_prop(sched_tcb_cur_snapshot_prop(
          sg, ls0.SchedState, tcbcur)) *
        coq_prop(task_prio_snapshot_of_prop(
          sg, ls0.TskState, cur_tid, cur_t, tcbcur, tcbprio)) *
        coq_prop(task_prio_field_layout_prop(
          tcbcur, &((OS_TCB *)tcbcur)->OSTCBPrio))
    */
    /*@ coq_prop(event_snapshot_of_prop(
          sg, ls0.TskState, ls0.EventState, eid, e, etype,
          ecnt_in, owner_ptr, egrp_in, evtL_in)) &&
        coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventType,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventPtr,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventCnt)) &&
        coq_prop(event_wait_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventGrp,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventTbl)) &&
        coq_prop(UCOS2_isr_or_task_call_boundary_prop(ls0)) &&
        data_at(&pevent, struct os_event *, pevent0) *
        UCOS2_Verify_inv(sg, ls0)
        which implies
        coq_prop(event_snapshot_of_prop(
          sg, ls0.TskState, ls0.EventState, eid, e, etype,
          ecnt_in, owner_ptr, egrp_in, evtL_in)) *
        coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventType,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventPtr,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventCnt)) *
        coq_prop(event_wait_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventGrp,
          &((OS_EVENT *)event_addr(sg, eid))->OSEventTbl)) *
        coq_prop(UCOS2_isr_or_task_call_boundary_prop(ls0)) *
        data_at(&pevent, struct os_event *, pevent0) *
        data_at(&((OS_EVENT *)event_addr(sg, eid))->OSEventType, unsigned char, etype) *
        data_at(&((OS_EVENT *)event_addr(sg, eid))->OSEventPtr, void *, owner_ptr) *
        data_at(&((OS_EVENT *)event_addr(sg, eid))->OSEventCnt, unsigned short, ecnt_in) *
        data_at(&((OS_EVENT *)event_addr(sg, eid))->OSEventGrp, unsigned char, egrp_in) *
        data_at(&((OS_EVENT *)event_addr(sg, eid))->OSEventTbl[0], unsigned char, Znth(0, evtL_in, 0)) *
        data_at(&((OS_EVENT *)event_addr(sg, eid))->OSEventTbl[1], unsigned char, Znth(1, evtL_in, 0)) *
        data_at(&((OS_EVENT *)event_addr(sg, eid))->OSEventTbl[2], unsigned char, Znth(2, evtL_in, 0)) *
        data_at(&((OS_EVENT *)event_addr(sg, eid))->OSEventTbl[3], unsigned char, Znth(3, evtL_in, 0)) *
        data_at(&((OS_EVENT *)event_addr(sg, eid))->OSEventTbl[4], unsigned char, Znth(4, evtL_in, 0)) *
        data_at(&((OS_EVENT *)event_addr(sg, eid))->OSEventTbl[5], unsigned char, Znth(5, evtL_in, 0)) *
        data_at(&((OS_EVENT *)event_addr(sg, eid))->OSEventTbl[6], unsigned char, Znth(6, evtL_in, 0)) *
        data_at(&((OS_EVENT *)event_addr(sg, eid))->OSEventTbl[7], unsigned char, Znth(7, evtL_in, 0)) *
        interrupt_inv(sg, ls0.IntrState) *
        task_inv(sg, ls0.TskState) *
        sched_inv(sg, ls0.TskState, ls0.SchedState) *
        event_inv_no_eid(sg, ls0.TskState, ls0.EventState, eid) *
        tick_inv(sg, ls0.TickState) *
        coq_prop(cross_module_consistency(sg, ls0)) *
        coq_prop(UCOS2_state_inv(sg, ls0))
    */
    /*@ Assert
        exists (cpu_sr_v: Z),
        data_at(&cpu_sr, unsigned int, cpu_sr_v) *
        undef_data_at(&pcp, unsigned char) *
        undef_data_at(&prio, unsigned char) *
        data_at(&pevent, struct os_event *, pevent0) *
        data_at(&pevent->OSEventType, unsigned char, etype) *
        data_at(&pevent->OSEventPtr, void *, owner_ptr) *
        data_at(&pevent->OSEventCnt, unsigned short, ecnt_in) *
        data_at(&pevent->OSEventGrp, unsigned char, egrp_in) *
        data_at(&pevent->OSEventTbl[0], unsigned char, Znth(0, evtL_in, 0)) *
        data_at(&pevent->OSEventTbl[1], unsigned char, Znth(1, evtL_in, 0)) *
        data_at(&pevent->OSEventTbl[2], unsigned char, Znth(2, evtL_in, 0)) *
        data_at(&pevent->OSEventTbl[3], unsigned char, Znth(3, evtL_in, 0)) *
        data_at(&pevent->OSEventTbl[4], unsigned char, Znth(4, evtL_in, 0)) *
        data_at(&pevent->OSEventTbl[5], unsigned char, Znth(5, evtL_in, 0)) *
        data_at(&pevent->OSEventTbl[6], unsigned char, Znth(6, evtL_in, 0)) *
        data_at(&pevent->OSEventTbl[7], unsigned char, Znth(7, evtL_in, 0)) *
        interrupt_inv(sg, ls0.IntrState) *
        task_inv(sg, ls0.TskState) *
        sched_inv(sg, ls0.TskState, ls0.SchedState) *
        event_inv_no_eid(sg, ls0.TskState, ls0.EventState, eid) *
        tick_inv(sg, ls0.TickState) *
        coq_prop(cross_module_consistency(sg, ls0)) *
        OutsideCritical(sg, ls0) &&
        coq_prop(UCOS2_state_inv(sg, ls0)) &&
        coq_prop(UCOS2_isr_or_task_call_boundary_prop(ls0)) &&
        coq_prop(valid_stable_glob_vars(sg)) &&
        coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) &&
        coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
        pevent == pevent0 &&
        pevent == event_addr(sg, eid) && etype == 4 &&
        coq_prop(mutex_post_checked_entry_prop(ls0, pevent0)) &&
        coq_prop(event_snapshot_of_prop(
          sg, ls0.TskState, ls0.EventState, eid, e, etype,
          ecnt_in, owner_ptr, egrp_in, evtL_in)) &&
        coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &pevent->OSEventType,
          &pevent->OSEventPtr,
          &pevent->OSEventCnt)) &&
        coq_prop(event_wait_fields_layout_prop(
          sg, eid,
          &pevent->OSEventGrp,
          &pevent->OSEventTbl)) &&
        pcp_idx == decode_PCP_from_cnt(ecnt_in) &&
        coq_prop(prio_tbl_list_rel(sg, ls0.TskState, prioL_in)) &&
        Znth(pcp_idx, prioL_in, 0) == prio_tbl_pcp &&
        coq_prop(sched_tcb_cur_snapshot_prop(
          sg, ls0.SchedState, tcbcur)) &&
        coq_prop(task_prio_snapshot_of_prop(
          sg, ls0.TskState, cur_tid, cur_t, tcbcur, tcbprio)) &&
        coq_prop(task_prio_field_layout_prop(
          tcbcur, &((OS_TCB *)tcbcur)->OSTCBPrio)) &&
        safeExec(LastSeen(ls0),
                 bind(OSMutexPost_atomic_cmd(sg, ls0, pevent0),
                      observe_os_err_code), X)
    */
    OS_ENTER_CRITICAL()/*@ where sg = sg, ls0 = ls0, eid = eid */;
    pcp  = (INT8U)(pevent->OSEventCnt >> 8u);
    prio = (INT8U)(pevent->OSEventCnt & OS_MUTEX_KEEP_LOWER_8);
    /*@ Assert
        exists (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (pcp_v: Z) (prio_v: Z),
          safeExec(LastSeen(ls0),
                   bind(OSMutexPost_atomic_cmd(sg, ls0, pevent0),
                         observe_os_err_code), X) &&
          coq_prop(UCOS2_state_inv(sg, ls0)) &&
          coq_prop(UCOS2_isr_or_task_call_boundary_prop(ls0)) &&
          coq_prop(crit_rel_no_os_state_change(ls0, ls1)) &&
          coq_prop(mutex_post_checked_entry_prop(ls0, pevent0)) &&
          InsideCritical(sg, ls1) &&
          pevent == pevent0 &&
          pevent == event_addr(sg, eid) &&
          tcbcur != 0 &&
          coq_prop(valid_event_id(sg, eid)) &&
          interrupt_inv(sg, ls1.IntrState) *
          data_at(&((OS_TCB *)tcbcur)->OSTCBPrio, unsigned char, tcbprio) *
          used_task_no_prio(sg, tcbcur, cur_tid, cur_t) *
          task_inv_no_tid_priotbl(sg, ls1.TskState, cur_tid) *
          store_priotbl_list(sg, prioL_in) *
          data_at(&OSTCBCur, struct os_tcb *, tcbcur) *
          sched_inv_no_tcb_cur(sg, ls1.TskState, ls1.SchedState) *
          data_at(&pevent->OSEventType, unsigned char, 4) *
          data_at(&pevent->OSEventCnt, unsigned short, ecnt_in) *
          data_at(&pevent->OSEventPtr, void *, owner_ptr) *
          data_at(&pevent->OSEventGrp, unsigned char, egrp_in) *
          data_at(&pevent->OSEventTbl[0], unsigned char, Znth(0, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[1], unsigned char, Znth(1, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[2], unsigned char, Znth(2, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[3], unsigned char, Znth(3, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[4], unsigned char, Znth(4, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[5], unsigned char, Znth(5, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[6], unsigned char, Znth(6, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[7], unsigned char, Znth(7, evtL_in, 0)) *
          event_inv_no_eid(sg, ls1.TskState, ls1.EventState, eid) *
          tick_inv(sg, ls1.TickState) *
          coq_prop(cross_module_consistency(sg, ls1)) *
          data_at(&cpu_sr, unsigned int, cpu_sr_v) *
          data_at(&pcp, unsigned char, pcp_v) *
          data_at(&prio, unsigned char, prio_v) &&
          coq_prop(valid_stable_glob_vars(sg)) &&
          coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(task_prio_field_layout_prop(
            tcbcur, &((OS_TCB *)tcbcur)->OSTCBPrio)) &&
          coq_prop(valid_mutex_pcp(sg, pcp_idx)) &&
          coq_prop(event_snapshot_of_prop(
            sg, ls1.TskState, ls1.EventState, eid, e, 4,
            ecnt_in, owner_ptr, egrp_in, evtL_in)) &&
          coq_prop(event_core_fields_layout_prop(
            sg, eid,
            &pevent->OSEventType,
            &pevent->OSEventPtr,
            &pevent->OSEventCnt)) &&
          coq_prop(event_wait_fields_layout_prop(
            sg, eid,
            &pevent->OSEventGrp,
            &pevent->OSEventTbl)) &&
          coq_prop(sched_tcb_cur_snapshot_prop(
            sg, ls1.SchedState, tcbcur)) &&
          coq_prop(task_prio_snapshot_of_prop(
            sg, ls1.TskState, cur_tid, cur_t, tcbcur, tcbprio)) &&
          coq_prop(prio_tbl_list_rel(
            sg, ls1.TskState, prioL_in)) &&
          Znth(pcp_idx, prioL_in, 0) == prio_tbl_pcp &&
          pcp_v == pcp_idx &&
          pcp_v == decode_PCP_from_cnt(ecnt_in) &&
          prio_v == decode_OwnerPrio_from_cnt(ecnt_in)
    */
    if (OSTCBCur != (OS_TCB *)pevent->OSEventPtr) {
        /*@
            exists (ls_cs: UCOS2_Verify_State),
            InsideCritical(sg, ls_cs) &&
            coq_prop(crit_rel_no_os_state_change(ls0, ls_cs))
            which implies
            InsideCritical(sg, ls_cs) &&
            coq_prop(crit_rel_no_os_state_change(ls0, ls_cs)) &&
            coq_prop(crit_rel_task_event_sched(ls_cs, ls0))
        */
        OS_EXIT_CRITICAL()/*@ where sg = sg, eid = eid */;
        return (OS_ERR_NOT_MUTEX_OWNER);
    }
    /*@ Assert
        exists (ls1: UCOS2_Verify_State) (cpu_sr_v: Z)
               (pcp_v: Z) (prio_v: Z),
          safeExec(LastSeen(ls0),
                   bind(OSMutexPost_atomic_cmd(sg, ls0, pevent0),
                         observe_os_err_code), X) &&
          coq_prop(UCOS2_state_inv(sg, ls0)) &&
          coq_prop(mutex_post_owner_entry_context_prop(
            sg, pevent0, eid, ls0, ls1, pcp_idx,
            decode_OwnerPrio_from_cnt(ecnt_in), tcbcur, tcbprio)) &&
          InsideCritical(sg, ls1) &&
          pevent == pevent0 &&
          pevent == event_addr(sg, eid) &&
          owner_ptr == tcbcur &&
          coq_prop(valid_event_id(sg, eid)) &&
          interrupt_inv(sg, ls1.IntrState) *
          data_at(&((OS_TCB *)tcbcur)->OSTCBPrio, unsigned char, tcbprio) *
          used_task_no_prio(sg, tcbcur, cur_tid, cur_t) *
          task_inv_no_tid_priotbl(sg, ls1.TskState, cur_tid) *
          store_priotbl_list(sg, prioL_in) *
          data_at(&OSTCBCur, struct os_tcb *, tcbcur) *
          sched_inv_no_tcb_cur(sg, ls1.TskState, ls1.SchedState) *
          data_at(&pevent->OSEventType, unsigned char, 4) *
          data_at(&pevent->OSEventCnt, unsigned short, ecnt_in) *
          data_at(&pevent->OSEventPtr, void *, owner_ptr) *
          data_at(&pevent->OSEventGrp, unsigned char, egrp_in) *
          data_at(&pevent->OSEventTbl[0], unsigned char, Znth(0, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[1], unsigned char, Znth(1, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[2], unsigned char, Znth(2, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[3], unsigned char, Znth(3, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[4], unsigned char, Znth(4, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[5], unsigned char, Znth(5, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[6], unsigned char, Znth(6, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[7], unsigned char, Znth(7, evtL_in, 0)) *
          event_inv_no_eid(sg, ls1.TskState, ls1.EventState, eid) *
          tick_inv(sg, ls1.TickState) *
          coq_prop(cross_module_consistency(sg, ls1)) *
          data_at(&cpu_sr, unsigned int, cpu_sr_v) *
          data_at(&pcp, unsigned char, pcp_v) *
          data_at(&prio, unsigned char, prio_v) &&
          coq_prop(valid_stable_glob_vars(sg)) &&
          coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(task_prio_field_layout_prop(
            tcbcur, &((OS_TCB *)tcbcur)->OSTCBPrio)) &&
          coq_prop(valid_mutex_pcp(sg, pcp_idx)) &&
          coq_prop(event_snapshot_of_prop(
            sg, ls1.TskState, ls1.EventState, eid, e, 4,
            ecnt_in, owner_ptr, egrp_in, evtL_in)) &&
          coq_prop(event_core_fields_layout_prop(
            sg, eid,
            &pevent->OSEventType,
            &pevent->OSEventPtr,
            &pevent->OSEventCnt)) &&
          coq_prop(event_wait_fields_layout_prop(
            sg, eid,
            &pevent->OSEventGrp,
            &pevent->OSEventTbl)) &&
          coq_prop(task_prio_snapshot_of_prop(
            sg, ls1.TskState, cur_tid, cur_t, tcbcur, tcbprio)) &&
          coq_prop(prio_tbl_list_rel(
            sg, ls1.TskState, prioL_in)) &&
          Znth(pcp_idx, prioL_in, 0) == prio_tbl_pcp &&
          pcp_v == pcp_idx &&
          pcp_v == decode_PCP_from_cnt(ecnt_in) &&
          prio_v == decode_OwnerPrio_from_cnt(ecnt_in)
    */
    if (pcp != OS_PRIO_MUTEX_CEIL_DIS) {
        if (OSTCBCur->OSTCBPrio == pcp) {
            /*@ Assert
                exists (ls_rdy_pre: UCOS2_Verify_State) Xrdy
                       (cpu_sr_v: Z) (pcp_v: Z) (prio_v: Z),
                  safeExec(LastSeen(ls0),
                           bind(OSMutexPost_atomic_cmd(sg, ls0, pevent0),
                                observe_os_err_code), X) &&
                  coq_prop(UCOS2_state_inv(sg, ls0)) &&
                  coq_prop(mutex_post_owner_entry_context_prop(
                    sg, pevent0, eid, ls0, ls_rdy_pre, pcp_idx,
                    decode_OwnerPrio_from_cnt(ecnt_in),
                    tcbcur, pcp_idx)) &&
                  safeExec(LastSeen(ls_rdy_pre),
                           bind(OSMutexPost_RdyAtPrio_atomic_cmd(
                                  sg, ls_rdy_pre, tcbcur, prio_v),
                                observe_unit_void), Xrdy) &&
                  InsideCritical(sg, ls_rdy_pre) &&
                  interrupt_inv(sg, ls_rdy_pre.IntrState) *
                  data_at(&((OS_TCB *)tcbcur)->OSTCBPrio,
                          unsigned char, tcbprio) *
                  used_task_no_prio(sg, tcbcur, cur_tid, cur_t) *
                  task_inv_no_tid_priotbl(
                    sg, ls_rdy_pre.TskState, cur_tid) *
                  store_priotbl_list(sg, prioL_in) *
                  data_at(&OSTCBCur, struct os_tcb *, tcbcur) *
                  sched_inv_no_tcb_cur(
                    sg, ls_rdy_pre.TskState, ls_rdy_pre.SchedState) *
                  data_at(&pevent->OSEventType, unsigned char, 4) *
                  data_at(&pevent->OSEventCnt, unsigned short, ecnt_in) *
                  data_at(&pevent->OSEventPtr, void *, owner_ptr) *
                  data_at(&pevent->OSEventGrp, unsigned char, egrp_in) *
                  data_at(&pevent->OSEventTbl[0], unsigned char,
                          Znth(0, evtL_in, 0)) *
                  data_at(&pevent->OSEventTbl[1], unsigned char,
                          Znth(1, evtL_in, 0)) *
                  data_at(&pevent->OSEventTbl[2], unsigned char,
                          Znth(2, evtL_in, 0)) *
                  data_at(&pevent->OSEventTbl[3], unsigned char,
                          Znth(3, evtL_in, 0)) *
                  data_at(&pevent->OSEventTbl[4], unsigned char,
                          Znth(4, evtL_in, 0)) *
                  data_at(&pevent->OSEventTbl[5], unsigned char,
                          Znth(5, evtL_in, 0)) *
                  data_at(&pevent->OSEventTbl[6], unsigned char,
                          Znth(6, evtL_in, 0)) *
                  data_at(&pevent->OSEventTbl[7], unsigned char,
                          Znth(7, evtL_in, 0)) *
                  event_inv_no_eid(
                    sg, ls_rdy_pre.TskState, ls_rdy_pre.EventState, eid) *
                  tick_inv(sg, ls_rdy_pre.TickState) *
                  coq_prop(cross_module_consistency(sg, ls_rdy_pre)) *
                  data_at(&cpu_sr, unsigned int, cpu_sr_v) *
                  data_at(&pcp, unsigned char, pcp_v) *
                  data_at(&prio, unsigned char, prio_v) &&
                  coq_prop(event_snapshot_of_prop(
                    sg, ls_rdy_pre.TskState, ls_rdy_pre.EventState,
                    eid, e, 4, ecnt_in, owner_ptr, egrp_in, evtL_in)) &&
                  coq_prop(event_core_fields_layout_prop(
                    sg, eid,
                    &pevent->OSEventType,
                    &pevent->OSEventPtr,
                    &pevent->OSEventCnt)) &&
                  coq_prop(event_wait_fields_layout_prop(
                    sg, eid,
                    &pevent->OSEventGrp,
                    &pevent->OSEventTbl)) &&
                  coq_prop(prio_tbl_list_rel(
                    sg, ls_rdy_pre.TskState, prioL_in)) &&
                  coq_prop(valid_stable_glob_vars(sg)) &&
                  coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) &&
                  coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
                  coq_prop(task_prio_field_layout_prop(
                    tcbcur, &((OS_TCB *)tcbcur)->OSTCBPrio)) &&
                  coq_prop(task_prio_snapshot_of_prop(
                    sg, ls_rdy_pre.TskState, cur_tid, cur_t,
                    tcbcur, tcbprio)) &&
                  pevent == pevent0 &&
                  pcp_v == pcp_idx &&
                  pcp_idx != 255 &&
                  tcbprio == pcp_idx &&
                  owner_ptr == tcbcur &&
                  prio_v == decode_OwnerPrio_from_cnt(ecnt_in) &&
                  Znth(pcp_idx, prioL_in, 0) == prio_tbl_pcp
            */
            OSMutex_RdyAtPrio(OSTCBCur, prio)
            /*@ where sg = sg, ls0 = ls0,
                       pe0 = pevent0, eid = eid, e0 = e,
                       cur_tid0 = cur_tid, cur_t0 = cur_t,
                       tcbprio0 = tcbprio, ecnt0 = ecnt_in,
                       owner_ptr0 = owner_ptr, egrp0 = egrp_in,
                       evtL0 = evtL_in, prioL0 = prioL_in,
                       pcp0 = pcp_idx,
                       owner_orig0 = decode_OwnerPrio_from_cnt(ecnt_in) */;
        }
        /*@ Assert
            exists (ls_d: UCOS2_Verify_State)
                   (cpu_sr_v: Z) (pcp_v: Z) (prio_v: Z),
              safeExec(LastSeen(ls0),
                       bind(OSMutexPost_atomic_cmd(sg, ls0, pevent0),
                            observe_os_err_code), X) &&
              coq_prop(UCOS2_state_inv(sg, ls0)) &&
              coq_prop(mutex_post_owner_disinherit_stage_prop(
                sg, pevent0, ls0, pcp_idx,
                decode_OwnerPrio_from_cnt(ecnt_in), ls_d)) &&
              coq_prop(valid_stable_glob_vars(sg)) &&
              coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
              coq_prop(valid_mutex_pcp(sg, pcp_idx)) &&
              coq_prop(valid_event_id(sg, eid)) &&
              coq_prop(event_raw_snapshot_of_prop(
                sg, ls_d.TskState, ls_d.EventState, eid, e, 4,
                ecnt_in, owner_ptr, egrp_in, evtL_in)) &&
              coq_prop(event_core_fields_layout_prop(
                sg, eid,
                &pevent->OSEventType,
                &pevent->OSEventPtr,
                &pevent->OSEventCnt)) &&
              coq_prop(event_wait_fields_layout_prop(
                sg, eid,
                &pevent->OSEventGrp,
                &pevent->OSEventTbl)) &&
              InsideCritical(sg, ls0) &&
              mutex_post_rep(sg, ls0, ls_d) *
              data_at(&cpu_sr, unsigned int, cpu_sr_v) *
              data_at(&pcp, unsigned char, pcp_v) *
              data_at(&prio, unsigned char, prio_v) &&
              pevent == pevent0 &&
              pevent == event_addr(sg, eid) &&
              pcp_v == pcp_idx && pcp_idx != 255 &&
              0 <= pcp_idx && pcp_idx < 64
        */
        /*@ Assert
            exists (ls_d: UCOS2_Verify_State) (prioL_d: list addr)
                   (cpu_sr_v: Z) (pcp_v: Z) (prio_v: Z),
              safeExec(LastSeen(ls0),
                       bind(OSMutexPost_atomic_cmd(sg, ls0, pevent0),
                            observe_os_err_code), X) &&
              coq_prop(UCOS2_state_inv(sg, ls0)) &&
              coq_prop(mutex_post_owner_disinherit_stage_prop(
                sg, pevent0, ls0, pcp_idx,
                decode_OwnerPrio_from_cnt(ecnt_in), ls_d)) &&
              coq_prop(prio_tbl_list_rel(
                sg, ls_d.TskState, prioL_d)) &&
              coq_prop(valid_stable_glob_vars(sg)) &&
              coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
              coq_prop(valid_mutex_pcp(sg, pcp_idx)) &&
              coq_prop(valid_event_id(sg, eid)) &&
              coq_prop(event_raw_snapshot_of_prop(
                sg, ls_d.TskState, ls_d.EventState, eid, e, 4,
                ecnt_in, owner_ptr, egrp_in, evtL_in)) &&
              coq_prop(event_core_fields_layout_prop(
                sg, eid,
                &pevent->OSEventType,
                &pevent->OSEventPtr,
                &pevent->OSEventCnt)) &&
              coq_prop(event_wait_fields_layout_prop(
                sg, eid,
                &pevent->OSEventGrp,
                &pevent->OSEventTbl)) &&
              InsideCritical(sg, ls0) &&
              store_priotbl_list(sg, prioL_d) *
              mutex_post_rep_no_priotbl_no_event(
                sg, ls0, ls_d, eid) *
              data_at(&pevent->OSEventType, unsigned char, 4) *
              data_at(&pevent->OSEventCnt, unsigned short, ecnt_in) *
              data_at(&pevent->OSEventPtr, void *, owner_ptr) *
              data_at(&pevent->OSEventGrp, unsigned char, egrp_in) *
              data_at(&pevent->OSEventTbl[0], unsigned char,
                      Znth(0, evtL_in, 0)) *
              data_at(&pevent->OSEventTbl[1], unsigned char,
                      Znth(1, evtL_in, 0)) *
              data_at(&pevent->OSEventTbl[2], unsigned char,
                      Znth(2, evtL_in, 0)) *
              data_at(&pevent->OSEventTbl[3], unsigned char,
                      Znth(3, evtL_in, 0)) *
              data_at(&pevent->OSEventTbl[4], unsigned char,
                      Znth(4, evtL_in, 0)) *
              data_at(&pevent->OSEventTbl[5], unsigned char,
                      Znth(5, evtL_in, 0)) *
              data_at(&pevent->OSEventTbl[6], unsigned char,
                      Znth(6, evtL_in, 0)) *
              data_at(&pevent->OSEventTbl[7], unsigned char,
                      Znth(7, evtL_in, 0)) *
              data_at(&cpu_sr, unsigned int, cpu_sr_v) *
              data_at(&pcp, unsigned char, pcp_v) *
              data_at(&prio, unsigned char, prio_v) &&
              pevent == pevent0 &&
              pevent == event_addr(sg, eid) &&
              pcp_v == pcp_idx && pcp_idx != 255 &&
              0 <= pcp_idx && pcp_idx < 64
        */
        /*@
            exists (prioL_d: list addr),
            coq_prop(valid_stable_glob_vars(sg)) &&
            coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
            coq_prop(valid_mutex_pcp(sg, pcp_idx)) &&
            pcp_idx != 255 && 0 <= pcp_idx && pcp_idx < 64 &&
            pcp_idx == pcp &&
            store_priotbl_list(sg, prioL_d)
            which implies
            coq_prop(valid_stable_glob_vars(sg)) &&
            coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
            coq_prop(valid_mutex_pcp(sg, pcp_idx)) &&
            pcp_idx != 255 && 0 <= pcp_idx && pcp_idx < 64 &&
            pcp_idx == pcp &&
            data_at(&OSTCBPrioTbl[pcp], Znth(pcp_idx, prioL_d, 0)) *
            store_priotbl_list_missing_i(sg, prioL_d, pcp_idx)
        */
        OSTCBPrioTbl[pcp] = OS_TCB_RESERVED;
    }
    /*@ Assert
        exists (ls2: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State)
               (cpu_sr_v: Z) (pcp_v: Z) (prio_v: Z),
          safeExec(LastSeen(ls0),
                   bind(OSMutexPost_atomic_cmd(sg, ls0, pevent0),
                        observe_os_err_code), X) &&
          coq_prop(UCOS2_state_inv(sg, ls0)) &&
          coq_prop(mutex_post_owner_disinherit_stage_prop(
            sg, pevent0, ls0, pcp_idx,
            decode_OwnerPrio_from_cnt(ecnt_in), ls_d)) &&
          coq_prop(mutex_post_reservation_stage_prop(
            sg, eid, ls_d, ls2)) &&
          coq_prop(valid_stable_glob_vars(sg)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(valid_mutex_pcp(sg, pcp_idx)) &&
          coq_prop(event_raw_snapshot_of_prop(
            sg, ls2.TskState, ls2.EventState, eid, e, 4,
            ecnt_in, owner_ptr, egrp_in, evtL_in)) &&
          coq_prop(event_core_fields_layout_prop(
            sg, eid,
            &pevent->OSEventType,
            &pevent->OSEventPtr,
            &pevent->OSEventCnt)) &&
          coq_prop(event_wait_fields_layout_prop(
            sg, eid,
            &pevent->OSEventGrp,
            &pevent->OSEventTbl)) &&
          InsideCritical(sg, ls0) &&
          pevent == pevent0 &&
          pevent == event_addr(sg, eid) &&
          coq_prop(valid_event_id(sg, eid)) &&
          mutex_post_rep_no_event(sg, ls0, ls2, eid) *
          data_at(&pevent->OSEventType, unsigned char, 4) *
          data_at(&pevent->OSEventCnt, unsigned short, ecnt_in) *
          data_at(&pevent->OSEventPtr, void *, owner_ptr) *
          data_at(&pevent->OSEventGrp, unsigned char, egrp_in) *
          data_at(&pevent->OSEventTbl[0], unsigned char,
                  Znth(0, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[1], unsigned char,
                  Znth(1, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[2], unsigned char,
                  Znth(2, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[3], unsigned char,
                  Znth(3, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[4], unsigned char,
                  Znth(4, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[5], unsigned char,
                  Znth(5, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[6], unsigned char,
                  Znth(6, evtL_in, 0)) *
          data_at(&pevent->OSEventTbl[7], unsigned char,
                  Znth(7, evtL_in, 0)) *
          data_at(&cpu_sr, unsigned int, cpu_sr_v) *
          data_at(&pcp, unsigned char, pcp_v) *
          data_at(&prio, unsigned char, prio_v) &&
          pcp_v == pcp_idx
    */
    if (pevent->OSEventGrp != 0u) {
        prio                = OS_EventTaskRdy(pevent, (void *)0, OS_STAT_MUTEX, OS_STAT_PEND_OK)
        /*@ where sg = sg, eid = eid, ls0_post = ls0, pe0 = pevent0,
                   pcp0 = pcp_idx,
                   owner_orig0 = decode_OwnerPrio_from_cnt(ecnt_in),
                   e0 = e, ecnt0 = ecnt_in, owner_ptr0 = owner_ptr,
                   egrp_in = egrp_in, evtL0 = evtL_in */;
        pevent->OSEventCnt &= OS_MUTEX_KEEP_UPPER_8;
        pevent->OSEventCnt |= (INT16U)prio;
        /*@ Assert
            exists (ls_wake: UCOS2_Verify_State)
                   (ls_cnt: UCOS2_Verify_State)
                   (ls_r: UCOS2_Verify_State)
                   (ls_d0: UCOS2_Verify_State)
                   (canonical_waiter: TaskID) (table_owner: TaskID)
                   (e_h: OSEventAbstractState)
                   (prioL_h: list addr) (cnt_h: Z) (ptr_h: addr)
                   (egrp_h: Z) (evtL_h: list Z)
                   (cpu_sr_v: Z) (pcp_v: Z) (prio_v: Z),
              safeExec(LastSeen(ls0),
                       bind(OSMutexPost_atomic_cmd(sg, ls0, pevent0),
                            observe_os_err_code), X) &&
              coq_prop(UCOS2_state_inv(sg, ls0)) &&
              coq_prop(mutex_post_owner_disinherit_stage_prop(
                sg, pevent0, ls0, pcp_idx,
                decode_OwnerPrio_from_cnt(ecnt_in), ls_d0)) &&
              coq_prop(mutex_post_reservation_stage_prop(
                sg, eid, ls_d0, ls_r)) &&
              coq_prop(event_raw_snapshot_of_prop(
                sg, ls_r.TskState, ls_r.EventState, eid, e, 4,
                ecnt_in, owner_ptr, egrp_in, evtL_in)) &&
              coq_prop(mutex_post_wake_step_prop(
                sg, eid, ls_r, prio_v,
                canonical_waiter, table_owner, ls_wake)) &&
              coq_prop(mutex_post_count_commit_step_prop(
                eid, prio_v, ls_wake, ls_cnt)) &&
              coq_prop(event_raw_snapshot_of_prop(
                sg, ls_cnt.TskState, ls_cnt.EventState, eid, e_h, 4,
                cnt_h, ptr_h, egrp_h, evtL_h)) &&
              coq_prop(valid_stable_glob_vars(sg)) &&
              coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
              coq_prop(should_be_equal(
                ls_cnt.TskState.prioTbl(prio_v), PTTask(table_owner))) &&
              coq_prop(prio_tbl_list_rel(
                sg, ls_cnt.TskState, prioL_h)) &&
              coq_prop(valid_event_id(sg, eid)) &&
              coq_prop(event_core_fields_layout_prop(
                sg, eid,
                &pevent->OSEventType,
                &pevent->OSEventPtr,
                &pevent->OSEventCnt)) &&
              coq_prop(event_wait_fields_layout_prop(
                sg, eid,
                &pevent->OSEventGrp,
                &pevent->OSEventTbl)) &&
              InsideCritical(sg, ls0) &&
              mutex_post_handover_residual_no_priotbl(
                sg, ls0, ls_cnt, eid) *
              store_priotbl_list(sg, prioL_h) *
              data_at(&pevent->OSEventType, unsigned char, 4) *
              data_at(&pevent->OSEventCnt, unsigned short, cnt_h) *
              data_at(&pevent->OSEventPtr, void *, owner_ptr) *
              data_at(&pevent->OSEventGrp, unsigned char, egrp_h) *
              data_at(&pevent->OSEventTbl[0], unsigned char,
                      Znth(0, evtL_h, 0)) *
              data_at(&pevent->OSEventTbl[1], unsigned char,
                      Znth(1, evtL_h, 0)) *
              data_at(&pevent->OSEventTbl[2], unsigned char,
                      Znth(2, evtL_h, 0)) *
              data_at(&pevent->OSEventTbl[3], unsigned char,
                      Znth(3, evtL_h, 0)) *
              data_at(&pevent->OSEventTbl[4], unsigned char,
                      Znth(4, evtL_h, 0)) *
              data_at(&pevent->OSEventTbl[5], unsigned char,
                      Znth(5, evtL_h, 0)) *
              data_at(&pevent->OSEventTbl[6], unsigned char,
                      Znth(6, evtL_h, 0)) *
              data_at(&pevent->OSEventTbl[7], unsigned char,
                      Znth(7, evtL_h, 0)) *
              data_at(&cpu_sr, unsigned int, cpu_sr_v) *
              data_at(&pcp, unsigned char, pcp_v) *
              data_at(&prio, unsigned char, prio_v) &&
              pevent == pevent0 &&
              pevent == event_addr(sg, eid) &&
              pcp_v == pcp_idx &&
              0 <= prio_v && prio_v < 64 &&
              Znth(prio_v, prioL_h, 0) == tcb_addr(sg, table_owner)
        */
        /*@
            exists (table_owner: TaskID) (prioL_h: list addr) (prio_v: Z),
            coq_prop(valid_stable_glob_vars(sg)) &&
            coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
            0 <= prio_v && prio_v < 64 && prio_v == prio &&
            Znth(prio_v, prioL_h, 0) == tcb_addr(sg, table_owner) &&
            store_priotbl_list(sg, prioL_h)
            which implies
            coq_prop(valid_stable_glob_vars(sg)) &&
            coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
            data_at(&OSTCBPrioTbl[prio], tcb_addr(sg, table_owner)) *
            store_priotbl_list_missing_i(sg, prioL_h, prio_v)
        */
        pevent->OSEventPtr  = OSTCBPrioTbl[prio];
        /*@ Assert
            exists (ls_h: UCOS2_Verify_State)
                   (ls_cnt: UCOS2_Verify_State)
                   (ls_wake: UCOS2_Verify_State)
                   (ls_r: UCOS2_Verify_State)
                   (ls_d: UCOS2_Verify_State) (e_h: OSEventAbstractState)
                   (canonical_waiter: TaskID) (table_owner: TaskID)
                   (cpu_sr_v: Z)
                   (pcp_v: Z) (prio_v: Z) (cnt_h: Z)
                   (ptr_h: addr) (grp_h: Z) (tbl_h: list Z),
            safeExec(LastSeen(ls0),
                     bind(OSMutexPost_atomic_cmd(sg, ls0, pevent0),
                          observe_os_err_code), X) &&
            coq_prop(UCOS2_state_inv(sg, ls0)) &&
            coq_prop(mutex_post_owner_disinherit_stage_prop(
              sg, pevent0, ls0, pcp_idx,
              decode_OwnerPrio_from_cnt(ecnt_in), ls_d)) &&
            coq_prop(mutex_post_reservation_stage_prop(
              sg, eid, ls_d, ls_r)) &&
            coq_prop(event_raw_snapshot_of_prop(
              sg, ls_r.TskState, ls_r.EventState, eid, e, 4,
              ecnt_in, owner_ptr, egrp_in, evtL_in)) &&
            coq_prop(mutex_post_wake_step_prop(
              sg, eid, ls_r, prio_v,
              canonical_waiter, table_owner, ls_wake)) &&
            coq_prop(mutex_post_count_commit_step_prop(
              eid, prio_v, ls_wake, ls_cnt)) &&
            coq_prop(mutex_post_owner_commit_step_prop(
              eid, prio_v, table_owner, ls_cnt, ls_h)) &&
            coq_prop(mutex_post_handover_step_prop(
              sg, eid, ls_d, prio_v,
              canonical_waiter, table_owner, ls_h)) &&
            coq_prop(crit_rel_task_event_sched(ls0, ls_h)) &&
            coq_prop(valid_stable_glob_vars(sg)) &&
            coq_prop(event_raw_snapshot_of_prop(
              sg, ls_h.TskState, ls_h.EventState, eid, e_h, 4,
              cnt_h, ptr_h, grp_h, tbl_h)) &&
            coq_prop(event_core_fields_layout_prop(
              sg, eid,
              &pevent->OSEventType,
              &pevent->OSEventPtr,
              &pevent->OSEventCnt)) &&
            coq_prop(event_wait_fields_layout_prop(
              sg, eid,
              &pevent->OSEventGrp,
              &pevent->OSEventTbl)) &&
            coq_prop(valid_event_id(sg, eid)) &&
            InsideCritical(sg, ls0) &&
            UCOS2_raw_ready_prio_stage(sg, ls0, ls_h) *
            data_at(&cpu_sr, unsigned int, cpu_sr_v) *
            data_at(&pcp, unsigned char, pcp_v) *
            data_at(&prio, unsigned char, prio_v) &&
            pevent == pevent0 &&
            pevent == event_addr(sg, eid) &&
            pcp_v == pcp_idx
        */
        if ((pcp  != OS_PRIO_MUTEX_CEIL_DIS) &&
            (prio <= pcp)) {
            OS_EXIT_CRITICAL()/*@ where sg = sg, eid = eid */;
            /*@ Assert
                exists (ls_h: UCOS2_Verify_State) (ls_r: UCOS2_Verify_State)
                       (ls_d: UCOS2_Verify_State)
                       (e_h: OSEventAbstractState)
                       (canonical_waiter: TaskID) (table_owner: TaskID)
                       (cnt_h: Z) (ptr_h: addr) (grp_h: Z)
                       (tbl_o: list Z) (cpu_sr_o: Z)
                       (pcp_o: Z) (prio_o: Z),
                safeExec(LastSeen(ls0),
                         bind(OSMutexPost_atomic_cmd(sg, ls0, pevent0),
                              observe_os_err_code), X) &&
                coq_prop(UCOS2_state_inv(sg, ls0)) &&
                coq_prop(mutex_post_owner_disinherit_stage_prop(
                  sg, pevent0, ls0, pcp_idx,
                  decode_OwnerPrio_from_cnt(ecnt_in), ls_d)) &&
                coq_prop(mutex_post_reservation_stage_prop(
                  sg, eid, ls_d, ls_r)) &&
                coq_prop(event_raw_snapshot_of_prop(
                  sg, ls_r.TskState, ls_r.EventState, eid, e, 4,
                  ecnt_in, owner_ptr, egrp_in, evtL_in)) &&
                coq_prop(mutex_post_handover_step_prop(
                  sg, eid, ls_d, prio_o,
                  canonical_waiter, table_owner, ls_h)) &&
                coq_prop(valid_stable_glob_vars(sg)) &&
                coq_prop(event_raw_snapshot_of_prop(
                  sg, ls_h.TskState, ls_h.EventState, eid, e_h,
                  4, cnt_h, ptr_h, grp_h, tbl_o)) &&
                coq_prop(event_core_fields_layout_prop(
                  sg, eid,
                  &pevent->OSEventType,
                  &pevent->OSEventPtr,
                  &pevent->OSEventCnt)) &&
                coq_prop(event_wait_fields_layout_prop(
                  sg, eid,
                  &pevent->OSEventGrp,
                  &pevent->OSEventTbl)) &&
                coq_prop(valid_event_id(sg, eid)) &&
                OutsideCritical(sg, ls_h) &&
                UCOS2_raw_ready_prio_stage(sg, ls0, ls_h) *
                data_at(&cpu_sr, unsigned int, cpu_sr_o) *
                data_at(&pcp, unsigned char, pcp_o) *
                data_at(&prio, unsigned char, prio_o) &&
                pevent == pevent0 &&
                pevent == event_addr(sg, eid) &&
                pcp_o == pcp_idx &&
                pcp_idx != 255 && prio_o <= pcp_idx
            */
            OS_Sched()/*@ where sg = sg, eid = eid,
                                 stage_entry = ls0 */;
            return (OS_ERR_PCP_LOWER);
        } else {
            OS_EXIT_CRITICAL()/*@ where sg = sg, eid = eid */;
            /*@ Assert
                exists (ls_h: UCOS2_Verify_State) (ls_r: UCOS2_Verify_State)
                       (ls_d: UCOS2_Verify_State)
                       (e_h: OSEventAbstractState)
                       (canonical_waiter: TaskID) (table_owner: TaskID)
                       (cnt_h: Z) (ptr_h: addr) (grp_h: Z)
                       (tbl_o: list Z) (cpu_sr_o: Z)
                       (pcp_o: Z) (prio_o: Z),
                safeExec(LastSeen(ls0),
                         bind(OSMutexPost_atomic_cmd(sg, ls0, pevent0),
                              observe_os_err_code), X) &&
                coq_prop(UCOS2_state_inv(sg, ls0)) &&
                coq_prop(mutex_post_owner_disinherit_stage_prop(
                  sg, pevent0, ls0, pcp_idx,
                  decode_OwnerPrio_from_cnt(ecnt_in), ls_d)) &&
                coq_prop(mutex_post_reservation_stage_prop(
                  sg, eid, ls_d, ls_r)) &&
                coq_prop(event_raw_snapshot_of_prop(
                  sg, ls_r.TskState, ls_r.EventState, eid, e, 4,
                  ecnt_in, owner_ptr, egrp_in, evtL_in)) &&
                coq_prop(mutex_post_handover_step_prop(
                  sg, eid, ls_d, prio_o,
                  canonical_waiter, table_owner, ls_h)) &&
                coq_prop(valid_stable_glob_vars(sg)) &&
                coq_prop(event_raw_snapshot_of_prop(
                  sg, ls_h.TskState, ls_h.EventState, eid, e_h,
                  4, cnt_h, ptr_h, grp_h, tbl_o)) &&
                coq_prop(event_core_fields_layout_prop(
                  sg, eid,
                  &pevent->OSEventType,
                  &pevent->OSEventPtr,
                  &pevent->OSEventCnt)) &&
                coq_prop(event_wait_fields_layout_prop(
                  sg, eid,
                  &pevent->OSEventGrp,
                  &pevent->OSEventTbl)) &&
                coq_prop(valid_event_id(sg, eid)) &&
                OutsideCritical(sg, ls_h) &&
                UCOS2_raw_ready_prio_stage(sg, ls0, ls_h) *
                data_at(&cpu_sr, unsigned int, cpu_sr_o) *
                data_at(&pcp, unsigned char, pcp_o) *
                data_at(&prio, unsigned char, prio_o) &&
                pevent == pevent0 &&
                pevent == event_addr(sg, eid) &&
                pcp_o == pcp_idx &&
                (pcp_idx == 255 || prio_o > pcp_idx)
            */
            OS_Sched()/*@ where sg = sg, eid = eid,
                                 stage_entry = ls0 */;
            return (OS_ERR_NONE);
        }
    }
    pevent->OSEventCnt |= OS_MUTEX_AVAILABLE;
    pevent->OSEventPtr  = (void *)0;
    /*@ Assert
        exists (ls_r: UCOS2_Verify_State)
               (ls_available: UCOS2_Verify_State)
               (ls_reserved: UCOS2_Verify_State)
               (ls_d: UCOS2_Verify_State)
               (e_r: OSEventAbstractState)
               (cpu_sr_v: Z)
               (pcp_v: Z) (prio_v: Z)
               (cnt_r: Z) (ptr_r: addr) (grp_r: Z)
               (tbl_r: list Z),
        safeExec(LastSeen(ls0),
                 bind(OSMutexPost_atomic_cmd(sg, ls0, pevent0),
                      observe_os_err_code), X) &&
        coq_prop(UCOS2_state_inv(sg, ls0)) &&
        coq_prop(mutex_post_owner_disinherit_stage_prop(
          sg, pevent0, ls0, pcp_idx,
          decode_OwnerPrio_from_cnt(ecnt_in), ls_d)) &&
        coq_prop(mutex_post_reservation_stage_prop(
          sg, eid, ls_d, ls_reserved)) &&
        coq_prop(mutex_post_empty_count_commit_step_prop(
          eid, ls_reserved, ls_available)) &&
        coq_prop(mutex_post_empty_owner_commit_step_prop(
          eid, ls_available, ls_r)) &&
        coq_prop(mutex_post_release_step_prop(sg, eid, ls_d, ls_r)) &&
        coq_prop(crit_rel_task_event_sched(ls0, ls_r)) &&
        coq_prop(valid_stable_glob_vars(sg)) &&
        coq_prop(event_raw_snapshot_of_prop(
          sg, ls_r.TskState, ls_r.EventState, eid, e_r,
          4, cnt_r, ptr_r, grp_r, tbl_r)) &&
        coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &pevent->OSEventType,
          &pevent->OSEventPtr,
          &pevent->OSEventCnt)) &&
        coq_prop(event_wait_fields_layout_prop(
          sg, eid,
          &pevent->OSEventGrp,
          &pevent->OSEventTbl)) &&
        coq_prop(valid_event_id(sg, eid)) &&
        InsideCritical(sg, ls0) &&
        mutex_post_rep(sg, ls0, ls_r) *
        data_at(&cpu_sr, unsigned int, cpu_sr_v) *
        data_at(&pcp, unsigned char, pcp_v) *
        data_at(&prio, unsigned char, prio_v) &&
        pevent == pevent0 &&
        pevent == event_addr(sg, eid) &&
        pcp_v == pcp_idx
    */
    OS_EXIT_CRITICAL()/*@ where sg = sg, eid = eid */;
    return (OS_ERR_NONE);
}
