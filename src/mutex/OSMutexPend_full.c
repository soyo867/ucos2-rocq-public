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
/*@ Extern Coq (tcb_addr : StableGlobVars -> TaskID -> addr) */
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
/*@ Extern Coq (mfPCP           : MutexFields -> Priority) */
/*@ Extern Coq (mfOwner         : MutexFields -> option TaskID) */
/*@ Extern Coq (mfOwnerOrigPrio : MutexFields -> option Priority) */

/*@ Extern Coq (OS_ERR_NONE           : OSErrCode) */
/*@ Extern Coq (OS_ERR_PEVENT_NULL    : OSErrCode) */
/*@ Extern Coq (OS_ERR_PDATA_NULL     : OSErrCode) */
/*@ Extern Coq (OS_ERR_EVENT_TYPE     : OSErrCode) */
/*@ Extern Coq (OS_ERR_QUERY_ISR      : OSErrCode) */
/*@ Extern Coq (OS_ERR_PEND_ISR       : OSErrCode) */
/*@ Extern Coq (OS_ERR_PEND_LOCKED    : OSErrCode) */
/*@ Extern Coq (OS_ERR_PEND_ABORT     : OSErrCode) */
/*@ Extern Coq (OS_ERR_TIMEOUT        : OSErrCode) */
/*@ Extern Coq (OS_ERR_PCP_LOWER      : OSErrCode) */
/*@ Extern Coq (encode_os_err_code    : OSErrCode -> Z) */
/*@ Extern Coq (OS_TRUE  : Z) */
/*@ Extern Coq (OS_FALSE : Z) */
/*@ Extern Coq (store_osrdytbl : StableGlobVars -> list Z -> Assertion) */
/*@ Extern Coq (store_osrdytbl_missing_i : StableGlobVars -> list Z -> Z -> Assertion) */
/*@ Extern Coq (store_oseventtbl : StableGlobVars -> addr -> list Z -> Assertion) */
/*@ Extern Coq (store_oseventtbl_missing_i : StableGlobVars -> addr -> list Z -> Z -> Assertion) */
/*@ Extern Coq (store_priotbl_list : StableGlobVars -> list addr -> Assertion) */
/*@ Extern Coq (store_priotbl_list_missing_i : StableGlobVars -> list addr -> Z -> Assertion) */
/*@ Extern Coq (osrdytbl_list_rel : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> list Z -> Prop) */
/*@ Extern Coq (prio_tbl_list_rel : StableGlobVars -> Glob_TaskAbstractState -> list addr -> Prop) */
/*@ Extern Coq (event_tbl_addr_list_rel : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> addr -> list Z -> Prop) */
/*@ Extern Coq (event_snapshot_of_prop : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> EventID -> OSEventAbstractState -> Z -> Z -> addr -> Z -> list Z -> Prop) */
/*@ Extern Coq (task_prio_snapshot_of_prop : StableGlobVars -> Glob_TaskAbstractState -> TaskID -> TaskAbstractState -> addr -> Z -> Prop) */
/*@ Extern Coq (task_mutex_full_snapshot_of_prop : StableGlobVars -> Glob_TaskAbstractState -> TaskID -> TaskAbstractState -> addr -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (task_rdy_snapshot_of_prop : StableGlobVars -> Glob_TaskAbstractState -> TaskID -> TaskAbstractState -> addr -> Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (task_inherit_snapshot_of_prop : StableGlobVars -> Glob_TaskAbstractState -> TaskID -> TaskAbstractState -> addr -> Z -> Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (task_mutex_pend_entry_prop : TaskAbstractState -> Prop) */
/*@ Extern Coq (task_mutex_pend_clean_prop : TaskAbstractState -> Prop) */
/*@ Extern Coq (used_task_pend_rest : StableGlobVars -> addr -> TaskID -> TaskAbstractState -> Assertion) */
/*@ Extern Coq (used_task_inherit_rest : StableGlobVars -> addr -> TaskID -> TaskAbstractState -> Assertion) */
/*@ Extern Coq (used_task_cleanup_rest : StableGlobVars -> addr -> TaskID -> TaskAbstractState -> Assertion) */
/*@ Extern Coq (task_inv_no_tid_priotbl : StableGlobVars -> Glob_TaskAbstractState -> TaskID -> Assertion) */
/*@ Extern Coq (task_inv_no_two_tids_priotbl : StableGlobVars -> Glob_TaskAbstractState -> TaskID -> TaskID -> Assertion) */
/*@ Extern Coq (sched_tcb_cur_snapshot_prop : StableGlobVars -> SchedAbstractState -> addr -> Prop) */
/*@ Extern Coq (sched_ready_prio_snapshot_prop : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> Z -> list Z -> Z -> Prop) */
/*@ Extern Coq (sched_inv_rest_ready_current : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> Assertion) */
/*@ Extern Coq (mutex_acquire_event_prop : OSEventAbstractState -> OSEventAbstractState -> TaskID -> Priority -> Prop) */
/*@ Extern Coq (mutex_owned_by_prop : OSEventAbstractState -> TaskID -> Priority -> Prop) */
/*@ Extern Coq (mutex_event_payload_unchanged_prop : OSEventAbstractState -> OSEventAbstractState -> Prop) */
/*@ Extern Coq (mutex_waiter_absent_prop : OSEventAbstractState -> TaskID -> Prop) */
/*@ Extern Coq (mutex_pend_owner_ready_prop : OSEventAbstractState -> Glob_TaskAbstractState -> TaskID -> TaskID -> TaskAbstractState -> Prop) */
/*@ Extern Coq (mutex_pend_owner_waiting_prop : OSEventAbstractState -> EventID -> Glob_TaskAbstractState -> SchedAbstractState -> Glob_EventAbstractState -> TaskID -> TaskID -> TaskAbstractState -> EventID -> OSEventAbstractState -> Prop) */
/*@ Extern Coq (mutex_pend_owner_dormant_prop : OSEventAbstractState -> Glob_TaskAbstractState -> SchedAbstractState -> TaskID -> TaskID -> TaskAbstractState -> Prop) */
/*@ Extern Coq (event_wait_snapshot_of_prop : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> EventID -> OSEventAbstractState -> addr -> Z -> list Z -> Prop) */
/*@ Extern Coq (verification_slice_event_type_ptr_cnt_rep : StableGlobVars -> addr -> OSEventAbstractState -> Assertion) */
/*@ Extern Coq (event_inv_no_two_eids : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> EventID -> EventID -> Assertion) */
/*@ Extern Coq (decode_PCP_from_cnt : Z -> Z) */
/*@ Extern Coq (decode_OwnerPrio_from_cnt : Z -> Z) */

/*@ Extern Coq (coq_prop : Prop -> Assertion) */
/*@ Extern Coq (valid_stable_glob_vars : StableGlobVars -> Prop) */
/*@ Extern Coq (valid_event_id : StableGlobVars -> EventID -> Prop) */
/*@ Extern Coq (pend_ecnt_out_prop : Z -> Z -> Z -> Prop) */
/*@ Extern Coq (store_used_event_map_missing_i : StableGlobVars -> (EventID -> option OSEventAbstractState) -> EventID -> Assertion) */
/*@ Extern Coq (used_complete_event : StableGlobVars -> addr -> EventID -> OSEventAbstractState -> Assertion) */
/*@ Extern Coq (unused_complete_event : StableGlobVars -> addr -> EventID -> Assertion) */
/*@ Extern Coq (store_free_event_list : StableGlobVars -> list EventID -> Assertion) */
/*@ Extern Coq (store_int_state : StableGlobVars -> Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (interrupt_inv : StableGlobVars -> Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (interrupt_inv_no_nesting_cells : Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (task_inv : StableGlobVars -> Glob_TaskAbstractState -> Assertion) */
/*@ Extern Coq (sched_inv : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> Assertion) */
/*@ Extern Coq (event_inv : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> Assertion) */
/*@ Extern Coq (used_event_wait_table_storage : Glob_TaskAbstractState -> addr -> OSEventAbstractState -> Assertion) */
/*@ Extern Coq (tick_inv : StableGlobVars -> TickAbstractState -> Assertion) */
/*@ Extern Coq (cross_module_consistency : StableGlobVars -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (event_inv_missing_usedevent : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> EventID -> OSEventAbstractState -> Assertion) */
/*@ Extern Coq (event_vaild_cond_prop : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> Prop) */
/*@ Extern Coq (interrupt_in_range : Glob_InterruptAbstractState -> Prop) */
/*@ Extern Coq (interrupt_inv : StableGlobVars -> Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (event_inv_no_eid : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> EventID -> Assertion) */
/*@ Extern Coq (UCOS2_Verify_inv : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (mutex_pend_sched_pre : StableGlobVars -> EventID -> TaskID -> addr -> TaskAbstractState -> UCOS2_Verify_State -> UCOS2_Verify_State -> UCOS2_Verify_State -> Z -> Z -> Z -> Z -> list Z -> Z -> list Z -> Assertion) */
/*@ Extern Coq (mutex_pend_cleanup_rest : StableGlobVars -> UCOS2_Verify_State -> TaskID -> TaskAbstractState -> Assertion) */
/*@ Extern Coq (mutex_pend_cleanup_nonintr_rest : StableGlobVars -> UCOS2_Verify_State -> TaskID -> TaskAbstractState -> Assertion) */
/*@ Extern Coq (UCOS2_Verify_inv_missing_usedevent : StableGlobVars -> UCOS2_Verify_State -> EventID -> OSEventAbstractState -> Assertion) */
/*@ Extern Coq (OSMutexPend_sem : StableGlobVars -> addr -> Z -> program UCOS2_Verify_State OSErrCode) */
/*@ Extern Coq (atomic_cmd : {A} -> program UCOS2_Verify_State A -> program (UCOS2_Verify_State -> Prop) A) */
/*@ Extern Coq (observe_os_err_code : OSErrCode -> program (UCOS2_Verify_State -> Prop) Z) */
/*@ Extern Coq (atomic_event_task_wait_mutex : StableGlobVars -> EventID -> Z -> UCOS2_Verify_State -> unit -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (atomic_mutex_inherit : StableGlobVars -> EventID -> UCOS2_Verify_State -> unit -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (atomic_task_pend_cleanup : TaskID -> UCOS2_Verify_State -> unit -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (atomic_event_task_remove : TaskID -> EventID -> UCOS2_Verify_State -> unit -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (atomic_event_task_remove_happens : TaskID -> EventID -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (MutexPendResumeResult :: *) */
/*@ Extern Coq (MutexPendResumeOK : MutexPendResumeResult) */
/*@ Extern Coq (MutexPendResumeAbort : MutexPendResumeResult) */
/*@ Extern Coq (MutexPendResumeTimeout : MutexPendResumeResult) */
/*@ Extern Coq (encode_mutex_pend_resume_stat : MutexPendResumeResult -> Z) */
/*@ Extern Coq (encode_mutex_pend_resume_statpend : MutexPendResumeResult -> Z) */
/*@ Extern Coq (encode_mutex_pend_resume_event_ptr : MutexPendResumeResult -> addr -> Z) */
/*@ Extern Coq (atomic_mutex_pend_sched_resume : StableGlobVars -> EventID -> TaskID -> UCOS2_Verify_State -> MutexPendResumeResult -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (os_int_nesting_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_lock_nesting_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_tcb_cur_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_rdy_grp_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_rdy_tbl_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_prio_cur_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_tcb_prio_tbl_addr : StableGlobVars -> addr -> Prop) */

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

/*@ Import Coq Local Open Scope Z_scope */
/*@ Import Coq Local Open Scope sac */

/*@ Import Coq From MonadLib Require Import Monad */
/*@ Import Coq From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib */
/*@ Import Coq Import Monad MonadNotation */
/*@ Import Coq Local Open Scope monad_scope */
/*@ Import Coq Require Import Ucos2Verify.lib.stable_glob_vars */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_verify_state_def */
/*@ Import Coq Require Import Ucos2Verify.lib.interrupt */
/*@ Import Coq Require Import Ucos2Verify.lib.task */
/*@ Import Coq Require Import Ucos2Verify.lib.sched */
/*@ Import Coq Require Import Ucos2Verify.lib.event */
/*@ Import Coq Require Import Ucos2Verify.lib.mutex */
/*@ Import Coq Require Import Ucos2Verify.lib.event_wait */
/*@ Import Coq Require Import Ucos2Verify.lib.error_codes */
/*@ Import Coq Require Import Ucos2Verify.lib.atomic_ops_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_rules_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_verify_inv */
/*@ Import Coq Require Import Ucos2Verify.lib.mutex_func_sem */
/*@ Import Coq Require Import Ucos2Verify.lib.array_abstraction */
/*@ Import Coq Require Import Ucos2Verify.lib.tick */
/*@ Import Coq Require Import Ucos2Verify.lib.cross_module_invariants */

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
#define  OS_ERR_PEND_ISR                2u
#define  OS_ERR_PEVENT_NULL             4u
#define  OS_ERR_TIMEOUT                 10u
#define  OS_ERR_PEND_LOCKED             13u
#define  OS_ERR_PEND_ABORT              14u
#define  OS_MUTEX_KEEP_LOWER_8          0x00FFu
#define  OS_MUTEX_KEEP_UPPER_8          0xFF00u
#define  OS_MUTEX_AVAILABLE             0x00FFu
#define  OS_PRIO_MUTEX_CEIL_DIS         0xFFu
#define  OS_ERR_PCP_LOWER               120u
#define  OS_STAT_MUTEX                  0x10u
#define  OS_STAT_RDY                    0x00u
#define  OS_STAT_PEND_OK                0u
#define  OS_STAT_PEND_TO                1u
#define  OS_STAT_PEND_ABORT             2u
#define  OS_EVENT_MULTI_EN              0u
#define  OS_TRACE_MUTEX_PEND_ENTER(pevent, timeout)
#define  OS_TRACE_MUTEX_PEND_EXIT(err)
#define  OS_TRACE_MUTEX_TASK_PRIO_INHERIT(ptcb, pcp)

typedef unsigned int OS_CPU_SR;
#define  OS_ENTER_CRITICAL()             cpu_sr = OS_CPU_SR_Save()
#define  OS_EXIT_CRITICAL()              OS_CPU_SR_Restore(cpu_sr)

/* ============================================================ */
/* OS_CPU_SR_Save: atomic entry into critical section.          */
/* OutsideCritical -> InsideCritical via RTrans_C.              */
/* ============================================================ */
unsigned int OS_CPU_SR_Save()
/*@ With (sg: StableGlobVars) (ls_in: UCOS2_Verify_State) (ls_out: UCOS2_Verify_State)
    Require OutsideCritical(sg, ls_in) &&
            interrupt_inv(sg, ls_in.IntrState)
    Ensure  RTrans_C(sg, ls_in, sg, ls_out) &&
            InsideCritical(sg, ls_out) &&
            interrupt_inv(sg, ls_out.IntrState) &&
            coq_prop(crit_rel_no_os_state_change(ls_in, ls_out)) &&
            __return == __return
*/
;

/* ============================================================ */
/* OS_CPU_SR_Restore: atomic exit from critical section.        */
/* InsideCritical -> OutsideCritical via GTrans_C.              */
/* ============================================================ */
void OS_CPU_SR_Restore(unsigned int cpu_sr)
/*@ With (sg: StableGlobVars) (ls_in: UCOS2_Verify_State) (ls_out: UCOS2_Verify_State)
    Require InsideCritical(sg, ls_in) &&
            interrupt_inv(sg, ls_in.IntrState)
    Ensure  GTrans_C(sg, ls_in, sg, ls_out) &&
            OutsideCritical(sg, ls_out) &&
            interrupt_inv(sg, ls_out.IntrState) &&
            coq_prop(crit_rel_task_event_sched(ls_in, ls_out))
*/
;

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

extern  INT8U    OSIntNesting;
extern  INT8U    OSLockNesting;
extern  OS_TCB  *OSTCBCur;
extern  OS_PRIO  OSRdyGrp;
extern  OS_PRIO  OSRdyTbl[8];
extern  INT8U    OSPrioCur;
extern  OS_TCB  *OSTCBPrioTbl[64];

void OS_EventTaskWait(OS_EVENT *pevent)
/*@ With (sg: StableGlobVars)
           (ls_entry: UCOS2_Verify_State)
           (ls_in: UCOS2_Verify_State) (ls_out: UCOS2_Verify_State)
           (eid: EventID) (cur_tid: TaskID) (tcbcur: addr)
           (cur_t: TaskAbstractState)
           (timeout: Z) (event_ptr_in: Z)
           (pcp_in: Z) (owner_prio_in: Z)
           (mprio_in: Z) (cur_prio_in: Z)
           (event_grp_pre: Z) (event_tbl_pre: list Z)
           (rdy_grp_pre: Z) (rdy_tbl_pre: list Z)
    Require InsideCritical(sg, ls_entry) &&
             interrupt_inv(sg, ls_entry.IntrState) &&
             (((pcp_in != 255 && owner_prio_in > pcp_in &&
                mprio_in > cur_prio_in) &&
               atomic_mutex_inherit(sg, eid, ls_entry, tt, ls_in)) ||
              ((pcp_in == 255 || owner_prio_in <= pcp_in ||
                mprio_in <= cur_prio_in) && ls_in == ls_entry)) &&
             pevent == event_addr(sg, eid) &&
             tcbcur == tcb_addr(sg, cur_tid) &&
             data_at(&((OS_TCB *)tcbcur)->OSTCBStat, 16) &&
             data_at(&((OS_TCB *)tcbcur)->OSTCBStatPend, 0) &&
             data_at(&((OS_TCB *)tcbcur)->OSTCBDly, timeout) &&
             data_at(&((OS_TCB *)tcbcur)->OSTCBEventPtr, event_ptr_in) &&
             used_task_pend_rest(sg, tcbcur, cur_tid, cur_t) &&
             data_at(&pevent->OSEventGrp, event_grp_pre) &&
             store_oseventtbl(sg, pevent, event_tbl_pre) &&
             data_at(&OSRdyGrp, rdy_grp_pre) &&
             store_osrdytbl(sg, rdy_tbl_pre)
    Ensure  exists (event_grp_post: Z) (event_tbl_post: list Z)
                   (rdy_grp_post: Z) (rdy_tbl_post: list Z),
             atomic_event_task_wait_mutex(sg, eid, timeout, ls_in, tt, ls_out) &&
             InsideCritical(sg, ls_out) &&
             interrupt_inv(sg, ls_out.IntrState) &&
             pevent == event_addr(sg, eid) &&
             tcbcur == tcb_addr(sg, cur_tid) &&
             data_at(&((OS_TCB *)tcbcur)->OSTCBStat, 16) &&
             data_at(&((OS_TCB *)tcbcur)->OSTCBStatPend, 0) &&
             data_at(&((OS_TCB *)tcbcur)->OSTCBDly, timeout) &&
             data_at(&((OS_TCB *)tcbcur)->OSTCBEventPtr, pevent) &&
             used_task_pend_rest(sg, tcbcur, cur_tid, cur_t) &&
             data_at(&pevent->OSEventGrp, event_grp_post) &&
             store_oseventtbl(sg, pevent, event_tbl_post) &&
             data_at(&OSRdyGrp, rdy_grp_post) &&
             store_osrdytbl(sg, rdy_tbl_post)
*/
;

void OS_EventTaskRemove(OS_TCB *ptcb, OS_EVENT *pevent)
/*@ With (sg: StableGlobVars) (ls_in: UCOS2_Verify_State) (ls_rm: UCOS2_Verify_State)
          (eid: EventID) (tid: TaskID) (pt: addr)
          (cur_t_pre: TaskAbstractState)
          (stat_pre: Z) (statpend_pre: Z) (dly_pre: Z)
    Require InsideCritical(sg, ls_in) &&
             mutex_pend_cleanup_rest(sg, ls_in, tid, cur_t_pre) &&
             pevent == event_addr(sg, eid) &&
             ptcb == pt &&
             pt == tcb_addr(sg, tid) &&
             data_at(&OSTCBCur, pt) &&
             data_at(&((OS_TCB *)pt)->OSTCBStat, stat_pre) &&
             data_at(&((OS_TCB *)pt)->OSTCBStatPend, statpend_pre) &&
             data_at(&((OS_TCB *)pt)->OSTCBDly, dly_pre) &&
             data_at(&((OS_TCB *)pt)->OSTCBEventPtr, pevent)
    Ensure  exists (cur_t_post: TaskAbstractState),
             atomic_event_task_remove(tid, eid, ls_in, tt, ls_rm) &&
             atomic_event_task_remove_happens(tid, eid, ls_in) &&
             InsideCritical(sg, ls_rm) &&
             mutex_pend_cleanup_rest(sg, ls_rm, tid, cur_t_post) &&
             pevent == event_addr(sg, eid) &&
             ptcb == pt &&
             pt == tcb_addr(sg, tid) &&
             data_at(&OSTCBCur, pt) &&
             data_at(&((OS_TCB *)pt)->OSTCBStat, stat_pre) &&
             data_at(&((OS_TCB *)pt)->OSTCBStatPend, statpend_pre) &&
             data_at(&((OS_TCB *)pt)->OSTCBDly, dly_pre) &&
             data_at(&((OS_TCB *)pt)->OSTCBEventPtr, 0)
*/
;

void OS_Sched()
/*@ With (sg: StableGlobVars) (eid: EventID) (cur_tid: TaskID)
          (tcbcur: addr)
          (cur_t_pre: TaskAbstractState)
          (ls_wait: UCOS2_Verify_State)
          (ls_frame: UCOS2_Verify_State)
          (timeout: Z)
          (ls_in: UCOS2_Verify_State) (ls_out: UCOS2_Verify_State)
          (cur_prio_in: Z) (prio_cur_pre: Z)
          (event_grp_pre: Z) (event_tbl_pre: list Z)
          (rdy_grp_pre: Z) (rdy_tbl_pre: list Z)
    Require mutex_pend_sched_pre(
              sg, eid, cur_tid, tcbcur, cur_t_pre,
              ls_wait, ls_frame, ls_in, timeout, cur_prio_in,
              prio_cur_pre, event_grp_pre, event_tbl_pre,
              rdy_grp_pre, rdy_tbl_pre)
    Ensure  exists (res: MutexPendResumeResult)
                   (cur_t_post: TaskAbstractState)
                   (event_grp_post: Z) (event_tbl_post: list Z)
                   (rdy_grp_post: Z) (rdy_tbl_post: list Z)
                   (prio_cur_post: Z),
            atomic_mutex_pend_sched_resume(
              sg, eid, cur_tid, ls_wait, res, ls_out) &&
            OutsideCritical(sg, ls_out) &&
            interrupt_inv(sg, ls_out.IntrState) &&
            tcbcur == tcb_addr(sg, cur_tid) &&
            coq_prop(task_prio_snapshot_of_prop(
              sg, ls_out.TskState, cur_tid, cur_t_post,
              tcbcur, cur_prio_in)) &&
            data_at(&OSTCBCur, tcbcur) &&
            data_at(&((OS_TCB *)tcbcur)->OSTCBPrio, cur_prio_in) &&
            data_at(&((OS_TCB *)tcbcur)->OSTCBDly, 0) &&
            data_at(&((OS_TCB *)tcbcur)->OSTCBStat, encode_mutex_pend_resume_stat(res)) &&
            data_at(&((OS_TCB *)tcbcur)->OSTCBStatPend, encode_mutex_pend_resume_statpend(res)) &&
            data_at(&((OS_TCB *)tcbcur)->OSTCBEventPtr,
                    encode_mutex_pend_resume_event_ptr(res, event_addr(sg, eid))) &&
            used_task_pend_rest(sg, tcbcur, cur_tid, cur_t_post) &&
            data_at(&OSRdyGrp, rdy_grp_post) &&
            store_osrdytbl(sg, rdy_tbl_post) &&
            data_at(&OSPrioCur, prio_cur_post) &&
            sched_inv_rest_ready_current(
              sg, ls_out.TskState, ls_out.SchedState) &&
            coq_prop(sched_ready_prio_snapshot_prop(
              sg, ls_out.TskState, ls_out.SchedState,
              rdy_grp_post, rdy_tbl_post, prio_cur_post)) &&
            data_at(&((OS_EVENT *)event_addr(sg, eid))->OSEventGrp,
                    event_grp_post) &&
            store_oseventtbl(
              sg, event_addr(sg, eid), event_tbl_post)
*/
;

/* ============================================================ */
/* OSMutexPend_full: line-by-line faithful to os_mutex.c:467-660*/
/*                                                              */
/* Spec pattern follows los_verify OsMuxPend:                    */
/*   PRE: direct global cells + safeExec + OutsideCritical       */
/*   POST: compact encoded error + direct global cells + safeExec*/
/*   Body: which implies for inv <-> concrete cell decomposition */
/* ============================================================ */
void  OSMutexPend_full (OS_EVENT *pevent, INT32U timeout, INT8U *perr)
/*@ With (sg: StableGlobVars) (ls0: UCOS2_Verify_State) X
           (ls1: UCOS2_Verify_State) (ls2: UCOS2_Verify_State)
           (ls3: UCOS2_Verify_State) (ls4: UCOS2_Verify_State)
           (ls5: UCOS2_Verify_State) (ls_wait: UCOS2_Verify_State)
           (ls_inherit: UCOS2_Verify_State)
           (ls_rm: UCOS2_Verify_State)
           (ls_ret: UCOS2_Verify_State)
           (eid: EventID) (e: OSEventAbstractState)
           (cur_t: TaskAbstractState) (owner_t: TaskAbstractState)
           (owner_tid: TaskID)
           (owner_wait_eid: EventID) (owner_wait_e: OSEventAbstractState)
           (pe: addr) (pd: addr)
           (etype: Z) (ecnt_in: Z) (eptr_in: Z)
           (event_grp_in: Z) (event_tbl_in: list Z)
           (tcbcur: Z) (tcbprio: Z) (cur_tid: TaskID)
           (owner_prio: Z) (owner_y: Z) (owner_x: Z)
           (owner_bity: Z) (owner_bitx: Z) (owner_event_ptr: Z)
           (owner_wait_grp: Z) (owner_wait_tbl_y: Z)
           (owner_new_y: Z) (rdy_tbl_new_y: Z) (owner_wait_tbl_new_y: Z)
           (pcp_idx: Z) (prio_tbl_pcp: Z)
           (rdyL_in: list Z) (prioL_in: list addr) (evtL_in: list Z)
           (event_grp_sched: Z) (event_tbl_sched: list Z)
           (rdy_grp_sched: Z) (rdy_tbl_sched: list Z)
           (resume_t: TaskAbstractState)
           (resume_stat: Z) (resume_statpend: Z) (resume_eventptr: Z)
           (cleanup_t: TaskAbstractState)
           (cleanup_stat: Z) (cleanup_statpend: Z)
           (cleanup_eventptr: Z) (cleanup_err: Z)
           (cur_stat: Z) (cur_statpend: Z) (cur_dly: Z) (cur_event_ptr: Z)
           (cur_event_multi_ptr: Z) (cur_event_multi_rdy: Z)
           (rdy_grp: Z) (rdy_tbl_owner_y: Z)
           (prio_cur_in: Z) (isr: Z) (lock: Z) (perr_in: Z)
    Require
        data_at(perr, unsigned char, perr_in) &&
        isr == intNesting(ls0.IntrState) &&
        lock == lockNesting(ls0.IntrState) &&
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
        coq_prop(os_lock_nesting_addr(sg, &OSLockNesting)) &&
        coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) &&
        coq_prop(os_rdy_grp_addr(sg, &OSRdyGrp)) &&
        coq_prop(os_rdy_tbl_addr(sg, OSRdyTbl)) &&
        coq_prop(os_prio_cur_addr(sg, &OSPrioCur)) &&
        coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
        coq_prop(sched_ready_prio_snapshot_prop(
          sg, ls0.TskState, ls0.SchedState,
          rdy_grp, rdyL_in, prio_cur_in)) &&
        coq_prop(prio_tbl_list_rel(sg, ls0.TskState, prioL_in)) &&
        pcp_idx == decode_PCP_from_cnt(ecnt_in) &&
        Znth(pcp_idx, prioL_in, 0) == prio_tbl_pcp &&
        safeExec(LastSeen(ls0),
                 bind(atomic_cmd(OSMutexPend_sem(sg, pevent, timeout)),
                      observe_os_err_code), X) &&
        OutsideCritical(sg, ls0) &&
        UCOS2_Verify_inv(sg, ls0) &&
        coq_prop(valid_stable_glob_vars(sg)) &&
        perr != 0 &&
        pd == perr &&
        pe == pevent &&
        (
          pevent == 0 ||
          (pevent != 0 &&
           pevent == event_addr(sg, eid) &&
           coq_prop(valid_event_id(sg, eid)) &&
           0 <= etype && etype <= 255 &&
           coq_prop(event_snapshot_of_prop(
             sg, ls0.TskState, ls0.EventState, eid, e, etype,
             ecnt_in, eptr_in, event_grp_in, event_tbl_in)) &&
           (etype != 4 || isr > 0 || lock > 0 ||
            (etype == 4 && isr <= 0 && lock <= 0 &&
             tcbcur != 0 &&
             coq_prop(sched_tcb_cur_snapshot_prop(
               sg, ls0.SchedState, tcbcur)) &&
             coq_prop(task_mutex_full_snapshot_of_prop(
               sg, ls0.TskState, cur_tid, cur_t, tcbcur, tcbprio,
               cur_stat, cur_statpend, cur_dly, cur_event_ptr,
               cur_event_multi_ptr, cur_event_multi_rdy)) &&
             coq_prop(task_mutex_pend_entry_prop(cur_t)) &&
             ((decode_OwnerPrio_from_cnt(ecnt_in) == 255 && eptr_in == 0) ||
              (decode_OwnerPrio_from_cnt(ecnt_in) != 255 &&
               eptr_in != 0 &&
               coq_prop(task_inherit_snapshot_of_prop(
                 sg, ls0.TskState, owner_tid, owner_t, eptr_in,
                 owner_prio, owner_x, owner_y, owner_bitx, owner_bity,
                 owner_event_ptr)) &&
               owner_new_y == ((decode_PCP_from_cnt(ecnt_in) >> 3) & 7) &&
               ((owner_event_ptr == 0 &&
                 (coq_prop(mutex_pend_owner_ready_prop(
                    e, ls0.TskState, cur_tid, owner_tid, owner_t)) ||
                  coq_prop(mutex_pend_owner_dormant_prop(
                    e, ls0.TskState, ls0.SchedState,
                    cur_tid, owner_tid, owner_t))) &&
                 Znth(owner_y, rdyL_in, 0) == rdy_tbl_owner_y &&
                 Znth(owner_new_y, rdyL_in, 0) == rdy_tbl_new_y) ||
                (owner_event_ptr != 0 && owner_event_ptr != pevent &&
                 coq_prop(valid_event_id(sg, owner_wait_eid)) &&
                 coq_prop(mutex_pend_owner_waiting_prop(
                   e, eid, ls0.TskState, ls0.SchedState, ls0.EventState,
                   cur_tid, owner_tid, owner_t,
                   owner_wait_eid, owner_wait_e)) &&
                 coq_prop(event_wait_snapshot_of_prop(
                   sg, ls0.TskState, ls0.EventState,
                   owner_wait_eid, owner_wait_e, owner_event_ptr,
                   owner_wait_grp, evtL_in)) &&
                 Znth(owner_y, evtL_in, 0) == owner_wait_tbl_y &&
                 Znth(owner_new_y, evtL_in, 0) ==
                   owner_wait_tbl_new_y))))))))
    Ensure
        exists (ls_post : UCOS2_Verify_State) (err_code : Z),
           safeExec(LastSeen(ls_post), return(err_code), X) &&
           OutsideCritical(sg, ls_post) &&
           UCOS2_Verify_inv(sg, ls_post) &&
            (
              (err_code == 4 &&
               pevent == 0 &&
               data_at(perr, unsigned char, 4)) ||
              (err_code == 1 &&
               pevent != 0 &&
               etype != 4 &&
               coq_prop(event_snapshot_of_prop(
                 sg, ls_post.TskState, ls_post.EventState, eid, e, etype,
                 ecnt_in, eptr_in, event_grp_in, event_tbl_in)) &&
               data_at(perr, unsigned char, 1)) ||
              (err_code == 2 &&
               pevent != 0 &&
               etype == 4 &&
               isr > 0 &&
               coq_prop(event_snapshot_of_prop(
                 sg, ls_post.TskState, ls_post.EventState, eid, e, 4,
                 ecnt_in, eptr_in, event_grp_in, event_tbl_in)) &&
               data_at(perr, unsigned char, 2)) ||
              (err_code == 13 &&
               pevent != 0 &&
               etype == 4 &&
               isr <= 0 &&
               lock > 0 &&
               coq_prop(event_snapshot_of_prop(
                 sg, ls_post.TskState, ls_post.EventState, eid, e, 4,
                 ecnt_in, eptr_in, event_grp_in, event_tbl_in)) &&
               data_at(perr, unsigned char, 13)) ||
              (exists (e_post: OSEventAbstractState)
                      (event_tbl_post: list Z),
               pevent != 0 && etype == 4 && isr <= 0 && lock <= 0 &&
               decode_OwnerPrio_from_cnt(ecnt_in) == 255 &&
               coq_prop(mutex_acquire_event_prop(
                 e, e_post, cur_tid, tcbprio)) &&
               coq_prop(event_snapshot_of_prop(
                 sg, ls_post.TskState, ls_post.EventState, eid, e_post, 4,
                 decode_PCP_from_cnt(ecnt_in) * 256 + tcbprio,
                 tcbcur, event_grp_in, event_tbl_post)) &&
               ((decode_PCP_from_cnt(ecnt_in) != 255 &&
                 tcbprio <= decode_PCP_from_cnt(ecnt_in) &&
                 err_code == 120 && data_at(perr, unsigned char, 120)) ||
                ((decode_PCP_from_cnt(ecnt_in) == 255 ||
                  tcbprio > decode_PCP_from_cnt(ecnt_in)) &&
                 err_code == 0 && data_at(perr, unsigned char, 0)))) ||
              (exists (e_post: OSEventAbstractState)
                      (cur_t_post: TaskAbstractState)
                      (ecnt_post: Z) (eptr_post: Z)
                      (event_grp_post: Z) (event_tbl_post: list Z),
               pevent != 0 && etype == 4 && isr <= 0 && lock <= 0 &&
               decode_OwnerPrio_from_cnt(ecnt_in) != 255 &&
               coq_prop(task_prio_snapshot_of_prop(
                 sg, ls_post.TskState, cur_tid, cur_t_post,
                 tcbcur, tcbprio)) &&
               coq_prop(task_mutex_pend_clean_prop(cur_t_post)) &&
               coq_prop(event_snapshot_of_prop(
                 sg, ls_post.TskState, ls_post.EventState, eid, e_post, 4,
                 ecnt_post, eptr_post, event_grp_post, event_tbl_post)) &&
               coq_prop(mutex_waiter_absent_prop(e_post, cur_tid)) &&
               ((err_code == 0 &&
                 eptr_post == tcbcur &&
                 decode_OwnerPrio_from_cnt(ecnt_post) == tcbprio &&
                 coq_prop(mutex_owned_by_prop(
                   e_post, cur_tid, tcbprio)) &&
                 data_at(perr, unsigned char, 0)) ||
                (err_code == 14 &&
                 coq_prop(mutex_event_payload_unchanged_prop(e, e_post)) &&
                 data_at(perr, unsigned char, 14)) ||
                (err_code == 10 &&
                 coq_prop(mutex_event_payload_unchanged_prop(e, e_post)) &&
                 data_at(perr, unsigned char, 10))))
            )
*/
{
    INT8U      pcp;
    INT8U      mprio;
    BOOLEAN    rdy;
    OS_TCB    *ptcb;
    OS_EVENT  *pevent2;
    INT8U      y;
    OS_CPU_SR  cpu_sr = 0u;

    if (pevent == (OS_EVENT *)0) {
        *perr = OS_ERR_PEVENT_NULL;
        return;
    }
    OS_TRACE_MUTEX_PEND_ENTER(pevent, timeout);
    /*@ exists (pevent_v: Z),
        pevent_v == pe &&
        data_at(&pevent, struct os_event *, pevent_v) *
        UCOS2_Verify_inv(sg, ls0)
        which implies
        data_at(&pevent, struct os_event *, pevent_v) *
        data_at(&((OS_EVENT *)pevent_v)->OSEventType, unsigned char, etype) *
        data_at(&((OS_EVENT *)pevent_v)->OSEventPtr, void *, eptr_in) *
        data_at(&((OS_EVENT *)pevent_v)->OSEventCnt, unsigned short, ecnt_in) *
        data_at(&((OS_EVENT *)pevent_v)->OSEventGrp, unsigned char, event_grp_in) *
        store_oseventtbl(sg, pevent_v, event_tbl_in) *
        interrupt_inv(sg, ls0.IntrState) *
        task_inv(sg, ls0.TskState) *
        sched_inv(sg, ls0.TskState, ls0.SchedState) *
        event_inv_no_eid(sg, ls0.TskState, ls0.EventState, eid) *
        tick_inv(sg, ls0.TickState) *
        coq_prop(cross_module_consistency(sg, ls0))
    */
    if (pevent->OSEventType != OS_EVENT_TYPE_MUTEX) {
        *perr = OS_ERR_EVENT_TYPE;
        OS_TRACE_MUTEX_PEND_EXIT(*perr);
        return;
    }
    /*@ interrupt_inv(sg, ls0.IntrState)
        which implies
        data_at(&OSIntNesting, unsigned char, isr) *
        data_at(&OSLockNesting, unsigned char, lock) *
        interrupt_inv_no_nesting_cells(ls0.IntrState)
    */
    if (OSIntNesting > 0u) {
        *perr = OS_ERR_PEND_ISR;
        OS_TRACE_MUTEX_PEND_EXIT(*perr);
        return;
    }
    if (OSLockNesting > 0u) {
        *perr = OS_ERR_PEND_LOCKED;
        OS_TRACE_MUTEX_PEND_EXIT(*perr);
        return;
    }

    /*@ data_at(&OSIntNesting, unsigned char, isr) *
        data_at(&OSLockNesting, unsigned char, lock) *
        interrupt_inv_no_nesting_cells(ls0.IntrState)
        which implies
        interrupt_inv(sg, ls0.IntrState)
    */
    OS_ENTER_CRITICAL()/*@ where sg = sg, ls_in = ls0, ls_out = ls1 */;
    /*@ task_inv(sg, ls0.TskState) *
        sched_inv(sg, ls0.TskState, ls0.SchedState)
        which implies
        data_at(&((OS_TCB *)tcbcur)->OSTCBPrio, unsigned char, tcbprio) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBStat, unsigned char, cur_stat) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBStatPend, unsigned char, cur_statpend) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBDly, unsigned int, cur_dly) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBEventPtr, void *, cur_event_ptr) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBEventMultiPtr, void **, cur_event_multi_ptr) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBEventMultiRdy, void *, cur_event_multi_rdy) *
        used_task_pend_rest(sg, tcbcur, cur_tid, cur_t) *
        task_inv_no_tid_priotbl(sg, ls0.TskState, cur_tid) *
        store_priotbl_list(sg, prioL_in) *
        data_at(&OSTCBCur, struct os_tcb *, tcbcur) *
        data_at(&OSRdyGrp, unsigned char, rdy_grp) *
        store_osrdytbl(sg, rdyL_in) *
        data_at(&OSPrioCur, unsigned char, prio_cur_in) *
        sched_inv_rest_ready_current(sg, ls0.TskState, ls0.SchedState)
    */
    pcp = (INT8U)(pevent->OSEventCnt >> 8u);

    if ((INT8U)(pevent->OSEventCnt & OS_MUTEX_KEEP_LOWER_8) == OS_MUTEX_AVAILABLE) {
        pevent->OSEventCnt &= OS_MUTEX_KEEP_UPPER_8;
        pevent->OSEventCnt |= (INT16U)OSTCBCur->OSTCBPrio;
        pevent->OSEventPtr  = (void *)OSTCBCur;
        if ((pcp != OS_PRIO_MUTEX_CEIL_DIS) &&
            (OSTCBCur->OSTCBPrio <= pcp)) {
            OS_EXIT_CRITICAL()/*@ where sg = sg, ls_in = ls1, ls_out = ls2 */;
            *perr = OS_ERR_PCP_LOWER;
        } else {
            OS_EXIT_CRITICAL()/*@ where sg = sg, ls_in = ls1, ls_out = ls2 */;
            *perr = OS_ERR_NONE;
        }
        OS_TRACE_MUTEX_PEND_EXIT(*perr);
        return;
    }
    /*@ data_at(&((OS_TCB *)tcbcur)->OSTCBPrio, unsigned char, tcbprio) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBStat, unsigned char, cur_stat) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBStatPend, unsigned char, cur_statpend) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBDly, unsigned int, cur_dly) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBEventPtr, void *, cur_event_ptr) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBEventMultiPtr, void **, cur_event_multi_ptr) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBEventMultiRdy, void *, cur_event_multi_rdy) *
        used_task_pend_rest(sg, tcbcur, cur_tid, cur_t) *
        task_inv_no_tid_priotbl(sg, ls0.TskState, cur_tid)
        which implies
        data_at(&((OS_TCB *)tcbcur)->OSTCBPrio, unsigned char, tcbprio) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBStat, unsigned char, cur_stat) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBStatPend, unsigned char, cur_statpend) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBDly, unsigned int, cur_dly) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBEventPtr, void *, cur_event_ptr) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBEventMultiPtr, void **, cur_event_multi_ptr) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBEventMultiRdy, void *, cur_event_multi_rdy) *
        used_task_pend_rest(sg, tcbcur, cur_tid, cur_t) *
        data_at(&((OS_TCB *)eptr_in)->OSTCBPrio, unsigned char, owner_prio) *
        data_at(&((OS_TCB *)eptr_in)->OSTCBX, unsigned char, owner_x) *
        data_at(&((OS_TCB *)eptr_in)->OSTCBY, unsigned char, owner_y) *
        data_at(&((OS_TCB *)eptr_in)->OSTCBBitX, unsigned char, owner_bitx) *
        data_at(&((OS_TCB *)eptr_in)->OSTCBBitY, unsigned char, owner_bity) *
        data_at(&((OS_TCB *)eptr_in)->OSTCBEventPtr, void *, owner_event_ptr) *
        used_task_inherit_rest(sg, eptr_in, owner_tid, owner_t) *
        task_inv_no_two_tids_priotbl(sg, ls0.TskState, cur_tid, owner_tid)
    */
    if (pcp != OS_PRIO_MUTEX_CEIL_DIS) {
        mprio = (INT8U)(pevent->OSEventCnt & OS_MUTEX_KEEP_LOWER_8);
        ptcb  = (OS_TCB *)(pevent->OSEventPtr);
        if (ptcb->OSTCBPrio > pcp) {
            if (mprio > OSTCBCur->OSTCBPrio) {
                /*@ 0 <= owner_y && owner_y < 8 && 0 <= owner_new_y && owner_new_y < 8 &&
                    store_osrdytbl(sg, rdyL_in)
                    which implies
                    data_at(&OSRdyTbl[owner_y], rdy_tbl_owner_y) *
                    store_osrdytbl_missing_i(sg, rdyL_in, owner_y)
                */
                y = ptcb->OSTCBY;
                if ((OSRdyTbl[y] & ptcb->OSTCBBitX) != 0u) {
                    OSRdyTbl[y] &= (OS_PRIO)~ptcb->OSTCBBitX;
                    if (OSRdyTbl[y] == 0u) {
                        OSRdyGrp &= (OS_PRIO)~ptcb->OSTCBBitY;
                    }
                    rdy = OS_TRUE;
                } else {
                    pevent2 = ptcb->OSTCBEventPtr;
                    if (pevent2 != (OS_EVENT *)0) {
                        /*@ data_at(&pevent->OSEventType, unsigned char, etype) *
                            data_at(&pevent->OSEventPtr, void *, eptr_in) *
                            data_at(&pevent->OSEventCnt, unsigned short, ecnt_in) *
                            data_at(&pevent->OSEventGrp, unsigned char, event_grp_in) *
                            store_oseventtbl(sg, pevent, event_tbl_in) *
                            event_inv_no_eid(
                              sg, ls0.TskState, ls0.EventState, eid)
                            which implies
                            data_at(&pevent->OSEventType, unsigned char, etype) *
                            data_at(&pevent->OSEventPtr, void *, eptr_in) *
                            data_at(&pevent->OSEventCnt, unsigned short, ecnt_in) *
                            data_at(&pevent->OSEventGrp, unsigned char, event_grp_in) *
                            store_oseventtbl(sg, pevent, event_tbl_in) *
                            verification_slice_event_type_ptr_cnt_rep(
                              sg, owner_event_ptr, owner_wait_e) *
                            data_at(&((OS_EVENT *)owner_event_ptr)->OSEventGrp,
                                    unsigned char, owner_wait_grp) *
                            store_oseventtbl(sg, owner_event_ptr, evtL_in) *
                            event_inv_no_two_eids(
                              sg, ls0.TskState, ls0.EventState,
                              eid, owner_wait_eid)
                        */
                        /*@ 0 <= owner_y && owner_y < 8 &&
                            store_oseventtbl(sg, owner_event_ptr, evtL_in)
                            which implies
                            data_at(&((OS_EVENT *)owner_event_ptr)->OSEventTbl[owner_y], owner_wait_tbl_y) *
                            store_oseventtbl_missing_i(sg, owner_event_ptr, evtL_in, owner_y)
                        */
                        y = ptcb->OSTCBY;
                        pevent2->OSEventTbl[y] &= (OS_PRIO)~ptcb->OSTCBBitX;
                        if (pevent2->OSEventTbl[y] == 0u) {
                            pevent2->OSEventGrp &= (OS_PRIO)~ptcb->OSTCBBitY;
                        }
                    }
                    rdy = OS_FALSE;
                }
                ptcb->OSTCBPrio = pcp;
                OS_TRACE_MUTEX_TASK_PRIO_INHERIT(ptcb, pcp);
                ptcb->OSTCBY    = (INT8U)(ptcb->OSTCBPrio >> 3u);
                ptcb->OSTCBX    = (INT8U)(ptcb->OSTCBPrio & 0x07u);
                ptcb->OSTCBBitY = (OS_PRIO)(1uL << ptcb->OSTCBY);
                ptcb->OSTCBBitX = (OS_PRIO)(1uL << ptcb->OSTCBX);
                /*@
                    exists (rdy_tbl_y_after: Z),
                    data_at(&ptcb->OSTCBY, owner_new_y) *
                    data_at(&OSRdyTbl[owner_y], rdy_tbl_y_after) *
                    store_osrdytbl_missing_i(sg, rdyL_in, owner_y)
                    which implies
                    data_at(&ptcb->OSTCBY, owner_new_y) *
                    data_at(&OSRdyTbl[owner_new_y], rdy_tbl_new_y) *
                    store_osrdytbl_missing_i(sg, replace_Znth(owner_y, rdy_tbl_y_after, rdyL_in), owner_new_y)
                */
                if (rdy == OS_TRUE) {
                    OSRdyGrp               |= ptcb->OSTCBBitY;
                    OSRdyTbl[ptcb->OSTCBY] |= ptcb->OSTCBBitX;
                } else {
                    pevent2 = ptcb->OSTCBEventPtr;
                    if (pevent2 != (OS_EVENT *)0) {
                        /*@
                            exists (evt_tbl_y_after: Z),
                            0 <= owner_new_y && owner_new_y < 8 &&
                            data_at(&ptcb->OSTCBY, owner_new_y) *
                            data_at(&((OS_EVENT *)owner_event_ptr)->OSEventTbl[owner_y], evt_tbl_y_after) *
                            store_oseventtbl_missing_i(sg, owner_event_ptr, evtL_in, owner_y)
                            which implies
                            data_at(&ptcb->OSTCBY, owner_new_y) *
                            data_at(&((OS_EVENT *)owner_event_ptr)->OSEventTbl[owner_new_y], owner_wait_tbl_new_y) *
                            store_oseventtbl_missing_i(sg, owner_event_ptr, replace_Znth(owner_y, evt_tbl_y_after, evtL_in), owner_new_y)
                        */
                        pevent2->OSEventGrp               |= ptcb->OSTCBBitY;
                        pevent2->OSEventTbl[ptcb->OSTCBY] |= ptcb->OSTCBBitX;
                    }
                }
                /*@ exists (rdy_cell: Z) (rdy_list_base: list Z),
                    data_at(&OSRdyTbl[owner_new_y], rdy_cell) *
                    store_osrdytbl_missing_i(sg, rdy_list_base, owner_new_y)
                    which implies
                    store_osrdytbl(
                      sg, replace_Znth(owner_new_y, rdy_cell, rdy_list_base))
                */
                /*@
                    0 <= pcp_idx && pcp_idx < 64 && pcp_idx == pcp &&
                    store_priotbl_list(sg, prioL_in)
                    which implies
                    data_at(&OSTCBPrioTbl[pcp], prio_tbl_pcp) *
                    store_priotbl_list_missing_i(sg, prioL_in, pcp_idx)
                */
                OSTCBPrioTbl[pcp] = ptcb;
            }
        }
    }
    OSTCBCur->OSTCBStat     |= OS_STAT_MUTEX;
    OSTCBCur->OSTCBStatPend  = OS_STAT_PEND_OK;
    OSTCBCur->OSTCBDly       = timeout;
    /*@
        data_at(&((OS_TCB *)tcbcur)->OSTCBStat, 16) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBStatPend, 0) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBDly, timeout)
        which implies
        data_at(&((OS_TCB *)tcbcur)->OSTCBStat, 16) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBStatPend, 0) *
        data_at(&((OS_TCB *)tcbcur)->OSTCBDly, timeout)
    */
    OS_EventTaskWait(pevent)/*@ where sg = sg, ls_entry = ls1,
        ls_in = ls_inherit, ls_out = ls_wait, eid = eid, cur_tid = cur_tid,
        tcbcur = tcbcur, cur_t = cur_t, timeout = timeout,
        event_ptr_in = cur_event_ptr,
        pcp_in = decode_PCP_from_cnt(ecnt_in),
        owner_prio_in = owner_prio,
        mprio_in = decode_OwnerPrio_from_cnt(ecnt_in),
        cur_prio_in = tcbprio */;
    OS_EXIT_CRITICAL()/*@ where sg = sg, ls_in = ls_wait, ls_out = ls2 */;
    /*@ Assert
        exists (pcp_v: Z) (mprio_v: Z) (rdy_v: Z) (ptcb_v: Z)
               (pevent2_v: Z) (y_v: Z) (cpu_sr_v: Z),
        atomic_event_task_wait_mutex(
          sg, eid, timeout, ls_inherit, tt, ls_wait) &&
        pevent == event_addr(sg, eid) &&
        mutex_pend_sched_pre(
          sg, eid, cur_tid, tcbcur, cur_t,
          ls_wait, ls0, ls2, timeout, tcbprio, prio_cur_in,
          event_grp_sched, event_tbl_sched,
          rdy_grp_sched, rdy_tbl_sched) *
        data_at(&pcp, unsigned char, pcp_v) *
        data_at(&mprio, unsigned char, mprio_v) *
        data_at(&rdy, unsigned char, rdy_v) *
        data_at(&ptcb, struct os_tcb *, ptcb_v) *
        data_at(&pevent2, struct os_event *, pevent2_v) *
        data_at(&y, unsigned char, y_v) *
        data_at(&cpu_sr, unsigned int, cpu_sr_v)
    */
    OS_Sched()/*@ where sg = sg, eid = eid, cur_tid = cur_tid,
        tcbcur = tcbcur, cur_t_pre = cur_t, ls_wait = ls_wait,
        ls_frame = ls0, timeout = timeout, ls_in = ls2, ls_out = ls3,
        cur_prio_in = tcbprio, prio_cur_pre = prio_cur_in,
        event_grp_pre = event_grp_sched,
        event_tbl_pre = event_tbl_sched,
        rdy_grp_pre = rdy_grp_sched,
        rdy_tbl_pre = rdy_tbl_sched */;
    OS_ENTER_CRITICAL()/*@ where sg = sg, ls_in = ls3, ls_out = ls4 */;
    /*@ Assert
        exists (pcp_v: Z) (mprio_v: Z) (rdy_v: Z) (ptcb_v: Z)
               (pevent2_v: Z) (y_v: Z) (cpu_sr_v: Z),
        (((atomic_mutex_pend_sched_resume(
             sg, eid, cur_tid, ls_wait, MutexPendResumeOK, ls3) &&
           resume_stat == 0 && resume_statpend == 0 &&
           resume_eventptr == 0) ||
          (atomic_mutex_pend_sched_resume(
             sg, eid, cur_tid, ls_wait, MutexPendResumeAbort, ls3) &&
           resume_stat == 0 && resume_statpend == 2 &&
           resume_eventptr == 0) ||
          (atomic_mutex_pend_sched_resume(
             sg, eid, cur_tid, ls_wait, MutexPendResumeTimeout, ls3) &&
           resume_stat == 16 && resume_statpend == 1 &&
           resume_eventptr == pevent)) &&
         InsideCritical(sg, ls4) &&
         pevent == event_addr(sg, eid) &&
         tcbcur == tcb_addr(sg, cur_tid) &&
         mutex_pend_cleanup_rest(sg, ls4, cur_tid, resume_t) *
         data_at(&OSTCBCur, struct os_tcb *, tcbcur) *
         data_at(&((OS_TCB *)tcbcur)->OSTCBStat,
                 unsigned char, resume_stat) *
         data_at(&((OS_TCB *)tcbcur)->OSTCBStatPend,
                 unsigned char, resume_statpend) *
         data_at(&((OS_TCB *)tcbcur)->OSTCBDly, unsigned int, 0) *
         data_at(&((OS_TCB *)tcbcur)->OSTCBEventPtr,
                 void *, resume_eventptr) *
         data_at(perr, unsigned char, perr_in) *
         data_at(&pcp, unsigned char, pcp_v) *
         data_at(&mprio, unsigned char, mprio_v) *
         data_at(&rdy, unsigned char, rdy_v) *
         data_at(&ptcb, struct os_tcb *, ptcb_v) *
         data_at(&pevent2, struct os_event *, pevent2_v) *
         data_at(&y, unsigned char, y_v) *
         data_at(&cpu_sr, unsigned int, cpu_sr_v))
    */
    switch (OSTCBCur->OSTCBStatPend) {
        case OS_STAT_PEND_OK:
             *perr = OS_ERR_NONE;
             break;

        case OS_STAT_PEND_ABORT:
             *perr = OS_ERR_PEND_ABORT;
             break;

        case OS_STAT_PEND_TO:
        default:
             OS_EventTaskRemove(OSTCBCur, pevent)/*@ where sg = sg,
                 ls_in = ls4, ls_rm = ls_rm, eid = eid, tid = cur_tid,
                 pt = tcbcur, cur_t_pre = resume_t,
                 stat_pre = 16, statpend_pre = 1, dly_pre = 0 */;
             *perr = OS_ERR_TIMEOUT;
             break;
    }
    /*@ Assert
        exists (pcp_v: Z) (mprio_v: Z) (rdy_v: Z) (ptcb_v: Z)
               (pevent2_v: Z) (y_v: Z) (cpu_sr_v: Z),
        (((atomic_mutex_pend_sched_resume(
             sg, eid, cur_tid, ls_wait, MutexPendResumeOK, ls3) &&
           atomic_task_pend_cleanup(cur_tid, ls4, tt, ls5) &&
           cleanup_stat == 0 && cleanup_statpend == 0 &&
           cleanup_eventptr == 0 && cleanup_err == 0) ||
          (atomic_mutex_pend_sched_resume(
             sg, eid, cur_tid, ls_wait, MutexPendResumeAbort, ls3) &&
           atomic_task_pend_cleanup(cur_tid, ls4, tt, ls5) &&
           cleanup_stat == 0 && cleanup_statpend == 2 &&
           cleanup_eventptr == 0 && cleanup_err == 14) ||
          (atomic_mutex_pend_sched_resume(
             sg, eid, cur_tid, ls_wait, MutexPendResumeTimeout, ls3) &&
           atomic_event_task_remove(cur_tid, eid, ls4, tt, ls_rm) &&
           atomic_task_pend_cleanup(cur_tid, ls_rm, tt, ls5) &&
           cleanup_stat == 16 && cleanup_statpend == 1 &&
           cleanup_eventptr == 0 && cleanup_err == 10)) &&
         InsideCritical(sg, ls5) &&
         pevent == event_addr(sg, eid) &&
         tcbcur == tcb_addr(sg, cur_tid) &&
         interrupt_inv(sg, ls5.IntrState) *
         mutex_pend_cleanup_nonintr_rest(sg, ls5, cur_tid, cleanup_t) *
         data_at(&OSTCBCur, struct os_tcb *, tcbcur) *
         data_at(&((OS_TCB *)tcbcur)->OSTCBStat,
                 unsigned char, cleanup_stat) *
         data_at(&((OS_TCB *)tcbcur)->OSTCBStatPend,
                 unsigned char, cleanup_statpend) *
         data_at(&((OS_TCB *)tcbcur)->OSTCBDly, unsigned int, 0) *
         data_at(&((OS_TCB *)tcbcur)->OSTCBEventPtr,
                 void *, cleanup_eventptr) *
         data_at(perr, unsigned char, cleanup_err) *
         data_at(&pcp, unsigned char, pcp_v) *
         data_at(&mprio, unsigned char, mprio_v) *
         data_at(&rdy, unsigned char, rdy_v) *
         data_at(&ptcb, struct os_tcb *, ptcb_v) *
         data_at(&pevent2, struct os_event *, pevent2_v) *
         data_at(&y, unsigned char, y_v) *
         data_at(&cpu_sr, unsigned int, cpu_sr_v))
    */
    OSTCBCur->OSTCBStat          = OS_STAT_RDY;
    OSTCBCur->OSTCBStatPend      = OS_STAT_PEND_OK;
    OSTCBCur->OSTCBEventPtr      = (OS_EVENT *)0;
#if (OS_EVENT_MULTI_EN > 0u)
    OSTCBCur->OSTCBEventMultiPtr = (OS_EVENT **)0;
    OSTCBCur->OSTCBEventMultiRdy = (OS_EVENT  *)0;
#endif
    OS_EXIT_CRITICAL()/*@ where sg = sg, ls_in = ls5, ls_out = ls_ret */;
    OS_TRACE_MUTEX_PEND_EXIT(*perr);
}
