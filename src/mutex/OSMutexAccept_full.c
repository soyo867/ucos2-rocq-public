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
/*@ Extern Coq (decode_PCP_from_cnt : Z -> Z) */
/*@ Extern Coq (decode_OwnerPrio_from_cnt : Z -> Z) */

/*@ Extern Coq (OS_ERR_NONE           : OSErrCode) */
/*@ Extern Coq (OS_ERR_PEVENT_NULL    : OSErrCode) */
/*@ Extern Coq (OS_ERR_PDATA_NULL     : OSErrCode) */
/*@ Extern Coq (OS_ERR_EVENT_TYPE     : OSErrCode) */
/*@ Extern Coq (OS_ERR_QUERY_ISR      : OSErrCode) */
/*@ Extern Coq (OS_ERR_PEND_ISR       : OSErrCode) */
/*@ Extern Coq (OS_ERR_PCP_LOWER      : OSErrCode) */
/*@ Extern Coq (OS_TRUE  : Z) */
/*@ Extern Coq (OS_FALSE : Z) */
/*@ Extern Coq (store_oseventtbl : StableGlobVars -> addr -> list Z -> Assertion) */

/*@ Extern Coq (coq_prop : Prop -> Assertion) */
/*@ Extern Coq (valid_stable_glob_vars : StableGlobVars -> Prop) */
/*@ Extern Coq (valid_event_id : StableGlobVars -> EventID -> Prop) */
/*@ Extern Coq (os_int_nesting_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_tcb_cur_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (event_snapshot_of_prop : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> EventID -> OSEventAbstractState -> Z -> Z -> Z -> Z -> list Z -> Prop) */
/*@ Extern Coq (task_prio_snapshot_of_prop : StableGlobVars -> Glob_TaskAbstractState -> TaskID -> TaskAbstractState -> Z -> Z -> Prop) */
/*@ Extern Coq (sched_tcb_cur_snapshot_prop : StableGlobVars -> SchedAbstractState -> Z -> Prop) */
/*@ Extern Coq (used_complete_event : StableGlobVars -> Glob_TaskAbstractState -> addr -> EventID -> OSEventAbstractState -> Assertion) */
/*@ Extern Coq (used_event_rest_no_type_cnt_ptr : StableGlobVars -> Glob_TaskAbstractState -> addr -> EventID -> OSEventAbstractState -> Assertion) */
/*@ Extern Coq (unused_complete_event : StableGlobVars -> addr -> EventID -> Assertion) */
/*@ Extern Coq (store_free_event_list : StableGlobVars -> list EventID -> Assertion) */
/*@ Extern Coq (store_int_state : StableGlobVars -> Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (interrupt_inv : StableGlobVars -> Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (interrupt_inv_no_int_nesting : StableGlobVars -> Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (task_inv : StableGlobVars -> Glob_TaskAbstractState -> Assertion) */
/*@ Extern Coq (task_inv_no_tid : StableGlobVars -> Glob_TaskAbstractState -> TaskID -> Assertion) */
/*@ Extern Coq (used_task_no_prio : StableGlobVars -> addr -> TaskID -> TaskAbstractState -> Assertion) */
/*@ Extern Coq (sched_inv : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> Assertion) */
/*@ Extern Coq (sched_inv_no_tcb_cur : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> Assertion) */
/*@ Extern Coq (tick_inv : StableGlobVars -> TickAbstractState -> Assertion) */
/*@ Extern Coq (cross_module_consistency : StableGlobVars -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (event_inv : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> Assertion) */
/*@ Extern Coq (event_inv_missing_usedevent : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> EventID -> OSEventAbstractState -> Assertion) */
/*@ Extern Coq (event_vaild_cond_prop : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> Prop) */
/*@ Extern Coq (interrupt_in_range : Glob_InterruptAbstractState -> Prop) */

/*@ Extern Coq (InsideCritical  : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (OutsideCritical : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (RTrans_C : StableGlobVars -> UCOS2_Verify_State -> StableGlobVars -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (GTrans_C : StableGlobVars -> UCOS2_Verify_State -> StableGlobVars -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (RTrans_Abs : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (GTrans_Abs : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (LastSeen : UCOS2_Verify_State -> (UCOS2_Verify_State -> Prop) -> Prop) */
/*@ Extern Coq (should_be_equal: {A} -> A -> A -> Prop) */
/*@ Extern Coq (crit_rel_no_os_state_change : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (crit_rel_event_only : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (event_core_fields_layout_prop : StableGlobVars -> EventID -> addr -> addr -> addr -> Prop) */
/*@ Extern Coq (task_prio_field_layout_prop : addr -> addr -> Prop) */
/*@ Extern Coq (event_count_value_range_prop : Z -> Prop) */
/*@ Extern Coq (task_runnable_prio_snapshot_prop : StableGlobVars -> Glob_TaskAbstractState -> TaskID -> TaskAbstractState -> addr -> Z -> Prop) */
/*@ Extern Coq (mutex_accept_acquire_post_state : UCOS2_Verify_State -> EventID -> OSEventAbstractState -> TaskID -> Priority -> UCOS2_Verify_State) */
/*@ Extern Coq (mutex_accept_restore_transition_prop : UCOS2_Verify_State -> UCOS2_Verify_State -> UCOS2_Verify_State -> EventID -> OSEventAbstractState -> TaskID -> Priority -> bool -> Prop) */
/*@ Extern Coq (UCOS2_Verify_inv : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (event_inv_no_eid : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> EventID -> Assertion) */
/*@ Extern Coq (mutex_accept_task_sched_guard_prop : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> Z -> Z -> TaskID -> TaskAbstractState -> Z -> Z -> Prop) */
/*@ Extern Coq (atomic_cmd : {A} -> program UCOS2_Verify_State A -> program (UCOS2_Verify_State -> Prop) A) */
/*@ Extern Coq (observe_mutex_accept_bool : OSErrCode * bool -> program (UCOS2_Verify_State -> Prop) Z) */
/*@ Extern Coq (OSMutexAccept_sem : StableGlobVars -> addr -> program UCOS2_Verify_State (OSErrCode * bool)) */

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
/*@ Import Coq Require Import Ucos2Verify.lib.tick */
/*@ Import Coq Require Import Ucos2Verify.lib.cross_module_invariants */
/*@ Import Coq Require Import Ucos2Verify.lib.error_codes */
/*@ Import Coq Require Import Ucos2Verify.lib.atomic_ops_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_rules_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_verify_inv */
/*@ Import Coq Require Import Ucos2Verify.lib.mutex_func_sem */
/*@ Import Coq Require Import Ucos2Verify.lib.array_abstraction */

typedef unsigned int OS_CPU_SR;

/* ============================================================ */
/* OS_CPU_SR_Save: atomic entry into critical section.          */
/* ============================================================ */
unsigned int OS_CPU_SR_Save()
/*@ With (sg: StableGlobVars) (ls0: UCOS2_Verify_State) (eid: EventID)
           (ecnt_in: Z)
    Require OutsideCritical(sg, ls0) &&
            interrupt_inv(sg, ls0.IntrState) &&
            event_inv_no_eid(sg, ls0.TskState, ls0.EventState, eid) &&
            coq_prop(event_vaild_cond_prop(
              sg, ls0.TskState, ls0.EventState)) &&
            coq_prop(event_count_value_range_prop(ecnt_in))
    Ensure  exists ls1,
            RTrans_C(sg, ls0, sg, ls1) &&
            InsideCritical(sg, ls1) &&
            interrupt_inv(sg, ls1.IntrState) &&
            event_inv_no_eid(sg, ls1.TskState, ls1.EventState, eid) &&
            coq_prop(event_vaild_cond_prop(
              sg, ls0.TskState, ls0.EventState)) &&
            coq_prop(event_count_value_range_prop(ecnt_in)) &&
            coq_prop(crit_rel_no_os_state_change(ls0, ls1)) &&
            __return == __return
*/
;

/* ============================================================ */
/* OS_CPU_SR_Restore: atomic exit from critical section.        */
/* ============================================================ */
void OS_CPU_SR_Restore(unsigned int cpu_sr)
/*@ With (sg: StableGlobVars)
           (ls0: UCOS2_Verify_State) (ls1: UCOS2_Verify_State)
           (ls2: UCOS2_Verify_State) (eid: EventID)
           (e: OSEventAbstractState) (tid: TaskID) (origPrio: Priority)
           (ecnt_in: Z) (acquired: bool)
    Require InsideCritical(sg, ls1) &&
            interrupt_inv(sg, ls1.IntrState) &&
            event_inv_no_eid(sg, ls1.TskState, ls1.EventState, eid) &&
            coq_prop(event_vaild_cond_prop(
              sg, ls0.TskState, ls0.EventState)) &&
            coq_prop(event_count_value_range_prop(ecnt_in)) &&
            coq_prop(mutex_accept_restore_transition_prop(
              ls0, ls1, ls2, eid, e, tid, origPrio, acquired))
    Ensure  GTrans_C(sg, ls1, sg, ls2) &&
            OutsideCritical(sg, ls2) &&
            interrupt_inv(sg, ls2.IntrState) &&
            event_inv_no_eid(sg, ls2.TskState, ls2.EventState, eid) &&
            coq_prop(event_vaild_cond_prop(
              sg, ls0.TskState, ls0.EventState)) &&
            coq_prop(event_count_value_range_prop(ecnt_in)) &&
            coq_prop(mutex_accept_restore_transition_prop(
              ls0, ls1, ls2, eid, e, tid, origPrio, acquired))
*/
;

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
#define  OS_ERR_PEND_ISR                2u
#define  OS_ERR_PCP_LOWER               120u
#define  OS_MUTEX_KEEP_LOWER_8          0x00FFu
#define  OS_MUTEX_KEEP_UPPER_8          0xFF00u
#define  OS_MUTEX_AVAILABLE             0x00FFu
#define  OS_PRIO_MUTEX_CEIL_DIS         0xFFu

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
extern  INT8U    OSPrioCur;

/* ============================================================ */
/* OSMutexAccept_full: source-order faithful OSMutexAccept.     */
/*                                                              */
/* The post retains the exact OSEventCnt bit update and owner   */
/* pointer selected by the source control-flow split.           */
/* ============================================================ */
BOOLEAN  OSMutexAccept_full (OS_EVENT *pevent, INT8U *perr)
/*@ With (sg: StableGlobVars) (ls0: UCOS2_Verify_State) X
           (eid: EventID) (e: OSEventAbstractState)
           (cur_tid: TaskID) (cur_t: TaskAbstractState)
           (isr: Z) (pe: addr) (pd: addr) (etype: Z) (perr_in: Z)
           (ecnt_in: Z) (eptr_in: Z) (egrp_in: Z) (evtL_in: list Z)
           (tcbcur: Z) (tcbprio: Z)
    Require
        data_at(perr, unsigned char, perr_in) &&
        isr >= 0 &&
        isr == intNesting(ls0.IntrState) &&
        perr != 0 &&
        pd == perr &&
        pe == pevent &&
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
        coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) &&
        safeExec(LastSeen(ls0),
                 bind(atomic_cmd(OSMutexAccept_sem(sg, pevent)),
                      observe_mutex_accept_bool), X) &&
        OutsideCritical(sg, ls0) &&
        UCOS2_Verify_inv(sg, ls0) &&
        coq_prop(valid_stable_glob_vars(sg)) &&
        (
            pevent == 0 ||
            (pevent != 0 &&
             pevent == event_addr(sg, eid) &&
             coq_prop(valid_event_id(sg, eid)) &&
             0 <= etype && etype <= 255 &&
             coq_prop(event_snapshot_of_prop(sg, ls0.TskState, ls0.EventState,
                                             eid, e, etype, ecnt_in, eptr_in,
                                             egrp_in, evtL_in)) &&
             coq_prop(event_core_fields_layout_prop(
               sg, eid,
               &((OS_EVENT *)pevent)->OSEventType,
               &((OS_EVENT *)pevent)->OSEventPtr,
               &((OS_EVENT *)pevent)->OSEventCnt)) &&
             coq_prop(mutex_accept_task_sched_guard_prop(
               sg, ls0.TskState, ls0.SchedState, etype, isr,
               cur_tid, cur_t, tcbcur, tcbprio)) &&
             coq_prop(task_prio_field_layout_prop(
               tcbcur, &((OS_TCB *)tcbcur)->OSTCBPrio)))
        )
    Ensure
        exists (ls_post : UCOS2_Verify_State) (retv : Z),
        safeExec(LastSeen(ls_post), return(retv), X) &&
        OutsideCritical(sg, ls_post) &&
        UCOS2_Verify_inv(sg, ls_post) &&
        __return == retv &&
        pe == pevent &&
        pd == perr &&
        (
            (__return == 0 &&
             pevent == 0 &&
             data_at(perr, unsigned char, 4)) ||
            (__return == 0 &&
             pevent != 0 &&
             etype != 4 &&
             coq_prop(event_snapshot_of_prop(sg, ls_post.TskState,
                                             ls_post.EventState, eid, e,
                                             etype, ecnt_in, eptr_in,
                                             egrp_in, evtL_in)) &&
             data_at(perr, unsigned char, 1)) ||
            (__return == 0 &&
             pevent != 0 &&
             etype == 4 &&
             isr > 0 &&
             coq_prop(event_snapshot_of_prop(sg, ls_post.TskState,
                                             ls_post.EventState, eid, e,
                                             etype, ecnt_in, eptr_in,
                                             egrp_in, evtL_in)) &&
             data_at(perr, unsigned char, 2)) ||
            (exists (e_post: OSEventAbstractState) (ecnt_post: Z),
             __return == 1 && pevent != 0 && etype == 4 && isr <= 0 &&
             (ecnt_in & OS_MUTEX_KEEP_LOWER_8) == OS_MUTEX_AVAILABLE &&
             ecnt_post == ((ecnt_in & OS_MUTEX_KEEP_UPPER_8) |
                           (INT16U)tcbprio) &&
             coq_prop(event_snapshot_of_prop(sg, ls_post.TskState,
                                             ls_post.EventState, eid, e_post,
                                             4, ecnt_post, tcbcur,
                                             egrp_in, evtL_in)) &&
             (((INT8U)(ecnt_in >> 8u) != OS_PRIO_MUTEX_CEIL_DIS &&
               tcbprio <= (INT8U)(ecnt_in >> 8u) &&
               data_at(perr, unsigned char, 120)) ||
              (((INT8U)(ecnt_in >> 8u) == OS_PRIO_MUTEX_CEIL_DIS ||
                tcbprio > (INT8U)(ecnt_in >> 8u)) &&
               data_at(perr, unsigned char, 0)))) ||
            (__return == 0 &&
             pevent != 0 &&
             etype == 4 &&
             isr <= 0 &&
             (ecnt_in & OS_MUTEX_KEEP_LOWER_8) != OS_MUTEX_AVAILABLE &&
             coq_prop(event_snapshot_of_prop(sg, ls_post.TskState,
                                             ls_post.EventState, eid, e,
                                             etype, ecnt_in, eptr_in,
                                             egrp_in, evtL_in)) &&
             data_at(perr, unsigned char, 0))
        )
*/
{
    INT8U      pcp    = 0u;
    OS_CPU_SR  cpu_sr = 0u;

    if (pevent == (OS_EVENT *)0) {
        *perr = OS_ERR_PEVENT_NULL;
        return (OS_FALSE);
    }

    /*@ exists (pevent_v: Z),
        pevent_v == pe &&
        pevent_v == event_addr(sg, eid) &&
        coq_prop(event_snapshot_of_prop(sg, ls0.TskState, ls0.EventState,
                                        eid, e, etype, ecnt_in, eptr_in,
                                        egrp_in, evtL_in)) &&
        coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)pevent_v)->OSEventType,
          &((OS_EVENT *)pevent_v)->OSEventPtr,
          &((OS_EVENT *)pevent_v)->OSEventCnt)) &&
        data_at(&pevent, struct os_event *, pevent_v) *
        UCOS2_Verify_inv(sg, ls0)
        which implies
        data_at(&pevent, struct os_event *, pevent_v) *
        interrupt_inv(sg, ls0.IntrState) *
        task_inv(sg, ls0.TskState) *
        sched_inv(sg, ls0.TskState, ls0.SchedState) *
        data_at(&((OS_EVENT *)pevent_v)->OSEventType, unsigned char, etype) *
        data_at(&((OS_EVENT *)pevent_v)->OSEventPtr, void *, eptr_in) *
        data_at(&((OS_EVENT *)pevent_v)->OSEventCnt, unsigned short, ecnt_in) *
        used_event_rest_no_type_cnt_ptr(sg, ls0.TskState, pevent_v, eid, e) *
        event_inv_no_eid(sg, ls0.TskState, ls0.EventState, eid) *
        tick_inv(sg, ls0.TickState) *
        coq_prop(cross_module_consistency(sg, ls0)) *
        coq_prop(event_snapshot_of_prop(sg, ls0.TskState, ls0.EventState,
                                        eid, e, etype, ecnt_in, eptr_in,
                                        egrp_in, evtL_in)) *
        coq_prop(event_vaild_cond_prop(
          sg, ls0.TskState, ls0.EventState)) *
        coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)pevent_v)->OSEventType,
          &((OS_EVENT *)pevent_v)->OSEventPtr,
          &((OS_EVENT *)pevent_v)->OSEventCnt)) *
        coq_prop(event_count_value_range_prop(ecnt_in))
    */
    if (pevent->OSEventType != OS_EVENT_TYPE_MUTEX) {
        *perr = OS_ERR_EVENT_TYPE;
        return (OS_FALSE);
    }
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
        *perr = OS_ERR_PEND_ISR;
        return (OS_FALSE);
    }

    /*@ etype == 4 && (INT32U)isr <= 0 &&
        coq_prop(mutex_accept_task_sched_guard_prop(
          sg, ls0.TskState, ls0.SchedState, etype, isr,
          cur_tid, cur_t, tcbcur, tcbprio))
        which implies
        etype == 4 && (INT32U)isr <= 0 && tcbcur != 0 &&
        coq_prop(sched_tcb_cur_snapshot_prop(
          sg, ls0.SchedState, tcbcur)) *
        coq_prop(task_runnable_prio_snapshot_prop(
          sg, ls0.TskState, cur_tid, cur_t, tcbcur, tcbprio))
    */
    /*@ isr == intNesting(ls0.IntrState) &&
        data_at(&OSIntNesting, unsigned char, isr) *
        interrupt_inv_no_int_nesting(sg, ls0.IntrState) *
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
        which implies
        isr == intNesting(ls0.IntrState) &&
        interrupt_inv(sg, ls0.IntrState) *
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
    */
    /*@ etype == 4 && (INT32U)isr <= 0 && tcbcur != 0 &&
        coq_prop(sched_tcb_cur_snapshot_prop(
          sg, ls0.SchedState, tcbcur)) &&
        coq_prop(task_runnable_prio_snapshot_prop(
          sg, ls0.TskState, cur_tid, cur_t, tcbcur, tcbprio)) &&
        coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) &&
        coq_prop(task_prio_field_layout_prop(
          tcbcur, &((OS_TCB *)tcbcur)->OSTCBPrio)) &&
        task_inv(sg, ls0.TskState) *
        sched_inv(sg, ls0.TskState, ls0.SchedState)
        which implies
        etype == 4 && (INT32U)isr <= 0 && tcbcur != 0 &&
        coq_prop(sched_tcb_cur_snapshot_prop(
          sg, ls0.SchedState, tcbcur)) &&
        coq_prop(task_runnable_prio_snapshot_prop(
          sg, ls0.TskState, cur_tid, cur_t, tcbcur, tcbprio)) &&
        data_at(&((OS_TCB *)tcbcur)->OSTCBPrio, unsigned char, tcbprio) *
        used_task_no_prio(sg, tcbcur, cur_tid, cur_t) *
        task_inv_no_tid(sg, ls0.TskState, cur_tid) *
        data_at(&OSTCBCur, struct os_tcb *, tcbcur) *
        sched_inv_no_tcb_cur(sg, ls0.TskState, ls0.SchedState) *
        coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) *
        coq_prop(task_prio_field_layout_prop(
          tcbcur, &((OS_TCB *)tcbcur)->OSTCBPrio))
    */
    cpu_sr = OS_CPU_SR_Save()/*@ where sg = sg, ls0 = ls0,
        eid = eid, ecnt_in = ecnt_in */;
    pcp = (INT8U)(pevent->OSEventCnt >> 8u);
    if ((pevent->OSEventCnt & OS_MUTEX_KEEP_LOWER_8) == OS_MUTEX_AVAILABLE) {
        pevent->OSEventCnt &= OS_MUTEX_KEEP_UPPER_8;
        pevent->OSEventCnt |= (INT16U)OSTCBCur->OSTCBPrio;
        pevent->OSEventPtr  = (void *)OSTCBCur;
        if ((pcp != OS_PRIO_MUTEX_CEIL_DIS) &&
            (OSTCBCur->OSTCBPrio <= pcp)) {
            /*@ exists (ls_cs: UCOS2_Verify_State),
                InsideCritical(sg, ls_cs) *
                interrupt_inv(sg, ls_cs.IntrState) *
                event_inv_no_eid(sg, ls_cs.TskState, ls_cs.EventState, eid) *
                coq_prop(event_vaild_cond_prop(
                  sg, ls0.TskState, ls0.EventState)) *
                coq_prop(event_count_value_range_prop(ecnt_in)) *
                coq_prop(crit_rel_no_os_state_change(ls0, ls_cs))
                which implies
                exists (ls_cs: UCOS2_Verify_State) (ls_next: UCOS2_Verify_State),
                InsideCritical(sg, ls_cs) *
                interrupt_inv(sg, ls_cs.IntrState) *
                event_inv_no_eid(sg, ls_cs.TskState, ls_cs.EventState, eid) *
                coq_prop(event_vaild_cond_prop(
                  sg, ls0.TskState, ls0.EventState)) *
                coq_prop(event_count_value_range_prop(ecnt_in)) *
                coq_prop(mutex_accept_restore_transition_prop(
                  ls0, ls_cs, ls_next,
                  eid, e, cur_tid, tcbprio, true))
            */
            OS_CPU_SR_Restore(cpu_sr)/*@ where sg = sg, ls0 = ls0,
                eid = eid, e = e, tid = cur_tid, origPrio = tcbprio,
                ecnt_in = ecnt_in, acquired = true */;
            *perr = OS_ERR_PCP_LOWER;
            return (OS_TRUE);
        } else {
            /*@ exists (ls_cs: UCOS2_Verify_State),
                InsideCritical(sg, ls_cs) *
                interrupt_inv(sg, ls_cs.IntrState) *
                event_inv_no_eid(sg, ls_cs.TskState, ls_cs.EventState, eid) *
                coq_prop(event_vaild_cond_prop(
                  sg, ls0.TskState, ls0.EventState)) *
                coq_prop(event_count_value_range_prop(ecnt_in)) *
                coq_prop(crit_rel_no_os_state_change(ls0, ls_cs))
                which implies
                exists (ls_cs: UCOS2_Verify_State) (ls_next: UCOS2_Verify_State),
                InsideCritical(sg, ls_cs) *
                interrupt_inv(sg, ls_cs.IntrState) *
                event_inv_no_eid(sg, ls_cs.TskState, ls_cs.EventState, eid) *
                coq_prop(event_vaild_cond_prop(
                  sg, ls0.TskState, ls0.EventState)) *
                coq_prop(event_count_value_range_prop(ecnt_in)) *
                coq_prop(mutex_accept_restore_transition_prop(
                  ls0, ls_cs, ls_next,
                  eid, e, cur_tid, tcbprio, true))
            */
            OS_CPU_SR_Restore(cpu_sr)/*@ where sg = sg, ls0 = ls0,
                eid = eid, e = e, tid = cur_tid, origPrio = tcbprio,
                ecnt_in = ecnt_in, acquired = true */;
            *perr = OS_ERR_NONE;
            return (OS_TRUE);
        }
    }
    /*@ exists (ls_cs: UCOS2_Verify_State),
        InsideCritical(sg, ls_cs) *
        interrupt_inv(sg, ls_cs.IntrState) *
        event_inv_no_eid(sg, ls_cs.TskState, ls_cs.EventState, eid) *
        coq_prop(event_vaild_cond_prop(
          sg, ls0.TskState, ls0.EventState)) *
        coq_prop(event_count_value_range_prop(ecnt_in)) *
        coq_prop(crit_rel_no_os_state_change(ls0, ls_cs))
        which implies
        exists (ls_cs: UCOS2_Verify_State) (ls_next: UCOS2_Verify_State),
        InsideCritical(sg, ls_cs) *
        interrupt_inv(sg, ls_cs.IntrState) *
        event_inv_no_eid(sg, ls_cs.TskState, ls_cs.EventState, eid) *
        coq_prop(event_vaild_cond_prop(
          sg, ls0.TskState, ls0.EventState)) *
        coq_prop(event_count_value_range_prop(ecnt_in)) *
        coq_prop(mutex_accept_restore_transition_prop(
          ls0, ls_cs, ls_next, eid, e, cur_tid, tcbprio, false))
    */
    OS_CPU_SR_Restore(cpu_sr)/*@ where sg = sg, ls0 = ls0,
        eid = eid, e = e, tid = cur_tid, origPrio = tcbprio,
        ecnt_in = ecnt_in, acquired = false */;
    *perr = OS_ERR_NONE;
    return (OS_FALSE);
}
