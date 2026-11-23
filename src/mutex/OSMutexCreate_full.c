/*@ Extern Coq (program :: * => * => *) */
/*@ Extern Coq (unit :: *) */
/*@ Extern Coq (safeExec : {Sigma} {A} -> (Sigma -> Prop) -> program Sigma A -> (A -> Sigma -> Prop) -> Prop) */
/*@ Extern Coq (bind: {Sigma} {A} {B} ->  program Sigma A -> (A -> program Sigma B) -> program Sigma B) */
/*@ Extern Coq (return : {Sigma} {A} -> A -> program Sigma A) */
/*@ Extern Coq (tt: unit) */
/*@ Extern Coq (ATrue: {A} -> A -> Prop) */
/*@ Extern Coq (equiv: {T} -> T -> T -> Prop) */

/*@ Extern Coq (cons : {A} -> A -> list A -> list A) */
/*@ Extern Coq (nil : {A} -> list A) */
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
/*@ Extern Coq (not : Prop -> Prop) */
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
/*@ Extern Coq Record Glob_TaskAbstractState {
  inUsedTaskStates : TaskID -> option TaskAbstractState;
  unUsedTaskStates : list TaskID;
  tcbListHead      : option TaskID;
  prioTbl          : Priority -> PrioTblEntry;
  taskCount        : Z;
} */
/*@ Extern Coq (PTFree : PrioTblEntry) */
/*@ Extern Coq (PTReserved : PrioTblEntry) */
/*@ Extern Coq (mfPCP           : MutexFields -> Priority) */
/*@ Extern Coq (mfOwner         : MutexFields -> option TaskID) */
/*@ Extern Coq (mfOwnerOrigPrio : MutexFields -> option Priority) */

/*@ Extern Coq (OS_ERR_NONE           : OSErrCode) */
/*@ Extern Coq (OS_ERR_PEVENT_NULL    : OSErrCode) */
/*@ Extern Coq (OS_ERR_PDATA_NULL     : OSErrCode) */
/*@ Extern Coq (OS_ERR_EVENT_TYPE     : OSErrCode) */
/*@ Extern Coq (OS_ERR_QUERY_ISR      : OSErrCode) */
/*@ Extern Coq (OS_ERR_CREATE_ISR     : OSErrCode) */
/*@ Extern Coq (OS_ERR_PRIO_INVALID   : OSErrCode) */
/*@ Extern Coq (OS_ERR_PRIO_EXIST     : OSErrCode) */
/*@ Extern Coq (OS_TRUE  : Z) */
/*@ Extern Coq (OS_FALSE : Z) */
/*@ Extern Coq (store_oseventtbl : StableGlobVars -> addr -> list Z -> Assertion) */
/*@ Extern Coq (store_oseventtbl_missing_i : StableGlobVars -> addr -> list Z -> Z -> Assertion) */
/*@ Extern Coq (store_priotbl_list : StableGlobVars -> list addr -> Assertion) */
/*@ Extern Coq (store_priotbl_list_missing_i : StableGlobVars -> list addr -> Z -> Assertion) */
/*@ Extern Coq (prio_tbl_list_rel : StableGlobVars -> Glob_TaskAbstractState -> list addr -> Prop) */
/*@ Extern Coq (event_tbl_addr_list_rel : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> addr -> list Z -> Prop) */
/*@ Extern Coq (zero_event_tbl : list Z -> list Z) */

/*@ Extern Coq (coq_prop : Prop -> Assertion) */
/*@ Extern Coq (valid_stable_glob_vars : StableGlobVars -> Prop) */
/*@ Extern Coq (valid_event_id : StableGlobVars -> EventID -> Prop) */
/*@ Extern Coq (valid_mutex_pcp : StableGlobVars -> Priority -> Prop) */
/*@ Extern Coq (store_used_event_map_missing_i : StableGlobVars -> (EventID -> option OSEventAbstractState) -> EventID -> Assertion) */
/*@ Extern Coq (used_complete_event : StableGlobVars -> Glob_TaskAbstractState -> addr -> EventID -> OSEventAbstractState -> Assertion) */
/*@ Extern Coq (unused_complete_event : StableGlobVars -> addr -> EventID -> Assertion) */
/*@ Extern Coq (store_free_event_list : StableGlobVars -> list EventID -> Assertion) */
/*@ Extern Coq (store_free_event_nodes : StableGlobVars -> list EventID -> Assertion) */
/*@ Extern Coq (free_event_head : StableGlobVars -> list EventID -> addr) */
/*@ Extern Coq (store_int_state : StableGlobVars -> Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (interrupt_inv : StableGlobVars -> Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (interrupt_inv_no_int_nesting : StableGlobVars -> Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (task_inv : StableGlobVars -> Glob_TaskAbstractState -> Assertion) */
/*@ Extern Coq (task_inv_no_priotbl : StableGlobVars -> Glob_TaskAbstractState -> Assertion) */
/*@ Extern Coq (sched_inv : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> Assertion) */
/*@ Extern Coq (event_inv : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> Assertion) */
/*@ Extern Coq (event_inv_no_free_head : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> Assertion) */
/*@ Extern Coq (event_inv_free_head_rest : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> list EventID -> Assertion) */
/*@ Extern Coq (event_free_head_snapshot_prop : StableGlobVars -> Glob_EventAbstractState -> EventID -> list EventID -> addr -> addr -> Prop) */
/*@ Extern Coq (event_core_fields_layout_prop : StableGlobVars -> EventID -> addr -> addr -> addr -> Prop) */
/*@ Extern Coq (event_free_list_head_prop : StableGlobVars -> Glob_EventAbstractState -> addr -> Prop) */
/*@ Extern Coq (event_free_list_exact_prop : Glob_EventAbstractState -> list EventID -> Prop) */
/*@ Extern Coq (event_snapshot_of_prop : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> EventID -> OSEventAbstractState -> Z -> Z -> addr -> Z -> list Z -> Prop) */
/*@ Extern Coq (tick_inv : StableGlobVars -> TickAbstractState -> Assertion) */
/*@ Extern Coq (cross_module_consistency : StableGlobVars -> UCOS2_Verify_State -> Prop) */
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
/*@ Extern Coq (crit_rel_task_event : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (UCOS2_Verify_inv : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (UCOS2_Verify_inv_no_int_nesting : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (atomic_cmd : {A} -> program UCOS2_Verify_State A -> program (UCOS2_Verify_State -> Prop) A) */
/*@ Extern Coq (observe_mutex_create_ptr : StableGlobVars -> OSErrCode * option EventID -> program (UCOS2_Verify_State -> Prop) Z) */
/*@ Extern Coq (observe_unit_void : unit -> program (UCOS2_Verify_State -> Prop) unit) */
/*@ Extern Coq (OSMutexCreate_sem : StableGlobVars -> Priority -> program UCOS2_Verify_State (OSErrCode * option EventID)) */
/*@ Extern Coq (atomic_event_wait_list_init : EventID -> UCOS2_Verify_State -> unit -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (os_int_nesting_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_event_free_list_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_tcb_prio_tbl_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (mutex_create_priotbl_after : StableGlobVars -> Priority -> list addr -> list addr) */
/*@ Extern Coq (mutex_create_pcp_slot_available_prop : StableGlobVars -> Priority -> list addr -> Prop) */
/*@ Extern Coq (task_event_id_unreferenced_prop : UCOS2_Verify_State -> EventID -> Prop) */
/*@ Extern Coq (mutex_create_free_snapshot_prop : StableGlobVars -> UCOS2_Verify_State -> EventID -> list EventID -> addr -> addr -> Prop) */
/*@ Extern Coq (mutex_create_priority_input_prop : Priority -> Priority -> Prop) */
/*@ Extern Coq (mutex_create_fresh_event : Priority -> OSEventAbstractState) */
/*@ Extern Coq (mutex_create_initialized_event : StableGlobVars -> UCOS2_Verify_State -> Priority -> EventID -> Assertion) */
/*@ Extern Coq (mutex_create_head_open_inv : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (mutex_create_node_open_inv : StableGlobVars -> UCOS2_Verify_State -> list EventID -> Assertion) */
/*@ Extern Coq (mutex_create_unused_event_no_ptr : addr -> Assertion) */
/*@ Extern Coq (mutex_create_wait_table_uninitialized : addr -> Assertion) */
/*@ Extern Coq (mutex_create_wait_table_zero : addr -> Assertion) */
/*@ Extern Coq (mutex_create_transient_frame : StableGlobVars -> UCOS2_Verify_State -> Priority -> EventID -> list EventID -> list addr -> Assertion) */
/*@ Extern Coq (mutex_create_restore_frame : StableGlobVars -> UCOS2_Verify_State -> Priority -> EventID -> list EventID -> list addr -> bool -> Assertion) */
/*@ Extern Coq (mutex_create_success_transition_prop : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> Priority -> EventID -> list EventID -> Prop) */
/*@ Extern Coq (mutex_create_restore_transition_prop : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> UCOS2_Verify_State -> Priority -> EventID -> list EventID -> bool -> Prop) */
/*@ Extern Coq (mutex_create_result_prop : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> Z -> Z -> list addr -> addr -> EventID -> list EventID -> Z -> Z -> Prop) */

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
/*@ Import Coq Require Import Ucos2Verify.lib.error_codes */
/*@ Import Coq Require Import Ucos2Verify.lib.atomic_ops_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_rules_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_verify_inv */
/*@ Import Coq Require Import Ucos2Verify.lib.mutex_func_sem */
/*@ Import Coq Require Import Ucos2Verify.lib.array_abstraction */
/*@ Import Coq Require Import Ucos2Verify.lib.tick */
/*@ Import Coq Require Import Ucos2Verify.lib.cross_module_invariants */
/*@ Import Coq Require Import Ucos2Verify.lib.mutex_create_spec */

typedef unsigned int OS_CPU_SR;

unsigned int OS_CPU_SR_Save()
/*@ With (sg: StableGlobVars) (ls0: UCOS2_Verify_State)
    Require OutsideCritical(sg, ls0) &&
            UCOS2_Verify_inv(sg, ls0)
    Ensure  exists ls1,
            RTrans_C(sg, ls0, sg, ls1) &&
            InsideCritical(sg, ls1) &&
            UCOS2_Verify_inv(sg, ls1) &&
            coq_prop(crit_rel_no_os_state_change(ls0, ls1)) &&
            __return == __return
*/
;

void OS_CPU_SR_Restore(unsigned int cpu_sr)
/*@ With (sg: StableGlobVars)
           (ls0: UCOS2_Verify_State)
           (ls_inside: UCOS2_Verify_State)
           (pcp: Priority) (eid: EventID) (rest: list EventID)
           (prio_before: list addr) (success: bool)
    Require InsideCritical(sg, ls_inside) &&
            mutex_create_restore_frame(
              sg, ls0, pcp, eid, rest, prio_before, success) &&
            coq_prop(crit_rel_no_os_state_change(ls0, ls_inside))
    Ensure  exists ls_post,
            GTrans_C(sg, ls_inside, sg, ls_post) &&
            OutsideCritical(sg, ls_post) &&
            mutex_create_restore_frame(
              sg, ls0, pcp, eid, rest, prio_before, success) &&
            coq_prop(mutex_create_restore_transition_prop(
              sg, ls0, ls_inside, ls_post,
              pcp, eid, rest, success))
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
#define  OS_PRIO_MUTEX_CEIL_DIS         0xFFu
#define  OS_EVENT_TBL_SIZE              ((OS_LOWEST_PRIO) / 8u + 1u)
#define  OS_EVENT_TYPE_UNUSED           0u
#define  OS_EVENT_TYPE_MUTEX            4u
#define  OS_MUTEX_AVAILABLE             0x00FFu
#define  OS_ERR_NONE                    0u
#define  OS_ERR_EVENT_TYPE              1u
#define  OS_ERR_PEVENT_NULL             4u
#define  OS_ERR_QUERY_ISR               6u
#define  OS_ERR_PDATA_NULL              9u
#define  OS_ERR_PRIO_INVALID            42u
#define  OS_ERR_PRIO_EXIST              40u
#define  OS_ERR_CREATE_ISR              16u

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
    OS_PRIO  OSEventTbl[OS_EVENT_TBL_SIZE];
} OS_EVENT;

extern  INT8U    OSIntNesting;
extern  INT8U    OSLockNesting;
extern  OS_TCB  *OSTCBPrioTbl[64];
extern  OS_EVENT *OSEventFreeList;

void OS_EventWaitListInit(OS_EVENT *pevent)
/*@ Require mutex_create_wait_table_uninitialized(pevent)
    Ensure  mutex_create_wait_table_zero(pevent)
*/
;

/* ============================================================ */
/* OSMutexCreate_full: µC/OS-II os_mutex.c 字面实现.            */
/*                                                              */
/* 目标(纯 list + 字面变下标):                                  */
/*   - 移除 OS_MutexPrioAvailable/Reserve/Release 3 helper      */
/*   - body 还原 µC/OS-II 字面 OSTCBPrioTbl[prio] 3 处变下标    */
/*   - PRE/POST 数组资源只用 list 谓词                          */
/*                                                              */
/* 字面 body 中 OSTCBPrioTbl[prio] 访问点(共 3 处):              */
/*   (1) 读: if (OSTCBPrioTbl[prio] != 0)  检查可用性           */
/*   (2) 写: OSTCBPrioTbl[prio] = 1;        reserve             */
/*   (3) 写: OSTCBPrioTbl[prio] = 0;        release (rollback)  */
/*                                                              */
/* OSEventTbl[0..7] = 0 是 8 路常量下标,非变下标,保留字面.      */
/* ============================================================ */
OS_EVENT *OSMutexCreate_full (INT8U prio, INT8U *perr)
/*@ With (sg: StableGlobVars) (ls0: UCOS2_Verify_State) X
           (eid: EventID) (isr: Z) (prio_in: Z) (perr_in: Z) (pd: addr)
           (freelist_in: addr) (next_in: addr) (free_rest: list EventID)
           (prioL_in: list addr)
    Require
        data_at(perr, unsigned char, perr_in) &&
        prio == prio_in &&
        coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
        0 <= prio_in && prio_in <= 255 &&
        pd == perr &&
        perr != 0 &&
        isr == intNesting(ls0.IntrState) &&
        0 <= isr && isr <= 255 &&
        coq_prop(event_free_list_head_prop(sg, ls0.EventState, freelist_in)) &&
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
        coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
        coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
        safeExec(LastSeen(ls0),
                 bind(atomic_cmd(OSMutexCreate_sem(sg, prio)),
                      observe_mutex_create_ptr(sg)), X) &&
        OutsideCritical(sg, ls0) &&
        UCOS2_Verify_inv(sg, ls0) &&
        coq_prop(valid_stable_glob_vars(sg)) &&
        coq_prop(prio_tbl_list_rel(sg, ls0.TskState, prioL_in)) &&
        coq_prop(mutex_create_free_snapshot_prop(
          sg, ls0, eid, free_rest, freelist_in, next_in)) &&
        (
          freelist_in == 0 ||
          (freelist_in != 0 &&
           coq_prop(event_core_fields_layout_prop(
             sg, eid,
             &((OS_EVENT *)freelist_in)->OSEventType,
             &((OS_EVENT *)freelist_in)->OSEventPtr,
             &((OS_EVENT *)freelist_in)->OSEventCnt)))
        )
    Ensure
        exists (ls_post : UCOS2_Verify_State) (retv : Z) (errv : Z),
        safeExec(LastSeen(ls_post), return(retv), X) &&
        OutsideCritical(sg, ls_post) &&
        UCOS2_Verify_inv(sg, ls_post) &&
        __return == retv &&
        data_at(pd, unsigned char, errv) &&
        prio == prio_in &&
        pd != 0 &&
        coq_prop(mutex_create_result_prop(
          sg, ls0, ls_post, prio_in, isr, prioL_in,
          freelist_in, eid, free_rest, retv, errv))
*/
{
    OS_EVENT  *pevent = (OS_EVENT *)0;
    OS_CPU_SR  cpu_sr = 0u;

    if (prio != OS_PRIO_MUTEX_CEIL_DIS) {
        if (prio >= OS_LOWEST_PRIO) {
           *perr = OS_ERR_PRIO_INVALID;
            return ((OS_EVENT *)0);
        }
    }
    /*@ isr == intNesting(ls0.IntrState) &&
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
        UCOS2_Verify_inv(sg, ls0)
        which implies
        isr == intNesting(ls0.IntrState) &&
        data_at(&OSIntNesting, unsigned char, isr) *
        UCOS2_Verify_inv_no_int_nesting(sg, ls0) *
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
    */
    if (OSIntNesting > 0u) {
        /*@ isr == intNesting(ls0.IntrState) &&
            data_at(&OSIntNesting, unsigned char, isr) *
            UCOS2_Verify_inv_no_int_nesting(sg, ls0) *
            coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
            which implies
            isr == intNesting(ls0.IntrState) &&
            UCOS2_Verify_inv(sg, ls0) *
            coq_prop(os_int_nesting_addr(sg, &OSIntNesting))
        */
        *perr = OS_ERR_CREATE_ISR;
        return ((OS_EVENT *)0);
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

    cpu_sr = OS_CPU_SR_Save();
    /*@ exists (ls1: UCOS2_Verify_State),
          InsideCritical(sg, ls1) *
          UCOS2_Verify_inv(sg, ls1) *
          coq_prop(crit_rel_no_os_state_change(ls0, ls1)) *
          coq_prop(prio_tbl_list_rel(sg, ls0.TskState, prioL_in)) *
          coq_prop(event_free_list_head_prop(
            sg, ls0.EventState, freelist_in)) *
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList))
        which implies
        exists (ls1: UCOS2_Verify_State),
          InsideCritical(sg, ls1) *
          mutex_create_head_open_inv(sg, ls1) *
          store_priotbl_list(sg, prioL_in) *
          data_at(&OSEventFreeList, struct os_event *, freelist_in) *
          coq_prop(crit_rel_no_os_state_change(ls0, ls1)) *
          coq_prop(prio_tbl_list_rel(sg, ls1.TskState, prioL_in)) *
          coq_prop(event_free_list_head_prop(
            sg, ls1.EventState, freelist_in)) *
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList))
    */
    if (prio != OS_PRIO_MUTEX_CEIL_DIS) {
        /*@
            0 <= prio_in && prio_in < 64 &&
            coq_prop(mutex_create_priority_input_prop(
              prio, prio_in)) *
            store_priotbl_list(sg, prioL_in) *
            coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl))
            which implies
            coq_prop(mutex_create_priority_input_prop(
              prio, prio_in)) *
            data_at(&OSTCBPrioTbl[prio],
                    Znth(prio_in, prioL_in, 0)) *
            store_priotbl_list_missing_i(sg, prioL_in, prio_in) *
            coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl))
        */
        if (OSTCBPrioTbl[prio] != (OS_TCB *)0) {
            /*@
                0 <= prio_in && prio_in < 64 &&
                coq_prop(mutex_create_priority_input_prop(
                  prio, prio_in)) *
                data_at(&OSTCBPrioTbl[prio],
                        Znth(prio_in, prioL_in, 0)) *
                store_priotbl_list_missing_i(sg, prioL_in, prio_in) *
                coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl))
                which implies
                coq_prop(mutex_create_priority_input_prop(
                  prio, prio_in)) *
                store_priotbl_list(sg, prioL_in) *
                coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl))
            */
            /*@ exists (ls1: UCOS2_Verify_State),
                  InsideCritical(sg, ls1) *
                  mutex_create_head_open_inv(sg, ls1) *
                  store_priotbl_list(sg, prioL_in) *
                  data_at(&OSEventFreeList, struct os_event *, freelist_in) *
                  coq_prop(crit_rel_no_os_state_change(ls0, ls1)) *
                  coq_prop(prio_tbl_list_rel(
                    sg, ls1.TskState, prioL_in)) *
                  coq_prop(event_free_list_head_prop(
                    sg, ls1.EventState, freelist_in)) *
                  coq_prop(os_event_free_list_addr(
                    sg, &OSEventFreeList))
                which implies
                exists (ls1: UCOS2_Verify_State),
                  InsideCritical(sg, ls1) *
                  mutex_create_restore_frame(
                    sg, ls0, prio_in, eid, free_rest,
                    prioL_in, false) *
                  coq_prop(crit_rel_no_os_state_change(ls0, ls1)) *
                  coq_prop(prio_tbl_list_rel(
                    sg, ls0.TskState, prioL_in)) *
                  coq_prop(os_event_free_list_addr(
                    sg, &OSEventFreeList))
            */
            OS_CPU_SR_Restore(cpu_sr)/*@ where sg = sg, ls0 = ls0,
                pcp = prio_in, eid = eid, rest = free_rest,
                prio_before = prioL_in, success = false */;
            /*@ exists (ls_inside_post: UCOS2_Verify_State)
                       (ls_post: UCOS2_Verify_State),
                  coq_prop(mutex_create_restore_transition_prop(
                    sg, ls0, ls_inside_post, ls_post,
                    prio_in, eid, free_rest, false)) &&
                  OutsideCritical(sg, ls_post) *
                  mutex_create_restore_frame(
                    sg, ls0, prio_in, eid, free_rest,
                    prioL_in, false) *
                  coq_prop(prio_tbl_list_rel(
                    sg, ls0.TskState, prioL_in))
                which implies
                OutsideCritical(sg, ls0) *
                UCOS2_Verify_inv(sg, ls0) *
                coq_prop(prio_tbl_list_rel(
                  sg, ls0.TskState, prioL_in))
            */
           *perr = OS_ERR_PRIO_EXIST;
            return ((OS_EVENT *)0);
        }
        OSTCBPrioTbl[prio] = (OS_TCB *)1;
        /*@
            0 <= prio_in && prio_in < 64 &&
            coq_prop(mutex_create_priority_input_prop(
              prio, prio_in)) *
            data_at(&OSTCBPrioTbl[prio], 1) *
            store_priotbl_list_missing_i(sg, prioL_in, prio_in) *
            coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl))
            which implies
            coq_prop(mutex_create_priority_input_prop(
              prio, prio_in)) *
            store_priotbl_list(
              sg, replace_Znth(prio_in, 1, prioL_in)) *
            coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl))
        */
    }

    /*@ Branch name
        enabled_empty:
          prio_in != 255 && freelist_in == 0;
        enabled_nonempty:
          prio_in != 255 && freelist_in != 0;
        disabled_empty:
          prio_in == 255 && freelist_in == 0;
        disabled_nonempty:
          prio_in == 255 && freelist_in != 0
    */
    /*@ prio_in != 255 &&
        0 <= prio_in && prio_in < 63 &&
        Znth(prio_in, prioL_in, 0) == 0 &&
        coq_prop(valid_stable_glob_vars(sg)) *
        store_priotbl_list(
          sg, replace_Znth(prio_in, 1, prioL_in))
        $ enabled_empty enabled_nonempty
        which implies
        prio_in != 255 &&
        0 <= prio_in && prio_in < 64 &&
        coq_prop(valid_stable_glob_vars(sg)) *
        coq_prop(valid_mutex_pcp(sg, prio_in)) *
        coq_prop(mutex_create_pcp_slot_available_prop(
          sg, prio_in, prioL_in)) *
        store_priotbl_list(
          sg, mutex_create_priotbl_after(
                sg, prio_in, prioL_in))
        $ enabled_empty enabled_nonempty
    */
    /*@ prio_in == 255 &&
        coq_prop(valid_stable_glob_vars(sg)) *
        store_priotbl_list(sg, prioL_in)
        $ disabled_empty disabled_nonempty
        which implies
        prio_in == 255 &&
        coq_prop(valid_stable_glob_vars(sg)) *
        coq_prop(valid_mutex_pcp(sg, prio_in)) *
        coq_prop(mutex_create_pcp_slot_available_prop(
          sg, prio_in, prioL_in)) *
        store_priotbl_list(
          sg, mutex_create_priotbl_after(
                sg, prio_in, prioL_in))
        $ disabled_empty disabled_nonempty
    */
    /*@
        exists (ls1: UCOS2_Verify_State) (cpu_sr_v: Z),
          safeExec(LastSeen(ls0),
                   bind(atomic_cmd(OSMutexCreate_sem(sg, prio_in)),
                        observe_mutex_create_ptr(sg)), X) &&
          RTrans_C(sg, ls0, sg, ls1) &&
          InsideCritical(sg, ls1) &&
          mutex_create_head_open_inv(sg, ls1) &&
          store_priotbl_list(
            sg, mutex_create_priotbl_after(
                  sg, prio_in, prioL_in)) &&
          data_at(&OSEventFreeList, struct os_event *, freelist_in) &&
          data_at(&cpu_sr, unsigned int, cpu_sr_v) &&
          data_at(&pevent, struct os_event *, 0) &&
          coq_prop(mutex_create_priority_input_prop(
            prio, prio_in)) &&
          perr == pd &&
          0 <= prio_in && prio_in <= 255 &&
          isr == intNesting(ls0.IntrState) &&
          0 <= isr && isr <= 255 &&
          isr <= 0 &&
          data_at(pd, unsigned char, perr_in) &&
          pd != 0 &&
          coq_prop(crit_rel_no_os_state_change(ls0, ls1)) &&
          coq_prop(prio_tbl_list_rel(
            sg, ls1.TskState, prioL_in)) &&
          coq_prop(event_free_list_head_prop(
            sg, ls1.EventState, freelist_in)) &&
          coq_prop(valid_stable_glob_vars(sg)) &&
          coq_prop(valid_mutex_pcp(sg, prio_in)) &&
          coq_prop(mutex_create_pcp_slot_available_prop(
            sg, prio_in, prioL_in)) &&
          coq_prop(mutex_create_free_snapshot_prop(
            sg, ls0, eid, free_rest, freelist_in, next_in)) &&
          coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl))
    */

    pevent = OSEventFreeList;
    if (pevent == (OS_EVENT *)0) {
        if (prio != OS_PRIO_MUTEX_CEIL_DIS) {
            /*@
                0 <= prio_in && prio_in < 64 &&
                prio_in != OS_PRIO_MUTEX_CEIL_DIS &&
                coq_prop(mutex_create_priority_input_prop(
                  prio, prio_in)) *
                store_priotbl_list(
                  sg, mutex_create_priotbl_after(
                        sg, prio_in, prioL_in)) *
                coq_prop(valid_stable_glob_vars(sg)) *
                coq_prop(mutex_create_pcp_slot_available_prop(
                  sg, prio_in, prioL_in)) *
                coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl))
                which implies
                coq_prop(mutex_create_priority_input_prop(
                  prio, prio_in)) *
                data_at(&OSTCBPrioTbl[prio], 1) *
                store_priotbl_list_missing_i(
                  sg,
                  mutex_create_priotbl_after(
                    sg, prio_in, prioL_in),
                  prio_in) *
                coq_prop(valid_stable_glob_vars(sg)) *
                coq_prop(mutex_create_pcp_slot_available_prop(
                  sg, prio_in, prioL_in)) *
                coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl))
            */
            OSTCBPrioTbl[prio] = (OS_TCB *)0;
            /*@
                0 <= prio_in && prio_in < 64 &&
                prio_in != OS_PRIO_MUTEX_CEIL_DIS &&
                coq_prop(mutex_create_priority_input_prop(
                  prio, prio_in)) *
                data_at(&OSTCBPrioTbl[prio], 0) *
                store_priotbl_list_missing_i(
                  sg,
                  mutex_create_priotbl_after(
                    sg, prio_in, prioL_in),
                  prio_in) *
                coq_prop(valid_stable_glob_vars(sg)) *
                coq_prop(mutex_create_pcp_slot_available_prop(
                  sg, prio_in, prioL_in)) *
                coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl))
                which implies
                coq_prop(mutex_create_priority_input_prop(
                  prio, prio_in)) *
                store_priotbl_list(sg, prioL_in) *
                coq_prop(valid_stable_glob_vars(sg)) *
                coq_prop(mutex_create_pcp_slot_available_prop(
                  sg, prio_in, prioL_in)) *
                coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl))
            */
        }
        /*@ Branch name
            enabled_empty: prio_in != 255;
            disabled_empty: prio_in == 255
        */
        /*@ prio_in == 255 &&
            store_priotbl_list(
              sg, mutex_create_priotbl_after(
                    sg, prio_in, prioL_in))
            $ disabled_empty
            which implies
            store_priotbl_list(sg, prioL_in)
            $ disabled_empty
        */
        /*@
            exists (ls1: UCOS2_Verify_State) (cpu_sr_v: Z),
              safeExec(LastSeen(ls0),
                       bind(atomic_cmd(OSMutexCreate_sem(sg, prio_in)),
                            observe_mutex_create_ptr(sg)), X) &&
              RTrans_C(sg, ls0, sg, ls1) &&
              InsideCritical(sg, ls1) &&
              mutex_create_head_open_inv(sg, ls1) &&
              store_priotbl_list(sg, prioL_in) &&
              data_at(&OSEventFreeList,
                      struct os_event *, freelist_in) &&
              data_at(&cpu_sr, unsigned int, cpu_sr_v) &&
              data_at(&pevent, struct os_event *, 0) &&
              coq_prop(mutex_create_priority_input_prop(
                prio, prio_in)) &&
              perr == pd &&
              0 <= prio_in && prio_in <= 255 &&
              isr == intNesting(ls0.IntrState) &&
              0 <= isr && isr <= 255 &&
              isr <= 0 &&
              freelist_in == 0 &&
              data_at(pd, unsigned char, perr_in) &&
              pd != 0 &&
              coq_prop(crit_rel_no_os_state_change(ls0, ls1)) &&
              coq_prop(prio_tbl_list_rel(
                sg, ls1.TskState, prioL_in)) &&
              coq_prop(event_free_list_head_prop(
                sg, ls1.EventState, freelist_in)) &&
              coq_prop(valid_stable_glob_vars(sg)) &&
              coq_prop(valid_mutex_pcp(sg, prio_in)) &&
              coq_prop(mutex_create_pcp_slot_available_prop(
                sg, prio_in, prioL_in)) &&
              coq_prop(mutex_create_free_snapshot_prop(
                sg, ls0, eid, free_rest,
                freelist_in, next_in)) &&
              coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
              coq_prop(os_event_free_list_addr(
                sg, &OSEventFreeList)) &&
              coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl))
        */
        /*@ exists (ls1: UCOS2_Verify_State),
              InsideCritical(sg, ls1) *
              mutex_create_head_open_inv(sg, ls1) *
              store_priotbl_list(sg, prioL_in) *
              data_at(&OSEventFreeList, struct os_event *, freelist_in) *
              coq_prop(crit_rel_no_os_state_change(ls0, ls1)) *
              coq_prop(prio_tbl_list_rel(
                sg, ls1.TskState, prioL_in)) *
              coq_prop(event_free_list_head_prop(
                sg, ls1.EventState, freelist_in)) *
              coq_prop(os_event_free_list_addr(
                sg, &OSEventFreeList))
            which implies
            exists (ls1: UCOS2_Verify_State),
              InsideCritical(sg, ls1) *
              mutex_create_restore_frame(
                sg, ls0, prio_in, eid, free_rest,
                prioL_in, false) *
              coq_prop(crit_rel_no_os_state_change(ls0, ls1)) *
              coq_prop(os_event_free_list_addr(
                sg, &OSEventFreeList))
        */
        OS_CPU_SR_Restore(cpu_sr)/*@ where sg = sg, ls0 = ls0,
            pcp = prio_in, eid = eid, rest = free_rest,
            prio_before = prioL_in, success = false */;
        /*@ exists (ls_inside_post: UCOS2_Verify_State)
                   (ls_post: UCOS2_Verify_State),
              coq_prop(mutex_create_restore_transition_prop(
                sg, ls0, ls_inside_post, ls_post,
                prio_in, eid, free_rest, false)) &&
              OutsideCritical(sg, ls_post) *
              mutex_create_restore_frame(
                sg, ls0, prio_in, eid, free_rest,
                prioL_in, false)
            which implies
            OutsideCritical(sg, ls0) *
            UCOS2_Verify_inv(sg, ls0)
        */
       *perr = OS_ERR_PEVENT_NULL;
        return (pevent);
    }
    /*@ freelist_in != 0 &&
        coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)freelist_in)->OSEventType,
          &((OS_EVENT *)freelist_in)->OSEventPtr,
          &((OS_EVENT *)freelist_in)->OSEventCnt)) &&
        exists (ls1: UCOS2_Verify_State),
          InsideCritical(sg, ls1) *
          mutex_create_head_open_inv(sg, ls1) *
          coq_prop(crit_rel_no_os_state_change(ls0, ls1)) *
          coq_prop(prio_tbl_list_rel(
            sg, ls1.TskState, prioL_in)) *
          coq_prop(mutex_create_free_snapshot_prop(
            sg, ls0, eid, free_rest, freelist_in, next_in))
        which implies
        freelist_in != 0 &&
        coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)freelist_in)->OSEventType,
          &((OS_EVENT *)freelist_in)->OSEventPtr,
          &((OS_EVENT *)freelist_in)->OSEventCnt)) &&
        exists (ls1: UCOS2_Verify_State),
          InsideCritical(sg, ls1) *
          mutex_create_node_open_inv(sg, ls1, free_rest) *
          data_at(&((OS_EVENT *)freelist_in)->OSEventPtr,
                  void *, next_in) *
          mutex_create_unused_event_no_ptr(freelist_in) *
          coq_prop(crit_rel_no_os_state_change(ls0, ls1)) *
          coq_prop(prio_tbl_list_rel(
            sg, ls1.TskState, prioL_in)) *
          coq_prop(event_free_head_snapshot_prop(
            sg, ls0.EventState, eid, free_rest,
            freelist_in, next_in)) *
          coq_prop(task_event_id_unreferenced_prop(
            ls0, eid)) *
          coq_prop(valid_event_id(sg, eid))
    */
    OSEventFreeList = (OS_EVENT *)pevent->OSEventPtr;
    /*@ coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)freelist_in)->OSEventType,
          &((OS_EVENT *)freelist_in)->OSEventPtr,
          &((OS_EVENT *)freelist_in)->OSEventCnt)) &&
        data_at(&((OS_EVENT *)freelist_in)->OSEventPtr,
                void *, next_in) *
        mutex_create_unused_event_no_ptr(freelist_in) *
        coq_prop(event_free_head_snapshot_prop(
          sg, ls0.EventState, eid, free_rest,
          freelist_in, next_in))
        which implies
        coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)freelist_in)->OSEventType,
          &((OS_EVENT *)freelist_in)->OSEventPtr,
          &((OS_EVENT *)freelist_in)->OSEventCnt)) &&
        unused_complete_event(sg, freelist_in, eid) *
        coq_prop(event_free_head_snapshot_prop(
          sg, ls0.EventState, eid, free_rest,
          freelist_in, next_in))
    */
    /*@ coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)freelist_in)->OSEventType,
          &((OS_EVENT *)freelist_in)->OSEventPtr,
          &((OS_EVENT *)freelist_in)->OSEventCnt)) &&
        exists (ls1: UCOS2_Verify_State),
          InsideCritical(sg, ls1) *
          mutex_create_node_open_inv(sg, ls1, free_rest) *
          store_priotbl_list(
            sg, mutex_create_priotbl_after(
                  sg, prio_in, prioL_in)) *
          data_at(&OSEventFreeList, struct os_event *, next_in) *
          unused_complete_event(sg, freelist_in, eid) *
          coq_prop(crit_rel_no_os_state_change(ls0, ls1)) *
          coq_prop(prio_tbl_list_rel(
            sg, ls1.TskState, prioL_in)) *
          coq_prop(event_free_head_snapshot_prop(
            sg, ls0.EventState, eid, free_rest,
            freelist_in, next_in)) *
          coq_prop(task_event_id_unreferenced_prop(
            ls0, eid)) *
          coq_prop(valid_stable_glob_vars(sg)) *
          coq_prop(valid_mutex_pcp(sg, prio_in)) *
          coq_prop(valid_event_id(sg, eid)) *
          coq_prop(mutex_create_pcp_slot_available_prop(
            sg, prio_in, prioL_in)) *
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList))
        which implies
        coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)freelist_in)->OSEventType,
          &((OS_EVENT *)freelist_in)->OSEventPtr,
          &((OS_EVENT *)freelist_in)->OSEventCnt)) &&
        exists (ls1: UCOS2_Verify_State),
          InsideCritical(sg, ls1) *
          mutex_create_restore_frame(
            sg, ls0, prio_in, eid, free_rest,
            prioL_in, true) *
          coq_prop(crit_rel_no_os_state_change(ls0, ls1)) *
          coq_prop(event_free_head_snapshot_prop(
            sg, ls0.EventState, eid, free_rest,
            freelist_in, next_in)) *
          coq_prop(task_event_id_unreferenced_prop(
            ls0, eid)) *
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList))
    */
    OS_CPU_SR_Restore(cpu_sr)/*@ where sg = sg, ls0 = ls0,
        pcp = prio_in, eid = eid, rest = free_rest,
        prio_before = prioL_in, success = true */;
    /*@ coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)freelist_in)->OSEventType,
          &((OS_EVENT *)freelist_in)->OSEventPtr,
          &((OS_EVENT *)freelist_in)->OSEventCnt)) &&
        exists (ls_inside_post: UCOS2_Verify_State)
               (ls_post: UCOS2_Verify_State),
          OutsideCritical(sg, ls_post) *
          mutex_create_restore_frame(
            sg, ls0, prio_in, eid, free_rest,
            prioL_in, true) *
          coq_prop(mutex_create_restore_transition_prop(
            sg, ls0, ls_inside_post, ls_post,
            prio_in, eid, free_rest, true)) *
          coq_prop(event_free_head_snapshot_prop(
            sg, ls0.EventState, eid, free_rest,
            freelist_in, next_in)) *
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList))
        which implies
        coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)freelist_in)->OSEventType,
          &((OS_EVENT *)freelist_in)->OSEventPtr,
          &((OS_EVENT *)freelist_in)->OSEventCnt)) &&
        exists (ls_post: UCOS2_Verify_State),
          OutsideCritical(sg, ls_post) *
          mutex_create_node_open_inv(sg, ls0, free_rest) *
          store_priotbl_list(
            sg, mutex_create_priotbl_after(
                  sg, prio_in, prioL_in)) *
          data_at(&OSEventFreeList, struct os_event *, next_in) *
          unused_complete_event(sg, freelist_in, eid) *
          coq_prop(mutex_create_success_transition_prop(
            sg, ls0, ls_post, prio_in, eid, free_rest)) *
          coq_prop(event_free_head_snapshot_prop(
            sg, ls0.EventState, eid, free_rest,
            freelist_in, next_in)) *
          coq_prop(valid_stable_glob_vars(sg)) *
          coq_prop(valid_mutex_pcp(sg, prio_in)) *
          coq_prop(valid_event_id(sg, eid)) *
          coq_prop(prio_tbl_list_rel(
            sg, ls0.TskState, prioL_in)) *
          coq_prop(mutex_create_pcp_slot_available_prop(
            sg, prio_in, prioL_in)) *
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList))
    */
    /*@ coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)freelist_in)->OSEventType,
          &((OS_EVENT *)freelist_in)->OSEventPtr,
          &((OS_EVENT *)freelist_in)->OSEventCnt)) &&
        exists (ls_post: UCOS2_Verify_State),
          OutsideCritical(sg, ls_post) *
          coq_prop(mutex_create_success_transition_prop(
            sg, ls0, ls_post, prio_in, eid, free_rest)) *
          unused_complete_event(sg, freelist_in, eid) *
          coq_prop(event_free_head_snapshot_prop(
            sg, ls0.EventState, eid, free_rest,
            freelist_in, next_in))
        which implies
        coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)freelist_in)->OSEventType,
          &((OS_EVENT *)freelist_in)->OSEventPtr,
          &((OS_EVENT *)freelist_in)->OSEventCnt)) &&
        exists (ls_post: UCOS2_Verify_State),
          OutsideCritical(sg, ls_post) *
          coq_prop(mutex_create_success_transition_prop(
            sg, ls0, ls_post, prio_in, eid, free_rest)) *
          data_at(&((OS_EVENT *)freelist_in)->OSEventType,
                  unsigned char, 0) *
          undef_data_at(&((OS_EVENT *)freelist_in)->OSEventPtr,
                        void *) *
          undef_data_at(&((OS_EVENT *)freelist_in)->OSEventCnt,
                        unsigned short) *
          mutex_create_wait_table_uninitialized(freelist_in) *
          coq_prop(event_free_head_snapshot_prop(
              sg, ls0.EventState, eid, free_rest,
              freelist_in, next_in))
    */

    pevent->OSEventType = OS_EVENT_TYPE_MUTEX;
    pevent->OSEventCnt  = (INT16U)((INT16U)prio << 8u) | OS_MUTEX_AVAILABLE;
    pevent->OSEventPtr  = (void *)0;

    OS_EventWaitListInit(pevent);

    /*@ coq_prop(event_core_fields_layout_prop(
          sg, eid,
          &((OS_EVENT *)freelist_in)->OSEventType,
          &((OS_EVENT *)freelist_in)->OSEventPtr,
          &((OS_EVENT *)freelist_in)->OSEventCnt)) &&
        exists (ls_post: UCOS2_Verify_State),
          OutsideCritical(sg, ls_post) *
          data_at(&((OS_EVENT *)freelist_in)->OSEventType,
                  unsigned char, 4) *
          data_at(&((OS_EVENT *)freelist_in)->OSEventPtr,
                  void *, 0) *
          data_at(&((OS_EVENT *)freelist_in)->OSEventCnt,
                  unsigned short, prio_in * 256 + 255) *
          mutex_create_wait_table_zero(freelist_in) *
          coq_prop(mutex_create_success_transition_prop(
            sg, ls0, ls_post, prio_in, eid, free_rest)) *
          coq_prop(event_free_head_snapshot_prop(
            sg, ls0.EventState, eid, free_rest,
            freelist_in, next_in))
        which implies
        exists (ls_post: UCOS2_Verify_State),
          OutsideCritical(sg, ls_post) *
          mutex_create_initialized_event(
            sg, ls_post, prio_in, eid) *
          coq_prop(mutex_create_success_transition_prop(
            sg, ls0, ls_post, prio_in, eid, free_rest)) *
          coq_prop(event_free_head_snapshot_prop(
            sg, ls0.EventState, eid, free_rest,
            freelist_in, next_in))
    */
    /*@ exists (ls_post: UCOS2_Verify_State),
          OutsideCritical(sg, ls_post) *
          mutex_create_node_open_inv(sg, ls0, free_rest) *
          store_priotbl_list(
            sg, mutex_create_priotbl_after(
                  sg, prio_in, prioL_in)) *
          data_at(&OSEventFreeList, struct os_event *, next_in) *
          mutex_create_initialized_event(
            sg, ls_post, prio_in, eid) *
          coq_prop(mutex_create_success_transition_prop(
            sg, ls0, ls_post, prio_in, eid, free_rest)) *
          coq_prop(event_free_head_snapshot_prop(
            sg, ls0.EventState, eid, free_rest,
            freelist_in, next_in)) *
          coq_prop(valid_stable_glob_vars(sg)) *
          coq_prop(valid_mutex_pcp(sg, prio_in)) *
          coq_prop(valid_event_id(sg, eid)) *
          coq_prop(prio_tbl_list_rel(
            sg, ls0.TskState, prioL_in)) *
          coq_prop(mutex_create_pcp_slot_available_prop(
            sg, prio_in, prioL_in)) *
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList))
        which implies
        exists (ls_post: UCOS2_Verify_State),
          OutsideCritical(sg, ls_post) *
          UCOS2_Verify_inv(sg, ls_post) *
          coq_prop(mutex_create_success_transition_prop(
            sg, ls0, ls_post, prio_in, eid, free_rest)) *
          coq_prop(event_free_head_snapshot_prop(
            sg, ls0.EventState, eid, free_rest,
            freelist_in, next_in)) *
          coq_prop(valid_stable_glob_vars(sg)) *
          coq_prop(valid_mutex_pcp(sg, prio_in)) *
          coq_prop(valid_event_id(sg, eid)) *
          coq_prop(prio_tbl_list_rel(
            sg, ls0.TskState, prioL_in)) *
          coq_prop(mutex_create_pcp_slot_available_prop(
            sg, prio_in, prioL_in)) *
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList))
    */
    /*@
        exists (ls_post: UCOS2_Verify_State)
               (cpu_sr_v: Z) (perr_v: Z),
          safeExec(LastSeen(ls_post), return(freelist_in), X) &&
          data_at(&cpu_sr, unsigned int, cpu_sr_v) &&
          data_at(&pevent, struct os_event *, freelist_in) &&
          coq_prop(mutex_create_priority_input_prop(
            prio, prio_in)) &&
          perr == pd &&
          0 <= prio_in && prio_in <= 255 &&
          isr == intNesting(ls0.IntrState) &&
          0 <= isr && isr <= 255 &&
          isr <= 0 &&
          freelist_in != 0 &&
          freelist_in == event_addr(sg, eid) &&
          next_in == free_event_head(sg, free_rest) &&
          data_at(pd, unsigned char, perr_v) &&
          pd != 0 &&
          OutsideCritical(sg, ls_post) &&
          UCOS2_Verify_inv(sg, ls_post) &&
          coq_prop(mutex_create_success_transition_prop(
            sg, ls0, ls_post, prio_in, eid, free_rest)) &&
          coq_prop(event_free_head_snapshot_prop(
            sg, ls0.EventState, eid, free_rest,
            freelist_in, next_in)) &&
          coq_prop(valid_stable_glob_vars(sg)) &&
          coq_prop(valid_mutex_pcp(sg, prio_in)) &&
          coq_prop(valid_event_id(sg, eid)) &&
          coq_prop(prio_tbl_list_rel(
            sg, ls0.TskState, prioL_in)) &&
          coq_prop(mutex_create_pcp_slot_available_prop(
            sg, prio_in, prioL_in))
    */

    *perr = OS_ERR_NONE;
    return pevent;
}
