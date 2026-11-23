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

/*@ Extern Coq (tcb_addr : StableGlobVars -> TaskID -> addr) */
/*@ Extern Coq (coq_prop : Prop -> Assertion) */
/*@ Extern Coq (valid_stable_glob_vars : StableGlobVars -> Prop) */
/*@ Extern Coq (valid_priority_index : StableGlobVars -> Priority -> Prop) */
/*@ Extern Coq (os_rdy_grp_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_rdy_tbl_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_prio_cur_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_tcb_cur_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (os_tcb_prio_tbl_addr : StableGlobVars -> addr -> Prop) */
/*@ Extern Coq (UCOS2_Verify_inv : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (InsideCritical : StableGlobVars -> UCOS2_Verify_State -> Assertion) */
/*@ Extern Coq (atomic_cmd : {A} -> program UCOS2_Verify_State A -> program (UCOS2_Verify_State -> Prop) A) */
/*@ Extern Coq (observe_unit_void : unit -> program (UCOS2_Verify_State -> Prop) unit) */
/*@ Extern Coq (OSMutex_RdyAtPrio_sem : StableGlobVars -> addr -> Priority -> program UCOS2_Verify_State unit) */
/*@ Extern Coq (OSMutex_RdyAtPrio_guarantee : StableGlobVars -> addr -> Priority -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (OSMutex_RdyAtPrio_LastSeen : StableGlobVars -> addr -> Priority -> UCOS2_Verify_State -> UCOS2_Verify_State -> (UCOS2_Verify_State -> Prop) -> Prop) */
/*@ Extern Coq (OSMutex_RdyAtPrio_atomic_cmd : StableGlobVars -> UCOS2_Verify_State -> addr -> Priority -> program (UCOS2_Verify_State -> Prop) unit) */
/*@ Extern Coq (OSMutex_RdyAtPrio_raw_stage : StableGlobVars -> UCOS2_Verify_State -> TaskID -> TaskAbstractState -> Z -> Z -> Z -> Z -> Z -> Z -> list Z -> list addr -> Assertion) */
/*@ Extern Coq (OSMutex_RdyAtPrio_conditional_ready_snapshot : StableGlobVars -> UCOS2_Verify_State -> TaskID -> TaskAbstractState -> Priority -> UCOS2_Verify_State -> Z -> list Z -> Prop) */
/*@ Extern Coq (OSMutex_RdyAtPrio_conditional_preservation : StableGlobVars -> UCOS2_Verify_State -> TaskID -> TaskAbstractState -> Priority -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (OSMutex_RdyAtPrio_conditional_cross : StableGlobVars -> UCOS2_Verify_State -> EventID -> TaskID -> TaskAbstractState -> Priority -> UCOS2_Verify_State -> Prop) */
/*@ Extern Coq (ready_owner_relocation_domain : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> TaskID -> TaskAbstractState -> Priority -> Prop) */
/*@ Extern Coq (LastSeen : UCOS2_Verify_State -> (UCOS2_Verify_State -> Prop) -> Prop) */

/*@ Extern Coq (OS_TRUE  : Z) */
/*@ Extern Coq (OS_FALSE : Z) */

/*@ Extern Coq (store_osrdytbl : StableGlobVars -> list Z -> Assertion) */
/*@ Extern Coq (store_osrdytbl_missing_i : StableGlobVars -> list Z -> Z -> Assertion) */
/*@ Extern Coq (store_priotbl_list : StableGlobVars -> list addr -> Assertion) */
/*@ Extern Coq (store_priotbl_list_missing_i : StableGlobVars -> list addr -> Z -> Assertion) */
/*@ Extern Coq (osrdytbl_list_rel : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> list Z -> Prop) */
/*@ Extern Coq (prio_tbl_list_rel : StableGlobVars -> Glob_TaskAbstractState -> list addr -> Prop) */
/*@ Extern Coq (task_rdy_snapshot_of_prop : StableGlobVars -> Glob_TaskAbstractState -> TaskID -> TaskAbstractState -> Z -> Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (task_priority_fields_layout_prop : addr -> addr -> addr -> addr -> addr -> addr -> Prop) */
/*@ Extern Coq (used_task_rdy_rest : StableGlobVars -> addr -> TaskID -> TaskAbstractState -> Assertion) */
/*@ Extern Coq (task_inv_no_tid_priotbl : StableGlobVars -> Glob_TaskAbstractState -> TaskID -> Assertion) */
/*@ Extern Coq (sched_ready_prio_snapshot_prop : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> Z -> list Z -> Z -> Prop) */
/*@ Extern Coq (sched_tcb_cur_snapshot_prop : StableGlobVars -> SchedAbstractState -> addr -> Prop) */
/*@ Extern Coq (ready_group_after_relocation : Z -> Z -> Z -> Z -> Z) */
/*@ Extern Coq (sched_inv_rest_ready_prio : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> Assertion) */
/*@ Extern Coq (sched_inv_rest_ready_current : StableGlobVars -> Glob_TaskAbstractState -> SchedAbstractState -> Assertion) */
/*@ Extern Coq (interrupt_inv : StableGlobVars -> Glob_InterruptAbstractState -> Assertion) */
/*@ Extern Coq (event_inv : StableGlobVars -> Glob_TaskAbstractState -> Glob_EventAbstractState -> Assertion) */
/*@ Extern Coq (tick_inv : StableGlobVars -> TickAbstractState -> Assertion) */
/*@ Extern Coq (cross_module_consistency : StableGlobVars -> UCOS2_Verify_State -> Prop) */

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
/*@ Import Coq Require Import Ucos2Verify.lib.atomic_ops_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_rules_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_verify_inv */
/*@ Import Coq Require Import Ucos2Verify.lib.mutex_rdyatprio_spec */
/*@ Import Coq Require Import Ucos2Verify.lib.array_abstraction */

typedef unsigned char  INT8U;
typedef unsigned int   INT32U;
typedef unsigned short INT16U;
typedef unsigned char  OS_PRIO;

struct os_tcb;
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

extern  OS_PRIO  OSRdyGrp;
extern  OS_PRIO  OSRdyTbl[8];
extern  INT8U    OSPrioCur;
extern  OS_TCB  *OSTCBCur;
extern  OS_TCB  *OSTCBPrioTbl[64];

/* ============================================================ */
/* OSMutex_RdyAtPrio_full: µC/OS-II os_mutex.c 字面实现.        */
/*                                                              */
/* 目标(纯 list + 字面变下标):                                  */
/*   - PRE/POST 数组资源只用 list 谓词,不罗列 cell              */
/*   - body 还原源码字面 OSRdyTbl[y] / OSTCBPrioTbl[prio]       */
/*   - 不用 8 路 if-else 常量展开                                */
/*   - 不用 helper 包装                                          */
/*                                                              */
/* 字面 body 中的关键变下标/全局访问点(共 4 处):                */
/*   (1) OSRdyTbl[y] &= ~ptcb->OSTCBBitX  (清旧位)              */
/*   (2) OSRdyTbl[ptcb->OSTCBY] |= bitX   (置新位)              */
/*   (3) OSTCBCur                           (判定 current owner) */
/*   (4) OSTCBPrioTbl[prio] = ptcb         (登记优先级)         */
/*                                                              */
/* which implies 在每个变下标点把整体 list 拆为 missing_i + cell.*/
/* ============================================================ */
void  OSMutex_RdyAtPrio_full (OS_TCB *ptcb, INT8U prio)
/*@ With (sg: StableGlobVars) (ls0: UCOS2_Verify_State) X
           (restore_mid: EventID)
           (tid: TaskID) (old_t: TaskAbstractState) (pt: addr) (prio_in: Z)
           (tcbcur_in: addr)
           (tcb_prio_in: Z) (tcb_y_in: Z) (tcb_x_in: Z) (tcb_bity_in: Z) (tcb_bitx_in: Z)
           (rdy_grp_in: Z) (prio_cur_in: Z)
           (rdyL_in: list Z) (prioL_in: list addr)
           (rdyL_out: list Z) (prioL_out: list addr)
           (rdy_tbl_y_in: Z) (rdy_tbl_y_out: Z)
           (rdy_tbl_new_y_in: Z) (rdy_tbl_new_y_out: Z)
           (rdy_grp_out: Z)
           (tcb_y_out: Z) (tcb_x_out: Z) (tcb_bity_out: Z) (tcb_bitx_out: Z)
    Require
        prio == prio_in &&
        coq_prop(valid_priority_index(sg, prio_in)) &&
        pt == ptcb &&
        pt != 0 &&
        coq_prop(os_rdy_grp_addr(sg, &OSRdyGrp)) &&
        coq_prop(os_rdy_tbl_addr(sg, OSRdyTbl)) &&
        coq_prop(os_prio_cur_addr(sg, &OSPrioCur)) &&
        coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) &&
        coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
        safeExec(LastSeen(ls0),
                 bind(OSMutex_RdyAtPrio_atomic_cmd(sg, ls0, ptcb, prio),
                      observe_unit_void), X) &&
        InsideCritical(sg, ls0) &&
        UCOS2_Verify_inv(sg, ls0) &&
        coq_prop(valid_stable_glob_vars(sg)) &&
        coq_prop(task_rdy_snapshot_of_prop(sg, ls0.TskState, tid, old_t,
                                           pt, tcb_prio_in, tcb_x_in,
                                           tcb_y_in, tcb_bitx_in,
                                           tcb_bity_in)) &&
        coq_prop(task_priority_fields_layout_prop(
          pt,
          &((OS_TCB *)pt)->OSTCBPrio,
          &((OS_TCB *)pt)->OSTCBX,
          &((OS_TCB *)pt)->OSTCBY,
          &((OS_TCB *)pt)->OSTCBBitX,
          &((OS_TCB *)pt)->OSTCBBitY)) &&
        coq_prop(ready_owner_relocation_domain(sg, ls0.TskState,
                                               ls0.SchedState, tid, old_t,
                                               prio_in)) &&
        coq_prop(sched_ready_prio_snapshot_prop(sg, ls0.TskState,
                                                ls0.SchedState, rdy_grp_in,
                                                rdyL_in, prio_cur_in)) &&
        coq_prop(sched_tcb_cur_snapshot_prop(sg, ls0.SchedState,
                                             tcbcur_in)) &&
        coq_prop(prio_tbl_list_rel(sg, ls0.TskState, prioL_in)) &&
        Znth(tcb_y_in, rdyL_in, 0) == rdy_tbl_y_in &&
        0 <= tcb_y_in && tcb_y_in < 8 &&
        tcb_y_out == ((prio_in >> 3) & 7) &&
        tcb_x_out == (prio_in & 7) &&
        tcb_bity_out == (1 << tcb_y_out) &&
        tcb_bitx_out == (1 << tcb_x_out) &&
        rdy_tbl_y_out ==
          (rdy_tbl_y_in & unsigned_last_nbits(~tcb_bitx_in, 8)) &&
        rdy_grp_out == ready_group_after_relocation(
          rdy_grp_in, rdy_tbl_y_out, tcb_bity_in, tcb_bity_out) &&
        rdy_tbl_new_y_in == Znth(tcb_y_out,
                                 replace_Znth(tcb_y_in, rdy_tbl_y_out, rdyL_in), 0) &&
        rdy_tbl_new_y_out == (rdy_tbl_new_y_in | tcb_bitx_out) &&
        rdyL_out == replace_Znth(tcb_y_out, rdy_tbl_new_y_out,
                                replace_Znth(tcb_y_in, rdy_tbl_y_out, rdyL_in)) &&
        prioL_out == replace_Znth(prio_in, pt, prioL_in)
    Ensure
        exists (ls_post: UCOS2_Verify_State) (new_t: TaskAbstractState),
        coq_prop(OSMutex_RdyAtPrio_guarantee(sg, ptcb, prio,
                                              ls0, ls_post)) &&
        safeExec(OSMutex_RdyAtPrio_LastSeen(sg, ptcb, prio,
                                             ls0, ls_post),
                 return(tt), X) &&
        InsideCritical(sg, ls0) &&
        OSMutex_RdyAtPrio_raw_stage(
          sg, ls0, tid, old_t,
          prio_in, tcb_x_out, tcb_y_out, tcb_bitx_out, tcb_bity_out,
          rdy_grp_out, rdyL_out, prioL_out) &&
        coq_prop(OSMutex_RdyAtPrio_conditional_ready_snapshot(
          sg, ls0, tid, old_t, prio_in, ls_post, rdy_grp_out, rdyL_out)) &&
        coq_prop(OSMutex_RdyAtPrio_conditional_preservation(
          sg, ls0, tid, old_t, prio_in, ls_post)) &&
        coq_prop(OSMutex_RdyAtPrio_conditional_cross(
          sg, ls0, restore_mid, tid, old_t, prio_in, ls_post)) &&
        prio == prio_in && pt == ptcb &&
        coq_prop(task_rdy_snapshot_of_prop(sg, ls_post.TskState, tid, new_t,
                                           pt, prio_in, tcb_x_out,
                                           tcb_y_out, tcb_bitx_out,
                                           tcb_bity_out)) &&
        coq_prop(prio_tbl_list_rel(sg, ls_post.TskState, prioL_out)) &&
        prioL_out == replace_Znth(prio_in, pt, prioL_in)
*/
{
    INT8U  y;

    /*@ exists (ptcb_v: Z),
        ptcb_v == pt &&
        coq_prop(valid_stable_glob_vars(sg)) &&
        coq_prop(os_rdy_grp_addr(sg, &OSRdyGrp)) &&
        coq_prop(os_rdy_tbl_addr(sg, OSRdyTbl)) &&
        coq_prop(os_prio_cur_addr(sg, &OSPrioCur)) &&
        coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) &&
        coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
        coq_prop(task_rdy_snapshot_of_prop(sg, ls0.TskState, tid, old_t,
                                           pt, tcb_prio_in, tcb_x_in,
                                           tcb_y_in, tcb_bitx_in,
                                           tcb_bity_in)) &&
        coq_prop(task_priority_fields_layout_prop(
          pt,
          &((OS_TCB *)pt)->OSTCBPrio,
          &((OS_TCB *)pt)->OSTCBX,
          &((OS_TCB *)pt)->OSTCBY,
          &((OS_TCB *)pt)->OSTCBBitX,
          &((OS_TCB *)pt)->OSTCBBitY)) &&
        coq_prop(sched_ready_prio_snapshot_prop(sg, ls0.TskState,
                                                ls0.SchedState, rdy_grp_in,
                                                rdyL_in, prio_cur_in)) &&
        coq_prop(sched_tcb_cur_snapshot_prop(sg, ls0.SchedState,
                                             tcbcur_in)) &&
        coq_prop(prio_tbl_list_rel(sg, ls0.TskState, prioL_in)) &&
        data_at(&ptcb, struct os_tcb *, ptcb_v) *
        UCOS2_Verify_inv(sg, ls0)
        which implies
        data_at(&ptcb, struct os_tcb *, ptcb_v) *
        interrupt_inv(sg, ls0.IntrState) *
        data_at(&((OS_TCB *)ptcb_v)->OSTCBPrio, unsigned char, tcb_prio_in) *
        data_at(&((OS_TCB *)ptcb_v)->OSTCBX, unsigned char, tcb_x_in) *
        data_at(&((OS_TCB *)ptcb_v)->OSTCBY, unsigned char, tcb_y_in) *
        data_at(&((OS_TCB *)ptcb_v)->OSTCBBitX, unsigned char, tcb_bitx_in) *
        data_at(&((OS_TCB *)ptcb_v)->OSTCBBitY, unsigned char, tcb_bity_in) *
        used_task_rdy_rest(sg, ptcb_v, tid, old_t) *
        task_inv_no_tid_priotbl(sg, ls0.TskState, tid) *
        store_priotbl_list(sg, prioL_in) *
        data_at(&OSRdyGrp, unsigned char, rdy_grp_in) *
        store_osrdytbl(sg, rdyL_in) *
        data_at(&OSPrioCur, unsigned char, prio_cur_in) *
        data_at(&OSTCBCur, struct os_tcb *, tcbcur_in) *
        sched_inv_rest_ready_current(sg, ls0.TskState, ls0.SchedState) *
        event_inv(sg, ls0.TskState, ls0.EventState) *
        tick_inv(sg, ls0.TickState) *
        coq_prop(cross_module_consistency(sg, ls0)) *
        coq_prop(valid_stable_glob_vars(sg)) *
        coq_prop(os_rdy_grp_addr(sg, &OSRdyGrp)) *
        coq_prop(os_rdy_tbl_addr(sg, OSRdyTbl)) *
        coq_prop(os_prio_cur_addr(sg, &OSPrioCur)) *
        coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) *
        coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) *
        coq_prop(task_rdy_snapshot_of_prop(sg, ls0.TskState, tid, old_t,
                                           pt, tcb_prio_in, tcb_x_in,
                                           tcb_y_in, tcb_bitx_in,
                                           tcb_bity_in)) *
        coq_prop(task_priority_fields_layout_prop(
          pt,
          &((OS_TCB *)pt)->OSTCBPrio,
          &((OS_TCB *)pt)->OSTCBX,
          &((OS_TCB *)pt)->OSTCBY,
          &((OS_TCB *)pt)->OSTCBBitX,
          &((OS_TCB *)pt)->OSTCBBitY)) *
        coq_prop(sched_ready_prio_snapshot_prop(sg, ls0.TskState,
                                                ls0.SchedState, rdy_grp_in,
                                                rdyL_in, prio_cur_in)) *
        coq_prop(sched_tcb_cur_snapshot_prop(sg, ls0.SchedState,
                                             tcbcur_in)) *
        coq_prop(prio_tbl_list_rel(sg, ls0.TskState, prioL_in))
    */
    y            =  ptcb->OSTCBY;
    /*@ 0 <= tcb_y_in && tcb_y_in < 8 &&
        Znth(tcb_y_in, rdyL_in, 0) == rdy_tbl_y_in &&
        coq_prop(os_rdy_tbl_addr(sg, OSRdyTbl)) &&
        coq_prop(sched_ready_prio_snapshot_prop(sg, ls0.TskState,
                                                ls0.SchedState, rdy_grp_in,
                                                rdyL_in, prio_cur_in)) &&
        store_osrdytbl(sg, rdyL_in)
        which implies
        data_at(&OSRdyTbl[tcb_y_in], rdy_tbl_y_in) *
        store_osrdytbl_missing_i(sg, rdyL_in, tcb_y_in) *
        coq_prop(os_rdy_tbl_addr(sg, OSRdyTbl)) *
        coq_prop(sched_ready_prio_snapshot_prop(sg, ls0.TskState,
                                                ls0.SchedState, rdy_grp_in,
                                                rdyL_in, prio_cur_in))
    */
    OSRdyTbl[y] &= (OS_PRIO)~ptcb->OSTCBBitX;
    if (OSRdyTbl[y] == 0u) {
        OSRdyGrp &= (OS_PRIO)~ptcb->OSTCBBitY;
    }
    ptcb->OSTCBPrio         = prio;
    if (ptcb == OSTCBCur) {
        /*@ Branch name current_owner */
        OSPrioCur           = prio;
    } else {
        /*@ Branch name noncurrent_owner */
    }
    ptcb->OSTCBY            = (INT8U)((INT8U)(prio >> 3u) & 0x07u);
    ptcb->OSTCBX            = (INT8U)(prio & 0x07u);
    ptcb->OSTCBBitY         = (OS_PRIO)(1uL << ptcb->OSTCBY);
    ptcb->OSTCBBitX         = (OS_PRIO)(1uL << ptcb->OSTCBX);
    OSRdyGrp               |= ptcb->OSTCBBitY;
    /*@ 0 <= tcb_y_out && tcb_y_out < 8 &&
        rdy_tbl_new_y_in == Znth(tcb_y_out,
                                 replace_Znth(tcb_y_in, rdy_tbl_y_out,
                                              rdyL_in), 0) &&
        coq_prop(os_rdy_tbl_addr(sg, OSRdyTbl)) &&
        coq_prop(sched_ready_prio_snapshot_prop(sg, ls0.TskState,
                                                ls0.SchedState, rdy_grp_in,
                                                rdyL_in, prio_cur_in)) &&
        data_at(&ptcb->OSTCBY, tcb_y_out) *
        data_at(&OSRdyTbl[tcb_y_in], rdy_tbl_y_out) *
        store_osrdytbl_missing_i(sg, rdyL_in, tcb_y_in)
        which implies
        data_at(&ptcb->OSTCBY, tcb_y_out) *
        data_at(&OSRdyTbl[tcb_y_out], rdy_tbl_new_y_in) *
        store_osrdytbl_missing_i(sg, replace_Znth(tcb_y_in, rdy_tbl_y_out, rdyL_in), tcb_y_out) *
        coq_prop(os_rdy_tbl_addr(sg, OSRdyTbl)) *
        coq_prop(sched_ready_prio_snapshot_prop(sg, ls0.TskState,
                                                ls0.SchedState, rdy_grp_in,
                                                rdyL_in, prio_cur_in))
    */
    OSRdyTbl[ptcb->OSTCBY] |= ptcb->OSTCBBitX;
    /*@ 0 <= prio_in && prio_in < 64 && prio_in == prio &&
        coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
        coq_prop(prio_tbl_list_rel(sg, ls0.TskState, prioL_in)) &&
        store_priotbl_list(sg, prioL_in)
        which implies
        data_at(&OSTCBPrioTbl[prio], Znth(prio_in, prioL_in, 0)) *
        store_priotbl_list_missing_i(sg, prioL_in, prio_in) *
        coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) *
        coq_prop(prio_tbl_list_rel(sg, ls0.TskState, prioL_in))
    */
    OSTCBPrioTbl[prio]      = ptcb;
}
