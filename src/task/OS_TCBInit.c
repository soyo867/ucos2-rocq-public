/*
 * Native executable-source intake for OS_TCBInit, not an accepted proof.
 * Base: uC/OS-II V2.93.01, bfc6120f20cb27a927a9fc5dd667f9e455495777.
 * Profile: config/queue-v2.93.01-first-round/profile.json.
 * Variant: source_variants/task-atomic-publication/os_core.patch.
 * The selected native TCB fields and preprocessed function body are checked
 * against that patched source by tests/task_publication/check-tcb-source.py.
 * Creation hooks: task-native-v2.93.01/hook-source-binding.json, selected in
 * this controller handoff. Their contracts below describe direct C body
 * effects only; they do not suppress open-interrupt environment interference.
 * OS_TCBInit's platform/resumption contract is still a separate obligation.
 */

/*@ Import Coq Require Import Ucos2Verify.lib.stable_glob_vars */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_verify_state_def */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_rules_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.task */
/*@ Import Coq Require Import Ucos2Verify.lib.interrupt */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_verify_inv */
/*@ Import Coq Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec */
/*@ Import Coq Import TaskStateDef SchedStateDef UCOS2_C_Rules */
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq
    (StableGlobVars :: *) (UCOS2_Verify_State :: *)
    (InterruptPlatformResources :: *) (CriticalRegionResources :: *)
    (InterruptSaveToken :: *) (TaskInvocationOrigin :: *) (nat :: *)
    (TCBCommonImage :: *) (TCBLayoutImage :: *) (TCBField :: *) (TaskTCBInitArgs :: *)
*/
/*@ Extern Coq
    (interrupt_platform_running : InterruptPlatformResources -> nat -> TaskInvocationOrigin -> Z -> Assertion)
    (interrupt_platform_saved : InterruptPlatformResources -> InterruptSaveToken -> Assertion)
    (critical_region_outside : CriticalRegionResources -> StableGlobVars -> nat -> UCOS2_Verify_State -> Assertion)
    (critical_region_inside : CriticalRegionResources -> StableGlobVars -> nat -> UCOS2_Verify_State -> Assertion)
    (critical_region_masked : InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> nat -> TaskInvocationOrigin -> Z -> UCOS2_Verify_State -> Assertion)
    (critical_region_interval : CriticalRegionResources -> StableGlobVars -> nat -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop)
    (save_token : Z -> nat -> TaskInvocationOrigin -> InterruptSaveToken)
    (interrupt_saved_value : Z -> Z -> Prop)
    (armv7a_irq_fiq_mask : Z -> Z)
    (UCOS2_raw_rep : StableGlobVars -> UCOS2_Verify_State -> Assertion)
    (UCOS2_inv : StableGlobVars -> UCOS2_Verify_State -> Assertion)
    (task_tcb_init_arguments : TaskTCBInitArgs -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
    (task_tcb_init_global_addresses : StableGlobVars -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
    (task_tcb_init_entry : StableGlobVars -> TaskTCBInitArgs -> nat -> TaskInvocationOrigin -> UCOS2_Verify_State -> Prop)
    (task_tcb_init_pre : InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> TaskTCBInitArgs -> nat -> TaskInvocationOrigin -> Z -> UCOS2_Verify_State -> Assertion)
    (task_tcb_init_post : InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> TaskTCBInitArgs -> nat -> TaskInvocationOrigin -> Z -> UCOS2_Verify_State -> Z -> Assertion)
    (task_tcb_init_free_root : StableGlobVars -> UCOS2_Verify_State -> Z)
    (task_tcb_init_public_without_free_root : StableGlobVars -> UCOS2_Verify_State -> Assertion)
    (task_tcb_init_public_without_free_head : StableGlobVars -> UCOS2_Verify_State -> list Z -> Assertion)
    (task_tcb_init_detached_state : TaskTCBInitArgs -> nat -> TaskInvocationOrigin -> UCOS2_Verify_State -> Z -> list Z -> TCBLayoutImage -> UCOS2_Verify_State)
    (task_tcb_init_detach_observation : TaskTCBInitArgs -> nat -> TaskInvocationOrigin -> UCOS2_Verify_State -> Z -> list Z -> TCBLayoutImage -> Prop)
    (tcb_layout_common_image : TCBLayoutImage -> TCBCommonImage)
    (task_tcb_init_retained_storage : Z -> TCBCommonImage -> Assertion)
    (task_tcb_init_retained_without_links : Z -> TCBCommonImage -> Assertion)
    (task_tcb_init_register_prefix : Z -> Z -> Assertion)
    (task_tcb_init_raw_image : TaskTCBInitArgs -> TCBCommonImage -> TCBCommonImage)
    (tcb64_addr : StableGlobVars -> Z -> Z)
    (tcb64_storage_rep : Z -> TCBCommonImage -> Assertion)
    (tcb64_storage_without : Z -> TCBField -> TCBCommonImage -> Assertion)
    (TCBNext : TCBField)
    (GlobalStrings : (String -> Z) -> Assertion)
    (task_tcb_init_free_next : StableGlobVars -> list Z -> Z)
    (task_tcb_init_free_next_image : TCBLayoutImage -> Z -> Prop)
    (task_tcb_init_no_free : UCOS2_Verify_State -> Prop)
    (task_tcb_init_active_head : StableGlobVars -> UCOS2_Verify_State -> Z)
    (task_tcb_init_count : UCOS2_Verify_State -> Z)
    (task_tcb_init_ready_group : UCOS2_Verify_State -> Z)
    (task_tcb_init_ready_rows : UCOS2_Verify_State -> list Z)
    (task_tcb_init_priority_table : StableGlobVars -> UCOS2_Verify_State -> list Z)
    (task_tcb_init_used_storage : StableGlobVars -> UCOS2_Verify_State -> Assertion)
    (task_tcb_init_used_without_head_prev : StableGlobVars -> UCOS2_Verify_State -> Assertion)
    (task_tcb_init_used_with_head_prev : StableGlobVars -> UCOS2_Verify_State -> Z -> Assertion)
    (task_tcb_init_publication_other : StableGlobVars -> UCOS2_Verify_State -> Assertion)
    (task_tcb_init_published_state : StableGlobVars -> TaskTCBInitArgs -> nat -> UCOS2_Verify_State -> UCOS2_Verify_State -> Z -> TCBLayoutImage -> UCOS2_Verify_State)
    (task_tcb_init_commit_binding : TaskTCBInitArgs -> nat -> TaskInvocationOrigin -> UCOS2_Verify_State -> UCOS2_Verify_State -> Z -> Prop)
    (UCOS2_state_inv : StableGlobVars -> UCOS2_Verify_State -> Prop)
    (task_tcb_init_result : CriticalRegionResources -> StableGlobVars -> TaskTCBInitArgs -> nat -> TaskInvocationOrigin -> UCOS2_Verify_State -> Z -> UCOS2_Verify_State -> Prop)
    (UCharArray::full : Z -> Z -> list Z -> Assertion)
    (PtrArray::full : Z -> Z -> list Z -> Assertion)
*/

typedef unsigned char  INT8U;
typedef unsigned short INT16U;
typedef unsigned int   INT32U;
typedef unsigned int   OS_STK;
typedef unsigned int   OS_CPU_SR;
typedef INT8U          OS_PRIO;
typedef INT16U         OS_FLAGS;

#define OS_LOWEST_PRIO          63u
#define OS_TASK_REG_TBL_SIZE     1u
#define OS_RDY_TBL_SIZE          8u
#define OS_STAT_RDY          0x00u
#define OS_STAT_PEND_OK          0u
#define OS_ERR_NONE              0u
#define OS_ERR_TASK_NO_MORE_TCB 66u

#define OS_ENTER_CRITICAL() do {cpu_sr = OS_CPU_SR_Save();} while (0)
#define OS_EXIT_CRITICAL()  do {OS_CPU_SR_Restore(cpu_sr);} while (0)
#define OS_TRACE_TASK_READY(p_tcb)

struct os_event;
typedef struct os_event OS_EVENT;
struct os_flag_node;
typedef struct os_flag_node OS_FLAG_NODE;

typedef struct os_tcb {
    OS_STK        *OSTCBStkPtr;
    void          *OSTCBExtPtr;
    OS_STK        *OSTCBStkBottom;
    INT32U         OSTCBStkSize;
    INT16U         OSTCBOpt;
    INT16U         OSTCBId;
    struct os_tcb *OSTCBNext;
    struct os_tcb *OSTCBPrev;
    OS_EVENT      *OSTCBEventPtr;
    void          *OSTCBMsg;
    OS_FLAG_NODE  *OSTCBFlagNode;
    OS_FLAGS       OSTCBFlagsRdy;
    INT32U         OSTCBDly;
    INT8U          OSTCBStat;
    INT8U          OSTCBStatPend;
    INT8U          OSTCBPrio;
    INT8U          OSTCBX;
    INT8U          OSTCBY;
    OS_PRIO        OSTCBBitX;
    OS_PRIO        OSTCBBitY;
    INT8U          OSTCBDelReq;
    INT8U         *OSTCBTaskName;
    INT32U         OSTCBRegTbl[OS_TASK_REG_TBL_SIZE];
} OS_TCB;

extern OS_TCB *OSTCBFreeList;
extern OS_TCB *OSTCBList;
extern OS_TCB *OSTCBPrioTbl[OS_LOWEST_PRIO + 1u];
extern OS_PRIO OSRdyGrp;
extern OS_PRIO OSRdyTbl[OS_RDY_TBL_SIZE];
extern INT8U OSTaskCtr;

/* Modular platform/CSL wrapper contract. The actual saved word retains the
 * original IRQ/FIQ mask and invocation. Raw bytes are borrowed from the
 * logical region; certified source traces transport validity and the private
 * creation key at the two acquire assertions. Restore must return the FULL
 * native invariant. A concrete platform/region/client linking proof remains
 * distinct from this parameterized client contract. */
OS_CPU_SR OS_CPU_SR_Save(void)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
         (sg : StableGlobVars) (before : UCOS2_Verify_State)
         (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
    Require interrupt_platform_running(platform, invocation, origin, mask) *
            critical_region_outside(critical, sg, invocation, before)
    Ensure exists (acquired : UCOS2_Verify_State),
             critical_region_interval(critical, sg, invocation, before, acquired) &&
             interrupt_saved_value(mask, __return) &&
             critical_region_masked(platform, critical, sg, invocation, origin, __return, acquired) *
             UCOS2_raw_rep(sg, acquired)
*/
;
void OS_CPU_SR_Restore(OS_CPU_SR cpu_sr)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
         (sg : StableGlobVars) (acquired released : UCOS2_Verify_State)
         (invocation : nat) (origin : TaskInvocationOrigin) (saved : Z)
    Require cpu_sr == saved &&
            critical_region_masked(platform, critical, sg, invocation, origin, saved, acquired) *
            UCOS2_inv(sg, released)
    Ensure interrupt_platform_running(platform, invocation, origin, armv7a_irq_fiq_mask(saved)) *
           critical_region_outside(critical, sg, invocation, released)
*/
;

/* The four bodies below are exactly the source-selected implementation.
 * An arbitrary frame is preserved by their direct C steps. Interrupt and
 * resumption effects are composed separately in task_tcb_init_hook_call. */
void App_TaskCreateHook(OS_TCB *ptcb)
/*@ With (frame : Assertion)
    Require frame
    Ensure frame
*/
{
    (void)ptcb;
}

void App_TCBInitHook(OS_TCB *ptcb)
/*@ With (frame : Assertion)
    Require frame
    Ensure frame
*/
{
    (void)ptcb;
}

void OSTCBInitHook(OS_TCB *ptcb)
/*@ With (frame : Assertion)
    Require frame
    Ensure frame
*/
{
    App_TCBInitHook(ptcb)/*@ where frame = frame */;
}

void OSTaskCreateHook(OS_TCB *ptcb)
/*@ With (frame : Assertion)
    Require frame
    Ensure frame
*/
{
    App_TaskCreateHook(ptcb)/*@ where frame = frame */;
}

INT8U OS_TCBInit(INT8U prio,
                 OS_STK *ptos,
                 OS_STK *pbos,
                 INT16U id,
                 INT32U stk_size,
                 void *pext,
                 INT16U opt)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
         (sg : StableGlobVars) (args : TaskTCBInitArgs)
         (invocation : nat) (origin : TaskInvocationOrigin)
         (mask : Z) (initial : UCOS2_Verify_State) (LitMap : String -> Z)
    Require task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
              OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
            task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt,
              LitMap("?")) &&
            task_tcb_init_pre(platform, critical, sg, args, invocation, origin, mask, initial) *
            GlobalStrings(LitMap)
    Ensure task_tcb_init_post(platform, critical, sg, args, invocation, origin,
              mask, initial, __return) * GlobalStrings(LitMap)
*/
{
    OS_TCB *ptcb;
    OS_CPU_SR cpu_sr = 0u;
    INT8U i;

    /*@ task_tcb_init_pre(platform, critical, sg, args, invocation, origin, mask, initial)
        which implies
          task_tcb_init_entry(sg, args, invocation, origin, initial) &&
          interrupt_platform_running(platform, invocation, origin, mask) *
          critical_region_outside(critical, sg, invocation, initial)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (acquired : UCOS2_Verify_State),
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          critical_region_interval(critical, sg, invocation, initial, acquired) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
          data_at(&OSTCBFreeList, OS_TCB *, task_tcb_init_free_root(sg, acquired)) *
          task_tcb_init_public_without_free_root(sg, acquired) * GlobalStrings(LitMap) *
          undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&i, INT8U)
    */
    ptcb = OSTCBFreeList;
    if (ptcb != (OS_TCB *)0) {
        /*@ Assert exists (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage) (next_free : Z),
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
              critical_region_interval(critical, sg, invocation, initial, acquired) &&
              interrupt_saved_value(mask, cpu_sr) &&
              task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
              task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
              task_tcb_init_free_next_image(free_image, next_free) &&
              next_free == task_tcb_init_free_next(sg, rest) &&
              ptcb == tcb64_addr(sg, slot) &&
              critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
              data_at(&OSTCBFreeList, OS_TCB *, ptcb) *
              data_at(&ptcb->OSTCBNext, OS_TCB *, next_free) *
              tcb64_storage_without(ptcb, TCBNext, tcb_layout_common_image(free_image)) *
              task_tcb_init_public_without_free_head(sg, acquired, rest) * GlobalStrings(LitMap) *
              undef_data_at(&i, INT8U)
        */
        OSTCBFreeList = ptcb->OSTCBNext;
        /*@ Assert exists (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage),
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
              critical_region_interval(critical, sg, invocation, initial, acquired) &&
              interrupt_saved_value(mask, cpu_sr) &&
              task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
              task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
              ptcb == tcb64_addr(sg, slot) &&
              critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
              UCOS2_inv(sg,
                task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image)) *
              tcb64_storage_rep(ptcb, tcb_layout_common_image(free_image)) * GlobalStrings(LitMap) *
              undef_data_at(&i, INT8U)
        */
        OS_EXIT_CRITICAL();
        /*@ Assert exists (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage),
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          critical_region_interval(critical, sg, invocation, initial, acquired) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
          task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
          ptcb == tcb64_addr(sg, slot) &&
          interrupt_platform_running(platform, invocation, origin, armv7a_irq_fiq_mask(cpu_sr)) *
          critical_region_outside(critical, sg, invocation,
            task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image)) *
          task_tcb_init_retained_storage(ptcb, tcb_layout_common_image(free_image)) *
          undef_data_at(&ptcb->OSTCBStkPtr, OS_STK *) *
          undef_data_at(&ptcb->OSTCBPrio, INT8U) *
          undef_data_at(&ptcb->OSTCBStat, INT8U) *
          undef_data_at(&ptcb->OSTCBStatPend, INT8U) *
          undef_data_at(&ptcb->OSTCBDly, INT32U) *
          undef_data_at(&ptcb->OSTCBExtPtr, void *) *
          undef_data_at(&ptcb->OSTCBStkSize, INT32U) *
          undef_data_at(&ptcb->OSTCBStkBottom, OS_STK *) *
          undef_data_at(&ptcb->OSTCBOpt, INT16U) *
          undef_data_at(&ptcb->OSTCBId, INT16U) *
          undef_data_at(&ptcb->OSTCBDelReq, INT8U) *
          undef_data_at(&ptcb->OSTCBY, INT8U) *
          undef_data_at(&ptcb->OSTCBX, INT8U) *
          undef_data_at(&ptcb->OSTCBBitY, OS_PRIO) *
          undef_data_at(&ptcb->OSTCBBitX, OS_PRIO) *
          undef_data_at(&ptcb->OSTCBEventPtr, OS_EVENT *) *
          undef_data_at(&ptcb->OSTCBFlagNode, OS_FLAG_NODE *) *
          undef_data_at(&ptcb->OSTCBMsg, void *) *
          undef_data_at(&ptcb->OSTCBTaskName, INT8U *) *
          UIntArray::undef_full(ptcb->OSTCBRegTbl, 1) * GlobalStrings(LitMap) *
          undef_data_at(&i, INT8U)
        */
        ptcb->OSTCBStkPtr = ptos;
        ptcb->OSTCBPrio = prio;
        ptcb->OSTCBStat = OS_STAT_RDY;
        ptcb->OSTCBStatPend = OS_STAT_PEND_OK;
        ptcb->OSTCBDly = 0u;
        ptcb->OSTCBExtPtr = pext;
        ptcb->OSTCBStkSize = stk_size;
        ptcb->OSTCBStkBottom = pbos;
        ptcb->OSTCBOpt = opt;
        ptcb->OSTCBId = id;
        ptcb->OSTCBDelReq = OS_ERR_NONE;
        ptcb->OSTCBY = (INT8U)(prio >> 3u);
        ptcb->OSTCBX = (INT8U)(prio & 0x07u);
        ptcb->OSTCBBitY = (OS_PRIO)(1uL << ptcb->OSTCBY);
        ptcb->OSTCBBitX = (OS_PRIO)(1uL << ptcb->OSTCBX);
        ptcb->OSTCBEventPtr = (OS_EVENT *)0;
        ptcb->OSTCBFlagNode = (OS_FLAG_NODE *)0;
        ptcb->OSTCBMsg = (void *)0;
        ptcb->OSTCBTaskName = (INT8U *)(void *)"?";
        /*@ Inv Assert exists (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage),
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          critical_region_interval(critical, sg, invocation, initial, acquired) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
          task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
          ptcb == tcb64_addr(sg, slot) &&
          0 <= i && i <= 1 &&
          interrupt_platform_running(platform, invocation, origin, armv7a_irq_fiq_mask(cpu_sr)) *
          critical_region_outside(critical, sg, invocation,
            task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image)) *
          task_tcb_init_retained_storage(ptcb, tcb_layout_common_image(free_image)) *
          data_at(&ptcb->OSTCBStkPtr, OS_STK *, ptos) *
          data_at(&ptcb->OSTCBPrio, INT8U, prio) *
          data_at(&ptcb->OSTCBStat, INT8U, 0) *
          data_at(&ptcb->OSTCBStatPend, INT8U, 0) *
          data_at(&ptcb->OSTCBDly, INT32U, 0) *
          data_at(&ptcb->OSTCBExtPtr, void *, pext) *
          data_at(&ptcb->OSTCBStkSize, INT32U, stk_size) *
          data_at(&ptcb->OSTCBStkBottom, OS_STK *, pbos) *
          data_at(&ptcb->OSTCBOpt, INT16U, opt) *
          data_at(&ptcb->OSTCBId, INT16U, id) *
          data_at(&ptcb->OSTCBDelReq, INT8U, 0) *
          data_at(&ptcb->OSTCBY, INT8U, prio / 8) *
          data_at(&ptcb->OSTCBX, INT8U, prio % 8) *
          data_at(&ptcb->OSTCBBitY, OS_PRIO, 1 << (prio / 8)) *
          data_at(&ptcb->OSTCBBitX, OS_PRIO, 1 << (prio % 8)) *
          data_at(&ptcb->OSTCBEventPtr, OS_EVENT *, 0) *
          data_at(&ptcb->OSTCBFlagNode, OS_FLAG_NODE *, 0) *
          data_at(&ptcb->OSTCBMsg, void *, 0) *
          data_at(&ptcb->OSTCBTaskName, INT8U *, LitMap("?")) *
          UIntArray::seg(ptcb->OSTCBRegTbl, 0, i, zeros(i)) *
          UIntArray::undef_seg(ptcb->OSTCBRegTbl, i, 1) * GlobalStrings(LitMap)
        */
        for (i = 0u; i < OS_TASK_REG_TBL_SIZE; i++) {
            ptcb->OSTCBRegTbl[i] = 0u;
        }

        /*@ Assert exists (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage),
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          critical_region_interval(critical, sg, invocation, initial, acquired) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
          task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
          ptcb == tcb64_addr(sg, slot) &&
          i == 1 &&
          interrupt_platform_running(platform, invocation, origin, armv7a_irq_fiq_mask(cpu_sr)) *
          critical_region_outside(critical, sg, invocation,
            task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image)) *
          tcb64_storage_rep(ptcb, task_tcb_init_raw_image(args, tcb_layout_common_image(free_image))) *
          GlobalStrings(LitMap)
        */

        OSTCBInitHook(ptcb)/*@ where frame = GlobalStrings(LitMap) */;
        OSTaskCreateHook(ptcb)/*@ where frame = GlobalStrings(LitMap) */;

        OS_ENTER_CRITICAL();
        /*@ Assert exists (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage) (current : UCOS2_Verify_State),
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          critical_region_interval(critical, sg, invocation, initial, acquired) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
          task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
          ptcb == tcb64_addr(sg, slot) &&
          i == 1 && 0 <= prio && prio < 64 &&
          0 <= prio / 8 && prio / 8 < 8 && 0 <= prio % 8 && prio % 8 < 8 &&
          critical_region_interval(critical, sg, invocation,
            task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image), current) &&
          task_tcb_init_commit_binding(args, invocation, origin, acquired, current, slot) &&
          UCOS2_state_inv(sg, current) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, current) *
          task_tcb_init_retained_without_links(ptcb, tcb_layout_common_image(free_image)) *
          data_at(&ptcb->OSTCBStkPtr, OS_STK *, ptos) *
          data_at(&ptcb->OSTCBPrio, INT8U, prio) *
          data_at(&ptcb->OSTCBStat, INT8U, 0) *
          data_at(&ptcb->OSTCBStatPend, INT8U, 0) *
          data_at(&ptcb->OSTCBDly, INT32U, 0) *
          data_at(&ptcb->OSTCBExtPtr, void *, pext) *
          data_at(&ptcb->OSTCBStkSize, INT32U, stk_size) *
          data_at(&ptcb->OSTCBStkBottom, OS_STK *, pbos) *
          data_at(&ptcb->OSTCBOpt, INT16U, opt) *
          data_at(&ptcb->OSTCBId, INT16U, id) *
          data_at(&ptcb->OSTCBDelReq, INT8U, 0) *
          data_at(&ptcb->OSTCBY, INT8U, prio / 8) *
          data_at(&ptcb->OSTCBX, INT8U, prio % 8) *
          data_at(&ptcb->OSTCBBitY, OS_PRIO, 1 << (prio / 8)) *
          data_at(&ptcb->OSTCBBitX, OS_PRIO, 1 << (prio % 8)) *
          data_at(&ptcb->OSTCBEventPtr, OS_EVENT *, 0) *
          data_at(&ptcb->OSTCBFlagNode, OS_FLAG_NODE *, 0) *
          data_at(&ptcb->OSTCBMsg, void *, 0) *
          data_at(&ptcb->OSTCBTaskName, INT8U *, LitMap("?")) *
          UIntArray::full(ptcb->OSTCBRegTbl, 1, zeros(1)) *
          undef_data_at(&ptcb->OSTCBNext, OS_TCB *) *
          undef_data_at(&ptcb->OSTCBPrev, OS_TCB *) *
          data_at(&OSTCBList, OS_TCB *, task_tcb_init_active_head(sg, current)) *
          task_tcb_init_used_storage(sg, current) *
          data_at(&OSTaskCtr, INT8U, task_tcb_init_count(current)) *
          data_at(&OSRdyGrp, OS_PRIO, task_tcb_init_ready_group(current)) *
          UCharArray::full(OSRdyTbl, 8, task_tcb_init_ready_rows(current)) *
          PtrArray::full(OSTCBPrioTbl, 64, task_tcb_init_priority_table(sg, current)) *
          task_tcb_init_publication_other(sg, current) * GlobalStrings(LitMap)
        */
        ptcb->OSTCBNext = OSTCBList;
        ptcb->OSTCBPrev = (OS_TCB *)0;
        if (OSTCBList != (OS_TCB *)0) {
            /*@ Assert exists (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage) (current : UCOS2_Verify_State)
                         (head : Z) (previous : Z),
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          critical_region_interval(critical, sg, invocation, initial, acquired) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
          task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
          ptcb == tcb64_addr(sg, slot) &&
          i == 1 && 0 <= prio && prio < 64 &&
          0 <= prio / 8 && prio / 8 < 8 && 0 <= prio % 8 && prio % 8 < 8 &&
          critical_region_interval(critical, sg, invocation,
            task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image), current) &&
          task_tcb_init_commit_binding(args, invocation, origin, acquired, current, slot) &&
          UCOS2_state_inv(sg, current) &&
          head == task_tcb_init_active_head(sg, current) && head != 0 &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, current) *
          task_tcb_init_retained_without_links(ptcb, tcb_layout_common_image(free_image)) *
          data_at(&ptcb->OSTCBStkPtr, OS_STK *, ptos) *
          data_at(&ptcb->OSTCBPrio, INT8U, prio) *
          data_at(&ptcb->OSTCBStat, INT8U, 0) *
          data_at(&ptcb->OSTCBStatPend, INT8U, 0) *
          data_at(&ptcb->OSTCBDly, INT32U, 0) *
          data_at(&ptcb->OSTCBExtPtr, void *, pext) *
          data_at(&ptcb->OSTCBStkSize, INT32U, stk_size) *
          data_at(&ptcb->OSTCBStkBottom, OS_STK *, pbos) *
          data_at(&ptcb->OSTCBOpt, INT16U, opt) *
          data_at(&ptcb->OSTCBId, INT16U, id) *
          data_at(&ptcb->OSTCBDelReq, INT8U, 0) *
          data_at(&ptcb->OSTCBY, INT8U, prio / 8) *
          data_at(&ptcb->OSTCBX, INT8U, prio % 8) *
          data_at(&ptcb->OSTCBBitY, OS_PRIO, 1 << (prio / 8)) *
          data_at(&ptcb->OSTCBBitX, OS_PRIO, 1 << (prio % 8)) *
          data_at(&ptcb->OSTCBEventPtr, OS_EVENT *, 0) *
          data_at(&ptcb->OSTCBFlagNode, OS_FLAG_NODE *, 0) *
          data_at(&ptcb->OSTCBMsg, void *, 0) *
          data_at(&ptcb->OSTCBTaskName, INT8U *, LitMap("?")) *
          UIntArray::full(ptcb->OSTCBRegTbl, 1, zeros(1)) *
          data_at(&ptcb->OSTCBNext, OS_TCB *, task_tcb_init_active_head(sg, current)) *
          data_at(&ptcb->OSTCBPrev, OS_TCB *, 0) *
          data_at(&OSTCBList, OS_TCB *, head) *
          data_at(&((OS_TCB *)head)->OSTCBPrev, OS_TCB *, previous) *
          task_tcb_init_used_without_head_prev(sg, current) *
          data_at(&OSTaskCtr, INT8U, task_tcb_init_count(current)) *
          data_at(&OSRdyGrp, OS_PRIO, task_tcb_init_ready_group(current)) *
          UCharArray::full(OSRdyTbl, 8, task_tcb_init_ready_rows(current)) *
          PtrArray::full(OSTCBPrioTbl, 64, task_tcb_init_priority_table(sg, current)) *
          task_tcb_init_publication_other(sg, current) * GlobalStrings(LitMap)
            */
            OSTCBList->OSTCBPrev = ptcb;
        }
        /*@ Assert exists (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage) (current : UCOS2_Verify_State),
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          critical_region_interval(critical, sg, invocation, initial, acquired) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
          task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
          ptcb == tcb64_addr(sg, slot) &&
          i == 1 && 0 <= prio && prio < 64 &&
          0 <= prio / 8 && prio / 8 < 8 && 0 <= prio % 8 && prio % 8 < 8 &&
          critical_region_interval(critical, sg, invocation,
            task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image), current) &&
          task_tcb_init_commit_binding(args, invocation, origin, acquired, current, slot) &&
          UCOS2_state_inv(sg, current) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, current) *
          task_tcb_init_retained_without_links(ptcb, tcb_layout_common_image(free_image)) *
          data_at(&ptcb->OSTCBStkPtr, OS_STK *, ptos) *
          data_at(&ptcb->OSTCBPrio, INT8U, prio) *
          data_at(&ptcb->OSTCBStat, INT8U, 0) *
          data_at(&ptcb->OSTCBStatPend, INT8U, 0) *
          data_at(&ptcb->OSTCBDly, INT32U, 0) *
          data_at(&ptcb->OSTCBExtPtr, void *, pext) *
          data_at(&ptcb->OSTCBStkSize, INT32U, stk_size) *
          data_at(&ptcb->OSTCBStkBottom, OS_STK *, pbos) *
          data_at(&ptcb->OSTCBOpt, INT16U, opt) *
          data_at(&ptcb->OSTCBId, INT16U, id) *
          data_at(&ptcb->OSTCBDelReq, INT8U, 0) *
          data_at(&ptcb->OSTCBY, INT8U, prio / 8) *
          data_at(&ptcb->OSTCBX, INT8U, prio % 8) *
          data_at(&ptcb->OSTCBBitY, OS_PRIO, 1 << (prio / 8)) *
          data_at(&ptcb->OSTCBBitX, OS_PRIO, 1 << (prio % 8)) *
          data_at(&ptcb->OSTCBEventPtr, OS_EVENT *, 0) *
          data_at(&ptcb->OSTCBFlagNode, OS_FLAG_NODE *, 0) *
          data_at(&ptcb->OSTCBMsg, void *, 0) *
          data_at(&ptcb->OSTCBTaskName, INT8U *, LitMap("?")) *
          UIntArray::full(ptcb->OSTCBRegTbl, 1, zeros(1)) *
          data_at(&ptcb->OSTCBNext, OS_TCB *, task_tcb_init_active_head(sg, current)) *
          data_at(&ptcb->OSTCBPrev, OS_TCB *, 0) *
          data_at(&OSTCBList, OS_TCB *, task_tcb_init_active_head(sg, current)) *
          task_tcb_init_used_with_head_prev(sg, current, slot) *
          data_at(&OSTaskCtr, INT8U, task_tcb_init_count(current)) *
          data_at(&OSRdyGrp, OS_PRIO, task_tcb_init_ready_group(current)) *
          UCharArray::full(OSRdyTbl, 8, task_tcb_init_ready_rows(current)) *
          PtrArray::full(OSTCBPrioTbl, 64, task_tcb_init_priority_table(sg, current)) *
          task_tcb_init_publication_other(sg, current) * GlobalStrings(LitMap)
        */
        OSTCBList = ptcb;
        OSRdyGrp |= ptcb->OSTCBBitY;
        OSRdyTbl[ptcb->OSTCBY] |= ptcb->OSTCBBitX;
        OSTaskCtr++;
        OSTCBPrioTbl[prio] = ptcb;
        OS_TRACE_TASK_READY(ptcb);
        /*@ Assert exists (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage) (current : UCOS2_Verify_State),
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          interrupt_saved_value(mask, cpu_sr) && i == 1 &&
          task_tcb_init_result(critical, sg, args, invocation, origin, initial, 0,
            task_tcb_init_published_state(sg, args, invocation, acquired, current, slot, free_image)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, current) *
          UCOS2_inv(sg,
            task_tcb_init_published_state(sg, args, invocation, acquired, current, slot, free_image)) *
          GlobalStrings(LitMap) * undef_data_at(&ptcb, OS_TCB *)
        */
        OS_EXIT_CRITICAL();
        return (OS_ERR_NONE);
    }
    /*@ Assert exists (acquired : UCOS2_Verify_State),
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_result(critical, sg, args, invocation, origin, initial, 66, acquired) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
          UCOS2_inv(sg, acquired) * GlobalStrings(LitMap) *
          undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&i, INT8U)
    */
    OS_EXIT_CRITICAL();
    return (OS_ERR_TASK_NO_MORE_TCB);
}
