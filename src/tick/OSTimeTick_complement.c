/* Same OSTimeTick execution body; Timer-complement contract candidate.
 * The smaller external Hook contract remains an unresolved dependency. */
/*
 * uC/OS-II V2.93.01, Source/os_core.c:937: OSTimeTick.
 * Selected queue-v2.93.01-first-round profile and ARMv7-A/GNU macros.
 * Candidate annotation; no completed QCP proof yet. Preserve stepping,
 * volatile OSTime, per-task critical intervals and the real tick hook.
 * A timed-out task remains registered with Event/Flag until caller cleanup.
 * The selected port hook calls App_TimeTickHook and periodically signals
 * Timer service; it is not an empty hook or an already verified callee.
 */

/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_rules_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.stable_glob_vars */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_verify_state_def */
/*@ Import Coq Require Import Ucos2Verify.lib.task_storage */
/*@ Import Coq Require Import Ucos2Verify.lib.tick */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_verify_inv */
/*@ Import Coq Require Import Ucos2Verify.lib.interrupt */
/*@ Import Coq Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.tick.spec.time_tick_complement_spec */
/*@ Import Coq Import TaskStateDef SchedStateDef UCOS2_C_Rules */
#include "verification_stdlib.h"
#include "verification_list.h"

/*@ Extern Coq
    (StableGlobVars :: *) (UCOS2_Verify_State :: *) (TaskAbstractState :: *)
    (InterruptPlatformResources :: *) (CriticalRegionResources :: *)
    (InterruptSaveToken :: *) (TaskInvocationOrigin :: *) (nat :: *)
    (TimeTickApplicationResources :: *)
*/
/*@ Extern Coq
    (interrupt_platform_running : InterruptPlatformResources -> nat -> TaskInvocationOrigin -> Z -> Assertion)
    (interrupt_platform_saved : InterruptPlatformResources -> InterruptSaveToken -> Assertion)
    (interrupt_saved_value : Z -> Z -> Prop)
    (save_token : Z -> nat -> TaskInvocationOrigin -> InterruptSaveToken)
    (time_tick_global_addresses : StableGlobVars -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
    (time_tick_entry : StableGlobVars -> nat -> TaskInvocationOrigin -> UCOS2_Verify_State -> Prop)
    (time_tick_complement_pre : InterruptPlatformResources -> CriticalRegionResources -> TimeTickApplicationResources -> StableGlobVars -> nat -> TaskInvocationOrigin -> UCOS2_Verify_State -> UCOS2_Verify_State -> Z -> Z -> Z -> (UCOS2_Verify_State -> Prop) -> Assertion)
    (time_tick_complement_post : InterruptPlatformResources -> CriticalRegionResources -> TimeTickApplicationResources -> StableGlobVars -> nat -> TaskInvocationOrigin -> UCOS2_Verify_State -> UCOS2_Verify_State -> Z -> Z -> Z -> (UCOS2_Verify_State -> Prop) -> Assertion)
    (time_tick_continuation : TimeTickApplicationResources -> StableGlobVars -> Z -> Z -> UCOS2_Verify_State -> (UCOS2_Verify_State -> Prop) -> Prop)
    (time_tick_complement_client_frame : CriticalRegionResources -> TimeTickApplicationResources -> StableGlobVars -> nat -> UCOS2_Verify_State -> Z -> Z -> Z -> Assertion)
    (time_tick_hook_result : TimeTickApplicationResources -> StableGlobVars -> Z -> Z -> UCOS2_Verify_State -> Z -> Z -> UCOS2_Verify_State -> Prop)
    (UCOS2_inv_missing_timer_pool_body : StableGlobVars -> UCOS2_Verify_State -> Assertion)
    (UCOS2_state_inv : StableGlobVars -> UCOS2_Verify_State -> Prop)
    (time_tick_counted_state : UCOS2_Verify_State -> UCOS2_Verify_State)
    (time_tick_clock_step_state : UCOS2_Verify_State -> UCOS2_Verify_State)
    (time_tick_serialized_after_hook : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State)
    (time_tick_time : UCOS2_Verify_State -> Z)
    (time_tick_step : UCOS2_Verify_State -> Z)
    (time_tick_running : UCOS2_Verify_State -> Z)
    (time_tick_process_byte : UCOS2_Verify_State -> Z)
    (time_tick_list_head : StableGlobVars -> UCOS2_Verify_State -> Z)
    (time_tick_ready_group : UCOS2_Verify_State -> Z)
    (time_tick_ready_rows : UCOS2_Verify_State -> list Z)
    (time_tick_complement_without_time : StableGlobVars -> UCOS2_Verify_State -> Assertion)
    (time_tick_complement_without_step : StableGlobVars -> UCOS2_Verify_State -> Assertion)
    (time_tick_complement_sched_without_running : StableGlobVars -> UCOS2_Verify_State -> Assertion)
    (time_tick_complement_task_without_head : StableGlobVars -> UCOS2_Verify_State -> Assertion)
    (time_tick_cursor : StableGlobVars -> UCOS2_Verify_State -> list Z -> list Z -> UCOS2_Verify_State -> Z -> TaskAbstractState -> Prop)
    (time_tick_complement_cursor_residual : StableGlobVars -> UCOS2_Verify_State -> Z -> TaskAbstractState -> Assertion)
    (time_tick_complement_body_residual : StableGlobVars -> UCOS2_Verify_State -> Z -> TaskAbstractState -> Assertion)
    (time_tick_body_after : StableGlobVars -> UCOS2_Verify_State -> Z -> TaskAbstractState -> UCOS2_Verify_State)
    (time_tick_delay : TaskAbstractState -> Z)
    (time_tick_status : TaskAbstractState -> Z)
    (time_tick_pend_result : TaskAbstractState -> Z)
    (time_tick_priority : TaskAbstractState -> Z)
    (time_tick_next : StableGlobVars -> TaskAbstractState -> Z)
    (time_tick_y : TaskAbstractState -> Z)
    (time_tick_bit_x : TaskAbstractState -> Z)
    (time_tick_bit_y : TaskAbstractState -> Z)
    (time_tick_lookup : UCOS2_Verify_State -> Z -> TaskAbstractState -> Prop)
    (task_slot_addr : StableGlobVars -> Z -> Z)
    (tick_task_update : TaskAbstractState -> TaskAbstractState)
    (UCharArray::full : Z -> Z -> list Z -> Assertion)
    (UCharArray::missing_i : Z -> Z -> Z -> Z -> list Z -> Assertion)
    (replace_Znth : {A} -> Z -> A -> list A -> list A)
*/

typedef unsigned char INT8U;
typedef unsigned short INT16U;
typedef unsigned int INT32U;
typedef unsigned char BOOLEAN;
typedef unsigned int OS_STK;
typedef unsigned int OS_CPU_SR;
typedef INT8U OS_PRIO;
typedef INT16U OS_FLAGS;

#define OS_LOWEST_PRIO 63u
#define OS_TASK_IDLE_PRIO (OS_LOWEST_PRIO)
#define OS_EVENT_TBL_SIZE ((OS_LOWEST_PRIO) / 8u + 1u)
#define OS_RDY_TBL_SIZE ((OS_LOWEST_PRIO) / 8u + 1u)
#define OS_TASK_REG_TBL_SIZE 1u
#define OS_CRITICAL_METHOD 3u
#define OS_TICK_STEP_EN 1u
#define OS_TIME_GET_SET_EN 1u
#define OS_TIME_TICK_HOOK_EN 1u

typedef struct os_event {
    INT8U OSEventType;
    void *OSEventPtr;
    INT16U OSEventCnt;
    OS_PRIO OSEventGrp;
    OS_PRIO OSEventTbl[OS_EVENT_TBL_SIZE];
} OS_EVENT;

struct os_flag_node;
typedef struct os_flag_node OS_FLAG_NODE;

typedef struct os_tcb {
    OS_STK *OSTCBStkPtr;
    void *OSTCBExtPtr;
    OS_STK *OSTCBStkBottom;
    INT32U OSTCBStkSize;
    INT16U OSTCBOpt;
    INT16U OSTCBId;
    struct os_tcb *OSTCBNext;
    struct os_tcb *OSTCBPrev;
    OS_EVENT *OSTCBEventPtr;
    void *OSTCBMsg;
    OS_FLAG_NODE *OSTCBFlagNode;
    OS_FLAGS OSTCBFlagsRdy;
    INT32U OSTCBDly;
    INT8U OSTCBStat;
    INT8U OSTCBStatPend;
    INT8U OSTCBPrio;
    INT8U OSTCBX;
    INT8U OSTCBY;
    OS_PRIO OSTCBBitX;
    OS_PRIO OSTCBBitY;
    INT8U OSTCBDelReq;
    INT8U *OSTCBTaskName;
    INT32U OSTCBRegTbl[OS_TASK_REG_TBL_SIZE];
} OS_TCB;

#define OS_TRUE 1u
#define OS_FALSE 0u
#define OS_TICK_STEP_DIS 0u
#define OS_TICK_STEP_WAIT 1u
#define OS_TICK_STEP_ONCE 2u
#define OS_STAT_RDY 0x00u
#define OS_STAT_SEM 0x01u
#define OS_STAT_MBOX 0x02u
#define OS_STAT_Q 0x04u
#define OS_STAT_SUSPEND 0x08u
#define OS_STAT_MUTEX 0x10u
#define OS_STAT_FLAG 0x20u
#define OS_STAT_PEND_ANY (OS_STAT_SEM | OS_STAT_MBOX | OS_STAT_Q | OS_STAT_MUTEX | OS_STAT_FLAG)
#define OS_STAT_PEND_OK 0u
#define OS_STAT_PEND_TO 1u

#define OS_ENTER_CRITICAL() do {cpu_sr = OS_CPU_SR_Save();} while (0)
#define OS_EXIT_CRITICAL() do {OS_CPU_SR_Restore(cpu_sr);} while (0)
/* Selected os_trace.h defaults: OS_TRACE_EN = 0, no custom overrides. */
#define OS_TRACE_TICK_INCREMENT(tick_ctr)
#define OS_TRACE_TASK_READY(p_tcb)

extern volatile INT32U OSTime;
extern BOOLEAN OSRunning;
extern INT8U OSTickStepState;
extern OS_TCB *OSTCBList;
extern OS_PRIO OSRdyGrp;
extern OS_PRIO OSRdyTbl[OS_RDY_TBL_SIZE];

/* Nested, already-masked platform specialization. The actual saved word
 * and invocation are retained. The caller owns an already-open region;
 * neither nested primitive releases its heap. No ARM/BSP body is proved. */
OS_CPU_SR OS_CPU_SR_Save(void)
/*@ With (platform : InterruptPlatformResources) (invocation : nat) (origin : TaskInvocationOrigin)
    Require interrupt_platform_running(platform, invocation, origin, 192)
    Ensure interrupt_saved_value(192, __return) &&
           interrupt_platform_saved(platform, save_token(__return, invocation, origin))
*/
;
void OS_CPU_SR_Restore(OS_CPU_SR cpu_sr)
/*@ With (platform : InterruptPlatformResources) (invocation : nat)
         (origin : TaskInvocationOrigin) (saved : Z)
    Require cpu_sr == saved && interrupt_saved_value(192, saved) &&
            interrupt_platform_saved(platform, save_token(saved, invocation, origin))
    Ensure interrupt_platform_running(platform, invocation, origin, 192)
*/
;
/* External supported callback class and source-ordered port effect:
 * application-owned work / semaphore posts, private INT16U counter, reset
 * before optional OSTmrSignal. Its Task/Event/Sched result is NOT framed
 * as the entry state. Partial correctness makes no callback termination
 * claim. Full OSSemPost/OSTmrSignal C and platform refinements remain open. */
void OSTimeTickHook(void)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
         (application : TimeTickApplicationResources) (sg : StableGlobVars)
         (invocation : nat) (origin : TaskInvocationOrigin)
         (region_entry initial : UCOS2_Verify_State) (app_value counter_address counter : Z)
    Require time_tick_entry(sg, invocation, origin, initial) &&
            interrupt_platform_running(platform, invocation, origin, 192) *
            time_tick_complement_client_frame(critical, application, sg, invocation, region_entry,
              app_value, counter_address, counter) * UCOS2_inv_missing_timer_pool_body(sg, initial)
    Ensure exists (app_after counter_after : Z) (hook_state : UCOS2_Verify_State),
           time_tick_hook_result(application, sg, app_value, counter, initial,
             app_after, counter_after, hook_state) &&
           interrupt_platform_running(platform, invocation, origin, 192) *
           time_tick_complement_client_frame(critical, application, sg, invocation, region_entry,
             app_after, counter_address, counter_after) * UCOS2_inv_missing_timer_pool_body(sg, hook_state)
*/
;

void OSTimeTick (void)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
         (application : TimeTickApplicationResources) (sg : StableGlobVars)
         (invocation : nat) (origin : TaskInvocationOrigin)
         (region_entry initial : UCOS2_Verify_State) (app_value counter_address counter : Z)
         (X : UCOS2_Verify_State -> Prop)
    Require time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning,
              &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
            time_tick_complement_pre(platform, critical, application, sg, invocation, origin,
              region_entry, initial, app_value, counter_address, counter, X)
    Ensure time_tick_complement_post(platform, critical, application, sg, invocation, origin,
             region_entry, initial, app_value, counter_address, counter, X)
*/
{
    OS_TCB *ptcb;
#if OS_TICK_STEP_EN > 0u
    BOOLEAN step;
#endif
#if OS_CRITICAL_METHOD == 3u
    OS_CPU_SR cpu_sr = 0u;
#endif

#if OS_TIME_TICK_HOOK_EN > 0u
    /*@ time_tick_complement_pre(platform, critical, application, sg, invocation, origin,
          region_entry, initial, app_value, counter_address, counter, X)
        which implies
        time_tick_entry(sg, invocation, origin, initial) &&
        time_tick_continuation(application, sg, app_value, counter, initial, X) &&
        interrupt_platform_running(platform, invocation, origin, 192) *
        time_tick_complement_client_frame(critical, application, sg, invocation, region_entry,
          app_value, counter_address, counter) * UCOS2_inv_missing_timer_pool_body(sg, initial)
    */
    OSTimeTickHook() /*@ where platform=platform, critical=critical, application=application,
      sg=sg, invocation=invocation, origin=origin, region_entry=region_entry,
      initial=initial, app_value=app_value, counter_address=counter_address, counter=counter */;
#endif
#if OS_TIME_GET_SET_EN > 0u
    OS_ENTER_CRITICAL();
    /*@ exists (hook_state : UCOS2_Verify_State),
        time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
        UCOS2_inv_missing_timer_pool_body(sg, hook_state) which implies
        UCOS2_state_inv(sg, hook_state) &&
        0 <= time_tick_time(hook_state) &&
        0 <= time_tick_step(hook_state) && time_tick_step(hook_state) < 256 &&
        data_at(&OSTime, INT32U, time_tick_time(hook_state)) * time_tick_complement_without_time(sg, hook_state)
    */
    OSTime++;
    /*@ exists (hook_state : UCOS2_Verify_State),
        time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
        UCOS2_state_inv(sg, hook_state) &&
        0 <= time_tick_time(hook_state) &&
        0 <= time_tick_step(hook_state) && time_tick_step(hook_state) < 256 &&
        data_at(&OSTime, INT32U, (time_tick_time(hook_state) + 1) % 4294967296) *
        time_tick_complement_without_time(sg, hook_state)
        which implies UCOS2_inv_missing_timer_pool_body(sg, time_tick_counted_state(hook_state))
    */
    OS_TRACE_TICK_INCREMENT(OSTime);
    OS_EXIT_CRITICAL();
#endif
    /*@ exists (hook_state : UCOS2_Verify_State),
        time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
        UCOS2_inv_missing_timer_pool_body(sg, time_tick_counted_state(hook_state)) which implies
        UCOS2_state_inv(sg, time_tick_counted_state(hook_state)) &&
        data_at(&OSRunning, BOOLEAN, time_tick_running(hook_state)) *
        time_tick_complement_sched_without_running(sg, time_tick_counted_state(hook_state))
    */
    if (OSRunning == OS_TRUE) {
        /*@ exists (hook_state : UCOS2_Verify_State),
            time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
            UCOS2_state_inv(sg, time_tick_counted_state(hook_state)) &&
            data_at(&OSRunning, BOOLEAN, time_tick_running(hook_state)) *
            time_tick_complement_sched_without_running(sg, time_tick_counted_state(hook_state))
            which implies UCOS2_inv_missing_timer_pool_body(sg, time_tick_counted_state(hook_state))
        */
#if OS_TICK_STEP_EN > 0u
        /*@ exists (hook_state : UCOS2_Verify_State),
            time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
            UCOS2_inv_missing_timer_pool_body(sg, time_tick_counted_state(hook_state)) which implies
            UCOS2_state_inv(sg, time_tick_counted_state(hook_state)) &&
            0 <= time_tick_time(time_tick_counted_state(hook_state)) &&
            time_tick_time(time_tick_counted_state(hook_state)) < 4294967296 &&
            data_at(&OSTickStepState, INT8U, time_tick_step(hook_state)) *
            time_tick_complement_without_step(sg, time_tick_counted_state(hook_state))
        */
        switch (OSTickStepState) {
            case OS_TICK_STEP_DIS:
                step = OS_TRUE;
                break;
            case OS_TICK_STEP_WAIT:
                step = OS_FALSE;
                break;
            case OS_TICK_STEP_ONCE:
                step = OS_TRUE;
                OSTickStepState = OS_TICK_STEP_WAIT;
                break;
            default:
                step = OS_TRUE;
                OSTickStepState = OS_TICK_STEP_DIS;
                break;
        }
        /*@ exists (hook_state : UCOS2_Verify_State),
            time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
            time_tick_running(hook_state) == 1 && step == time_tick_process_byte(hook_state) &&
            UCOS2_state_inv(sg, time_tick_counted_state(hook_state)) &&
            0 <= time_tick_time(time_tick_counted_state(hook_state)) &&
            time_tick_time(time_tick_counted_state(hook_state)) < 4294967296 &&
            data_at(&OSTickStepState, INT8U, time_tick_step(time_tick_clock_step_state(hook_state))) *
            time_tick_complement_without_step(sg, time_tick_counted_state(hook_state))
            which implies step == time_tick_process_byte(hook_state) &&
              UCOS2_inv_missing_timer_pool_body(sg, time_tick_clock_step_state(hook_state))
        */
        if (step == OS_FALSE) {
            return;
        }
#endif
        /*@ exists (hook_state : UCOS2_Verify_State),
            time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
            UCOS2_inv_missing_timer_pool_body(sg, time_tick_clock_step_state(hook_state)) which implies
            UCOS2_state_inv(sg, time_tick_clock_step_state(hook_state)) &&
            data_at(&OSTCBList, OS_TCB *, time_tick_list_head(sg, hook_state)) *
            time_tick_complement_task_without_head(sg, time_tick_clock_step_state(hook_state))
        */
        ptcb = OSTCBList;
        /*@ exists (hook_state : UCOS2_Verify_State),
            time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
            UCOS2_state_inv(sg, time_tick_clock_step_state(hook_state)) &&
            data_at(&OSTCBList, OS_TCB *, time_tick_list_head(sg, hook_state)) *
            time_tick_complement_task_without_head(sg, time_tick_clock_step_state(hook_state))
            which implies UCOS2_inv_missing_timer_pool_body(sg, time_tick_clock_step_state(hook_state))
        */
        /*@ Inv Assert exists (app_after counter_after : Z) (hook_state : UCOS2_Verify_State)
                       (visited remaining : list Z) (current : UCOS2_Verify_State)
                       (tid : Z) (node : TaskAbstractState) (cpu_word : Z),
              time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning,
                &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
              time_tick_entry(sg, invocation, origin, initial) &&
              time_tick_continuation(application, sg, app_value, counter, initial, X) &&
              time_tick_hook_result(application, sg, app_value, counter, initial,
                app_after, counter_after, hook_state) &&
              time_tick_process_byte(hook_state) == 1 &&
              time_tick_cursor(sg, hook_state, visited, remaining, current, tid, node) &&
              UCOS2_state_inv(sg, current) && time_tick_lookup(current, tid, node) &&
              interrupt_platform_running(platform, invocation, origin, 192) *
              time_tick_complement_client_frame(critical, application, sg, invocation, region_entry,
                app_after, counter_address, counter_after) *
              data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
              data_at(&step, BOOLEAN, 1) * data_at(&cpu_sr, OS_CPU_SR, cpu_word) *
              data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBPrio), INT8U, time_tick_priority(node)) *
              time_tick_complement_cursor_residual(sg, current, tid, node)
        */
        while (ptcb->OSTCBPrio != OS_TASK_IDLE_PRIO) {
            /*@ exists (current : UCOS2_Verify_State) (tid : Z) (node : TaskAbstractState),
                time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
                ptcb == task_slot_addr(sg, tid) && time_tick_lookup(current, tid, node) && UCOS2_state_inv(sg, current) &&
                data_at(&(ptcb->OSTCBPrio), INT8U, time_tick_priority(node)) *
                time_tick_complement_cursor_residual(sg, current, tid, node)
                which implies
                UCOS2_state_inv(sg, current) && time_tick_lookup(current, tid, node) &&
                0 <= time_tick_y(node) && time_tick_y(node) < 8 &&
                0 <= time_tick_delay(node) && time_tick_delay(node) < 4294967296 &&
                data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
                data_at(&(ptcb->OSTCBDly), INT32U, time_tick_delay(node)) *
                data_at(&(ptcb->OSTCBStat), INT8U, time_tick_status(node)) *
                data_at(&(ptcb->OSTCBStatPend), INT8U, time_tick_pend_result(node)) *
                data_at(&(ptcb->OSTCBPrio), INT8U, time_tick_priority(node)) *
                data_at(&(ptcb->OSTCBNext), OS_TCB *, time_tick_next(sg, node)) *
                data_at(&(ptcb->OSTCBY), INT8U, time_tick_y(node)) *
                data_at(&(ptcb->OSTCBBitX), OS_PRIO, time_tick_bit_x(node)) *
                data_at(&(ptcb->OSTCBBitY), OS_PRIO, time_tick_bit_y(node)) *
                data_at(&OSRdyGrp, OS_PRIO, time_tick_ready_group(current)) *
                UCharArray::full(OSRdyTbl, 8, time_tick_ready_rows(current)) *
                time_tick_complement_body_residual(sg, current, tid, node)
            */
            OS_ENTER_CRITICAL();
            if (ptcb->OSTCBDly != 0u) {
                ptcb->OSTCBDly--;
                if (ptcb->OSTCBDly == 0u) {
                    if ((ptcb->OSTCBStat & OS_STAT_PEND_ANY) != OS_STAT_RDY) {
                        ptcb->OSTCBStat &= (INT8U)~(INT8U)OS_STAT_PEND_ANY;
                        ptcb->OSTCBStatPend = OS_STAT_PEND_TO;
                    } else {
                        ptcb->OSTCBStatPend = OS_STAT_PEND_OK;
                    }
                    if ((ptcb->OSTCBStat & OS_STAT_SUSPEND) == OS_STAT_RDY) {
                        OSRdyGrp |= ptcb->OSTCBBitY;
                        OSRdyTbl[ptcb->OSTCBY] |= ptcb->OSTCBBitX;
                        OS_TRACE_TASK_READY(ptcb);
                    }
                }
            }
            ptcb = ptcb->OSTCBNext;
            OS_EXIT_CRITICAL();
        }
    }
}
