/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void OSTimeTick (void)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
         (application : TimeTickApplicationResources) (sg : StableGlobVars)
         (invocation : nat) (origin : TaskInvocationOrigin)
         (region_entry initial : UCOS2_Verify_State) (app_value counter_address counter : Z)
         (X : UCOS2_Verify_State -> Prop)
    Require &OSTmrCtr == counter_address && &OSTmrSemSignal == g_OSTmrSemSignal(sg) &&
            time_tick_internal_addresses(sg, &OSIntNesting, &OSTCBPrioTbl, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
            time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning,
              &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
            time_tick_pre(platform, critical, time_tick_fixed_application(sg, application), sg, invocation, origin,
              region_entry, initial, app_value, counter_address, counter, X)
    Ensure time_tick_post(platform, critical, time_tick_fixed_application(sg, application), sg, invocation, origin,
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
    /*@ time_tick_pre(platform, critical, time_tick_fixed_application(sg, application), sg, invocation, origin,
          region_entry, initial, app_value, counter_address, counter, X)
        which implies
        time_tick_entry(sg, invocation, origin, initial) &&
        time_tick_continuation(time_tick_fixed_application(sg, application), sg, app_value, counter, initial, X) &&
        0 <= counter && counter <= 65535 &&
        time_tick_owned(platform, critical, time_tick_fixed_application(sg, application), sg,
          invocation, origin, region_entry, app_value, counter_address, counter, initial)
    */
    OSTimeTickHook() /*@ where platform=platform, critical=critical, application=application,
      sg=sg, invocation=invocation, origin=origin, region_entry=region_entry,
      before=initial, app_value=app_value, counter=counter */;
    /*@ &OSTmrCtr == counter_address &&
      time_tick_hook_isr_post(platform, critical, application, sg, invocation, origin,
        region_entry, initial, app_value, &OSTmrCtr, counter)
      which implies exists (app_after counter_after : Z) (hook_state : UCOS2_Verify_State),
      time_tick_hook_result(time_tick_fixed_application(sg, application), sg,
        app_value, counter, initial, app_after, counter_after, hook_state) &&
      interrupt_platform_running(platform, invocation, origin, 192) *
      time_tick_client_frame(critical, time_tick_fixed_application(sg, application), sg,
        invocation, region_entry, app_after, counter_address, counter_after) * UCOS2_inv(sg, hook_state) */
#endif
#if OS_TIME_GET_SET_EN > 0u
    OS_ENTER_CRITICAL();
    /*@ exists (hook_state : UCOS2_Verify_State),
        time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
        UCOS2_inv(sg, hook_state) which implies
        UCOS2_state_inv(sg, hook_state) &&
        0 <= time_tick_time(hook_state) &&
        0 <= time_tick_step(hook_state) && time_tick_step(hook_state) < 256 &&
        data_at(&OSTime, INT32U, time_tick_time(hook_state)) * time_tick_without_time(sg, hook_state)
    */
    OSTime++;
    /*@ exists (hook_state : UCOS2_Verify_State),
        time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
        UCOS2_state_inv(sg, hook_state) &&
        0 <= time_tick_time(hook_state) &&
        0 <= time_tick_step(hook_state) && time_tick_step(hook_state) < 256 &&
        data_at(&OSTime, INT32U, (time_tick_time(hook_state) + 1) % 4294967296) *
        time_tick_without_time(sg, hook_state)
        which implies UCOS2_inv(sg, time_tick_counted_state(hook_state))
    */
    OS_TRACE_TICK_INCREMENT(OSTime);
    OS_EXIT_CRITICAL();
#endif
    /*@ exists (hook_state : UCOS2_Verify_State),
        time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
        UCOS2_inv(sg, time_tick_counted_state(hook_state)) which implies
        UCOS2_state_inv(sg, time_tick_counted_state(hook_state)) &&
        data_at(&OSRunning, BOOLEAN, time_tick_running(hook_state)) *
        time_tick_sched_without_running(sg, time_tick_counted_state(hook_state))
    */
    if (OSRunning == OS_TRUE) {
        /*@ exists (hook_state : UCOS2_Verify_State),
            time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
            UCOS2_state_inv(sg, time_tick_counted_state(hook_state)) &&
            data_at(&OSRunning, BOOLEAN, time_tick_running(hook_state)) *
            time_tick_sched_without_running(sg, time_tick_counted_state(hook_state))
            which implies UCOS2_inv(sg, time_tick_counted_state(hook_state))
        */
#if OS_TICK_STEP_EN > 0u
        /*@ exists (hook_state : UCOS2_Verify_State),
            time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
            UCOS2_inv(sg, time_tick_counted_state(hook_state)) which implies
            UCOS2_state_inv(sg, time_tick_counted_state(hook_state)) &&
            0 <= time_tick_time(time_tick_counted_state(hook_state)) &&
            time_tick_time(time_tick_counted_state(hook_state)) < 4294967296 &&
            data_at(&OSTickStepState, INT8U, time_tick_step(hook_state)) *
            time_tick_without_step(sg, time_tick_counted_state(hook_state))
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
            time_tick_without_step(sg, time_tick_counted_state(hook_state))
            which implies step == time_tick_process_byte(hook_state) &&
              UCOS2_inv(sg, time_tick_clock_step_state(hook_state))
        */
        if (step == OS_FALSE) {
            return;
        }
#endif
        /*@ exists (hook_state : UCOS2_Verify_State),
            time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
            UCOS2_inv(sg, time_tick_clock_step_state(hook_state)) which implies
            UCOS2_state_inv(sg, time_tick_clock_step_state(hook_state)) &&
            data_at(&OSTCBList, OS_TCB *, time_tick_list_head(sg, hook_state)) *
            time_tick_task_without_head(sg, time_tick_clock_step_state(hook_state))
        */
        ptcb = OSTCBList;
        /*@ exists (hook_state : UCOS2_Verify_State),
            time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
            UCOS2_state_inv(sg, time_tick_clock_step_state(hook_state)) &&
            data_at(&OSTCBList, OS_TCB *, time_tick_list_head(sg, hook_state)) *
            time_tick_task_without_head(sg, time_tick_clock_step_state(hook_state))
            which implies UCOS2_inv(sg, time_tick_clock_step_state(hook_state))
        */
        /*@ Inv Assert exists (app_after counter_after : Z) (hook_state : UCOS2_Verify_State)
                       (visited remaining : list Z) (current : UCOS2_Verify_State)
                       (tid : Z) (node : TaskAbstractState) (cpu_word : Z),
              time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning,
                &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
              time_tick_entry(sg, invocation, origin, initial) &&
              time_tick_continuation(time_tick_fixed_application(sg, application), sg, app_value, counter, initial, X) &&
              time_tick_hook_result(time_tick_fixed_application(sg, application), sg, app_value, counter, initial,
                app_after, counter_after, hook_state) &&
              time_tick_process_byte(hook_state) == 1 &&
              time_tick_cursor(sg, hook_state, visited, remaining, current, tid, node) &&
              UCOS2_state_inv(sg, current) && time_tick_lookup(current, tid, node) &&
              interrupt_platform_running(platform, invocation, origin, 192) *
              time_tick_client_frame(critical, time_tick_fixed_application(sg, application), sg, invocation, region_entry,
                app_after, counter_address, counter_after) *
              data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
              data_at(&step, BOOLEAN, 1) * data_at(&cpu_sr, OS_CPU_SR, cpu_word) *
              data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBPrio), INT8U, time_tick_priority(node)) *
              time_tick_cursor_residual(sg, current, tid, node)
        */
        while (ptcb->OSTCBPrio != OS_TASK_IDLE_PRIO) {
            /*@ exists (current : UCOS2_Verify_State) (tid : Z) (node : TaskAbstractState),
                time_tick_global_addresses(sg, &OSTime, &OSTickStepState, &OSRunning, &OSTCBList, &OSRdyGrp, OSRdyTbl) &&
                ptcb == task_slot_addr(sg, tid) && time_tick_lookup(current, tid, node) && UCOS2_state_inv(sg, current) &&
                data_at(&(ptcb->OSTCBPrio), INT8U, time_tick_priority(node)) *
                time_tick_cursor_residual(sg, current, tid, node)
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
                time_tick_body_residual(sg, current, tid, node)
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
