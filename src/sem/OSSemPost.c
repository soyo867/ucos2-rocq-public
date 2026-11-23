/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSSemPost (OS_EVENT *pevent)
/*@ With (environment: TaskStackCallEnvironment) saved_local (critical: CriticalRegionResources)
    (sg: StableGlobVars) (caller: TaskResumeCaller) (mask: Z) (before: UCOS2_Verify_State)
    (eid: EventID) (observed: OSEventAbstractState) (pe: addr) X
    Require pevent == pe && sem_post_profile(sg) && UCOS2_state_inv(sg, before) &&
      sem_post_api_call_input(critical, sg, caller, pe, before, eid, observed) &&
      (pevent == 0 || event_object_layout_prop(sg, eid)) &&
      sem_post_api_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, before) &&
      sem_post_api_safe(environment, critical, sg, caller, mask, pe, eid, before, X) &&
      os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
        &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
      q_post_closed(environment, critical, saved_local, sg, caller, mask, before)
    Ensure sem_post_api_post(environment, critical, saved_local, sg, caller, mask, pe, eid, before, __return, X)
*/
{
#if OS_CRITICAL_METHOD == 3u
    OS_CPU_SR cpu_sr = 0u;
#endif
#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {
        return (OS_ERR_PEVENT_NULL);
    }
#endif
    OS_TRACE_SEM_POST_ENTER(pevent);
    /*@ pevent == pe && pevent != 0 && sem_post_profile(sg) && UCOS2_state_inv(sg, before) &&
        sem_post_api_call_input(critical, sg, caller, pe, before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        q_post_closed(environment, critical, saved_local, sg, caller, mask, before)
        which implies
        pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && valid_event_id(sg, eid) && event_object_layout_prop(sg, eid) &&
        sem_post_profile(sg) && UCOS2_state_inv(sg, before) &&
        sem_post_api_call_input(critical, sg, caller, pe, before, eid, observed) &&
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        q_post_type_context(environment, saved_local, sg, caller, mask, before, eid) */
    /*@ 0 <= event_slot_type_value(EventState(before), eid) && event_slot_type_value(EventState(before), eid) <= 255 by local */
    if (pevent->OSEventType != OS_EVENT_TYPE_SEM) {
        OS_TRACE_SEM_POST_EXIT(OS_ERR_EVENT_TYPE);
        return (OS_ERR_EVENT_TYPE);
    }
    /*@ pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && valid_event_id(sg, eid) && event_object_layout_prop(sg, eid) &&
        sem_post_profile(sg) && UCOS2_state_inv(sg, before) &&
        sem_post_api_call_input(critical, sg, caller, pe, before, eid, observed) &&
        event_slot_type_value(EventState(before), eid) == 3 &&
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        q_post_type_context(environment, saved_local, sg, caller, mask, before, eid)
        which implies pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 &&
        valid_event_id(sg, eid) && event_object_layout_prop(sg, eid) && sem_post_profile(sg) &&
        sem_post_api_save_pre(environment, critical, saved_local, sg, caller, mask, before, pe, eid, observed) */
    OS_ENTER_CRITICAL();
    /*@ pevent == event_addr(sg, eid) && valid_event_id(sg, eid) && event_object_layout_prop(sg, eid) && sem_post_profile(sg) &&
        sem_post_api_save_result(environment, critical, saved_local, sg, caller, mask, cpu_sr, before, eid, observed)
        which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState), pevent == event_addr(sg, eid) &&
        sem_post_api_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current) * data_at(&pevent->OSEventGrp, unsigned char, sem_post_group(acquired, current)) */
    if (pevent->OSEventGrp != 0u) {
        /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState), pevent == event_addr(sg, eid) && sem_post_group(acquired, current) != 0 &&
            sem_post_api_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current) * data_at(&pevent->OSEventGrp, unsigned char, sem_post_group(acquired, current))
            which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState),
            pevent == event_addr(sg, eid) &&
            sem_post_api_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, tid, old) *
            event_task_rdy_pre(sg, TskState(acquired), eid, current, tid, old, 1, 0,
              q_post_sched_group(acquired), q_post_sched_rows(acquired)) */
        (void)OS_EventTaskRdy(pevent, (void *)0, OS_STAT_SEM, OS_STAT_PEND_OK);
        /*@ Assert exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState)
            (tid: TaskID) (old: TaskAbstractState) (priority: Z),
            pevent == pe && pevent != 0 && sem_post_api_safe(environment, critical, sg, caller, mask, pe, eid, before, X) &&
            sem_post_api_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, before) &&
            os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
              &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
            sem_post_api_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, tid, old) *
            event_task_rdy_post(sg, TskState(acquired), eid, current, tid, old, 0, 1, 0,
              q_post_sched_group(acquired), q_post_sched_rows(acquired), priority) */
        /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState) (priority: Z),
            pevent == pe && pevent != 0 && sem_post_api_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, tid, old) *
            event_task_rdy_post(sg, TskState(acquired), eid, current, tid, old, 0, 1, 0,
              q_post_sched_group(acquired), q_post_sched_rows(acquired), priority)
            which implies exists (active: TaskResumeCaller) (acquired released: UCOS2_Verify_State),
              pevent == pe && sem_post_api_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, eid, before, acquired, released, 0, 1) */
        OS_EXIT_CRITICAL();
        /*@ sem_post_api_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, before) &&
            sem_post_api_restore_post(environment, critical, saved_local, sg, caller, mask, pe, eid, before, 0, 1)
            which implies exists (returned: TaskResumeCaller) (restored: UCOS2_Verify_State),
            sem_post_api_prefix_result(environment, critical, sg, caller, mask, pe, eid, before, 0, 1, returned, restored) &&
            task_resume_sched_pre(environment, critical, saved_local, sg, returned, mask, restored) *
            q_post_extra_tables(sg, returned) */
        OS_Sched();
        OS_TRACE_SEM_POST_EXIT(OS_ERR_NONE);
        return (OS_ERR_NONE);
    }
    /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState),
        pevent == event_addr(sg, eid) && sem_post_group(acquired, current) == 0 &&
        sem_post_api_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current) *
        data_at(&pevent->OSEventGrp, unsigned char, sem_post_group(acquired, current))
        which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState),
        pevent == event_addr(sg, eid) &&
        0 <= encode_event_cnt_value(current) && encode_event_cnt_value(current) <= 65535 &&
        sem_post_api_count_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current) *
        data_at(&pevent->OSEventCnt, unsigned short, encode_event_cnt_value(current)) */
    if (pevent->OSEventCnt < 65535u) {
        pevent->OSEventCnt++;
        /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState),
            pevent == pe && pevent != 0 && pevent == event_addr(sg, eid) &&
            0 <= encode_event_cnt_value(current) && encode_event_cnt_value(current) < 65535 &&
            sem_post_api_count_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current) *
            data_at(&pevent->OSEventCnt, unsigned short, encode_event_cnt_value(current) + 1)
            which implies exists (active: TaskResumeCaller) (acquired released: UCOS2_Verify_State),
            pevent == pe &&
            sem_post_api_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, eid, before, acquired, released, 0, 0) */
        OS_EXIT_CRITICAL();
        OS_TRACE_SEM_POST_EXIT(OS_ERR_NONE);
        return (OS_ERR_NONE);
    }
    /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState),
        pevent == pe && pevent != 0 && pevent == event_addr(sg, eid) &&
        encode_event_cnt_value(current) >= 65535 && encode_event_cnt_value(current) <= 65535 &&
        sem_post_api_count_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current) *
        data_at(&pevent->OSEventCnt, unsigned short, encode_event_cnt_value(current))
        which implies exists (active: TaskResumeCaller) (acquired released: UCOS2_Verify_State),
        pevent == pe &&
        sem_post_api_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, eid, before, acquired, released, 51, 0) */
    OS_EXIT_CRITICAL();
    OS_TRACE_SEM_POST_EXIT(OS_ERR_SEM_OVF);
    return (OS_ERR_SEM_OVF);
}
