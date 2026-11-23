/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSMboxPost (OS_EVENT  *pevent,
                   void      *pmsg)
/*@ With (environment: TaskStackCallEnvironment) saved_local (critical: CriticalRegionResources)
    (sg: StableGlobVars) (caller: TaskResumeCaller) (mask: Z) (before: UCOS2_Verify_State)
    (eid: EventID) (pe message: addr) X
    Require pevent == pe && pmsg == message && mbox_post_profile(sg) && UCOS2_state_inv(sg, before) &&
      mbox_post_call_input(critical, sg, caller, pe, message, before, eid) &&
      mbox_post_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, message, before) &&
      mbox_post_safe(environment, critical, sg, caller, mask, pe, eid, message, before, X) &&
      os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
        &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
      q_post_closed(environment, critical, saved_local, sg, caller, mask, before)
    Ensure mbox_post_post(environment, critical, saved_local, sg, caller, mask, pe, eid, message, before, __return, X)
*/
{
#if OS_CRITICAL_METHOD == 3u
    OS_CPU_SR cpu_sr = 0u;
#endif
#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {
        return (OS_ERR_PEVENT_NULL);
    }
    if (pmsg == (void *)0) {
        return (OS_ERR_POST_NULL_PTR);
    }
#endif
    OS_TRACE_MBOX_POST_ENTER(pevent);
    /*@ pevent == pe && pevent != 0 && pmsg == message && pmsg != 0 && mbox_post_profile(sg) && UCOS2_state_inv(sg, before) &&
        mbox_post_call_input(critical, sg, caller, pe, message, before, eid) &&
        q_post_closed(environment, critical, saved_local, sg, caller, mask, before)
        which implies
        pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && pmsg == message && pmsg != 0 && valid_event_id(sg, eid) &&
        mbox_post_profile(sg) && UCOS2_state_inv(sg, before) &&
        mbox_post_call_input(critical, sg, caller, pe, message, before, eid) &&
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        mbox_post_type_context(environment, saved_local, sg, caller, mask, before, eid) */
    /*@ 0 <= event_slot_type_value(EventState(before), eid) && event_slot_type_value(EventState(before), eid) <= 255 by local */
    if (pevent->OSEventType != OS_EVENT_TYPE_MBOX) {
        OS_TRACE_MBOX_POST_EXIT(OS_ERR_EVENT_TYPE);
        return (OS_ERR_EVENT_TYPE);
    }
    /*@ pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && pmsg == message && pmsg != 0 && valid_event_id(sg, eid) &&
        mbox_post_profile(sg) && UCOS2_state_inv(sg, before) &&
        mbox_post_call_input(critical, sg, caller, pe, message, before, eid) &&
        event_slot_type_value(EventState(before), eid) == 1 &&
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        mbox_post_type_context(environment, saved_local, sg, caller, mask, before, eid)
        which implies pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && pmsg == message && pmsg != 0 &&
        valid_event_id(sg, eid) && mbox_post_profile(sg) &&
        mbox_post_save_pre(environment, critical, saved_local, sg, caller, mask, before, pe, message, eid) */
    OS_ENTER_CRITICAL();
    /*@ pevent == event_addr(sg, eid) && valid_event_id(sg, eid) && mbox_post_profile(sg) &&
        mbox_post_save_result(environment, critical, saved_local, sg, caller, mask, cpu_sr, before, pe, message, eid)
        which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed current: OSEventAbstractState), pevent == event_addr(sg, eid) &&
        mbox_post_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, message, before, acquired, eid, observed, current) * data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, current)) */
    if (pevent->OSEventGrp != 0u) {
        /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed current: OSEventAbstractState), pevent == event_addr(sg, eid) && q_post_group(acquired, current) != 0 &&
            mbox_post_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, message, before, acquired, eid, observed, current) * data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, current))
            which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed current: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState),
            pevent == event_addr(sg, eid) &&
            mbox_post_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, message, before, acquired, eid, observed, current, tid, old) *
            event_task_rdy_pre(sg, TskState(acquired), eid, current, tid, old, 2, 0,
              q_post_sched_group(acquired), q_post_sched_rows(acquired)) */
        (void)OS_EventTaskRdy(pevent, pmsg, OS_STAT_MBOX, OS_STAT_PEND_OK);
        /*@ Assert exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed current: OSEventAbstractState)
            (tid: TaskID) (old: TaskAbstractState) (priority: Z),
            pevent == pe && pevent != 0 && pmsg == message &&
            mbox_post_safe(environment, critical, sg, caller, mask, pe, eid, message, before, X) &&
            mbox_post_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, message, before) &&
            os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
              &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
            mbox_post_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, message, before, acquired, eid, observed, current, tid, old) *
            event_task_rdy_post(sg, TskState(acquired), eid, current, tid, old, message, 2, 0,
              q_post_sched_group(acquired), q_post_sched_rows(acquired), priority) */
        /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed current: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState) (priority: Z),
            pevent == pe && pevent != 0 && pmsg == message &&
            mbox_post_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, message, before, acquired, eid, observed, current, tid, old) *
            event_task_rdy_post(sg, TskState(acquired), eid, current, tid, old, message, 2, 0,
              q_post_sched_group(acquired), q_post_sched_rows(acquired), priority)
            which implies exists (active: TaskResumeCaller) (acquired released: UCOS2_Verify_State),
              pevent == pe && pmsg == message &&
              mbox_post_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, eid, message, before, acquired, released, 0, 1) */
        OS_EXIT_CRITICAL();
        /*@ mbox_post_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, message, before) &&
            mbox_post_restore_post(environment, critical, saved_local, sg, caller, mask, pe, eid, message, before, 0, 1)
            which implies exists (returned: TaskResumeCaller) (restored: UCOS2_Verify_State),
            mbox_post_prefix_result(environment, critical, sg, caller, mask, pe, eid, message, before, 0, 1, returned, restored) &&
            task_resume_sched_pre(environment, critical, saved_local, sg, returned, mask, restored) *
            q_post_extra_tables(sg, returned) */
        OS_Sched();
        OS_TRACE_MBOX_POST_EXIT(OS_ERR_NONE);
        return (OS_ERR_NONE);
    }
    /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed current: OSEventAbstractState), pevent == event_addr(sg, eid) && q_post_group(acquired, current) == 0 &&
        mbox_post_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, message, before, acquired, eid, observed, current) * data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, current))
        which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed current: OSEventAbstractState) (m: MboxFields), pevent == event_addr(sg, eid) &&
        mbox_post_message_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, message, before, acquired, eid, observed, current, m) * data_at(&pevent->OSEventPtr, void *, mbox_message_ptr(m)) */
    if (pevent->OSEventPtr != (void *)0) {
        /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed current: OSEventAbstractState) (m: MboxFields), pevent == pe && pmsg == message && mbox_message_ptr(m) != 0 &&
            mbox_post_message_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, message, before, acquired, eid, observed, current, m) * data_at(&pevent->OSEventPtr, void *, mbox_message_ptr(m))
            which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State),
            pevent == pe && pmsg == message && mbox_post_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, eid, message, before, acquired, acquired, 20, 0) */
        OS_EXIT_CRITICAL();
        OS_TRACE_MBOX_POST_EXIT(OS_ERR_MBOX_FULL);
        return (OS_ERR_MBOX_FULL);
    }
    /*@ Assert exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed current: OSEventAbstractState) (m: MboxFields),
        pevent == pe && pmsg == message && mbox_message_ptr(m) == 0 &&
        mbox_post_safe(environment, critical, sg, caller, mask, pe, eid, message, before, X) &&
        mbox_post_message_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, message, before, acquired, eid, observed, current, m) * data_at(&pevent->OSEventPtr, void *, 0) */
    pevent->OSEventPtr = pmsg;
    /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed current: OSEventAbstractState) (m: MboxFields),
        pevent == pe && pmsg == message && mbox_message_ptr(m) == 0 &&
        mbox_post_message_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, message, before, acquired, eid, observed, current, m) * data_at(&pevent->OSEventPtr, void *, message)
        which implies exists (active: TaskResumeCaller) (acquired released: UCOS2_Verify_State),
        pevent == pe && pmsg == message && mbox_post_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, eid, message, before, acquired, released, 0, 0) */
    OS_EXIT_CRITICAL();
    OS_TRACE_MBOX_POST_EXIT(OS_ERR_NONE);
    return (OS_ERR_NONE);
}
