/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

OS_EVENT  *OSMboxDel (OS_EVENT  *pevent,
                      INT8U      opt,
                      INT8U     *perr)
/*@ With (environment: TaskStackCallEnvironment) saved_local (critical: CriticalRegionResources)
    (sg: StableGlobVars) (caller: TaskResumeCaller) (mask: Z) (before: UCOS2_Verify_State)
    (eid: EventID) (observed: OSEventAbstractState) (pe error_addr: addr) (choice: Z) X
    Require pevent == pe && mbox_pend_abort_output_address(error_addr, perr) && opt == choice &&
      mbox_del_profile(sg) && UCOS2_state_inv(sg, before) &&
      mbox_del_call_input(critical, sg, caller, pe, before, eid, observed) &&
      mbox_del_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, choice, before) &&
      mbox_del_safe(environment, critical, sg, caller, mask, pe, eid, choice, before, X) &&
      os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
        &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
      &OSEventFreeList == g_OSEventFreeList(sg) &&
      q_post_closed(environment, critical, saved_local, sg, caller, mask, before) * undef_data_at(perr, unsigned char)
    Ensure mbox_del_post(environment, critical, saved_local, sg, caller, mask, pe, eid, choice, before, error_addr, __return, X)
*/
{
    BOOLEAN    tasks_waiting;
    OS_EVENT  *pevent_return;
#if OS_CRITICAL_METHOD == 3u                               /* Allocate storage for CPU status register */
    OS_CPU_SR  cpu_sr = 0u;
#endif


#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return ((OS_EVENT *)0);
    }
#endif

#ifdef OS_SAFETY_CRITICAL_IEC61508
    if (OSSafetyCriticalStartFlag == OS_TRUE) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        *perr = OS_ERR_ILLEGAL_DEL_RUN_TIME;
        return ((OS_EVENT *)0);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {                         /* Validate 'pevent'                        */
        *perr = OS_ERR_PEVENT_NULL;
        return (pevent);
    }
#endif

    OS_TRACE_MBOX_DEL_ENTER(pevent, opt);

    /*@ pevent == pe && pevent != 0 && mbox_del_profile(sg) && UCOS2_state_inv(sg, before) &&
        mbox_del_call_input(critical, sg, caller, pe, before, eid, observed) &&
        q_post_closed(environment, critical, saved_local, sg, caller, mask, before)
        which implies
        pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && valid_event_id(sg, eid) &&
        mbox_del_profile(sg) && UCOS2_state_inv(sg, before) &&
        mbox_del_call_input(critical, sg, caller, pe, before, eid, observed) &&
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        mbox_post_type_context(environment, saved_local, sg, caller, mask, before, eid) */
    /*@ 0 <= event_slot_type_value(EventState(before), eid) && event_slot_type_value(EventState(before), eid) <= 255 by local */
    if (pevent->OSEventType != OS_EVENT_TYPE_MBOX) {          /* Validate event block type                */
        *perr = OS_ERR_EVENT_TYPE;
        OS_TRACE_MBOX_DEL_EXIT(*perr);
        return (pevent);
    }
    /*@ pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && valid_event_id(sg, eid) &&
        mbox_del_profile(sg) && UCOS2_state_inv(sg, before) &&
        mbox_del_call_input(critical, sg, caller, pe, before, eid, observed) &&
        event_slot_type_value(EventState(before), eid) == 1 &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
          &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        mbox_post_type_context(environment, saved_local, sg, caller, mask, before, eid)
        which implies pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 &&
        valid_event_id(sg, eid) && mbox_del_profile(sg) && UCOS2_state_inv(sg, before) &&
        mbox_del_call_input(critical, sg, caller, pe, before, eid, observed) &&
        event_slot_type_value(EventState(before), eid) == 1 &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
          &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
        data_at(&OSIntNesting, unsigned char, q_del_int_nesting(before)) *
        q_del_interrupt_context(environment, saved_local, sg, caller, mask, before) */
    /*@ 0 <= q_del_int_nesting(before) && q_del_int_nesting(before) <= 255 by local */
    if (OSIntNesting > 0u) {                               /* See if called from ISR ...               */
        *perr = OS_ERR_DEL_ISR;                            /* ... can't DELETE from an ISR             */
        OS_TRACE_MBOX_DEL_EXIT(*perr);
        return (pevent);
    }
    /*@ pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && valid_event_id(sg, eid) &&
        mbox_del_profile(sg) && UCOS2_state_inv(sg, before) &&
        mbox_del_call_input(critical, sg, caller, pe, before, eid, observed) &&
        event_slot_type_value(EventState(before), eid) == 1 && q_del_int_nesting(before) <= 0 &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
          &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
        data_at(&OSIntNesting, unsigned char, q_del_int_nesting(before)) *
        q_del_interrupt_context(environment, saved_local, sg, caller, mask, before)
        which implies pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 &&
        valid_event_id(sg, eid) && mbox_del_profile(sg) && q_del_int_nesting(before) <= 0 &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
          &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
        mbox_pend_abort_save_pre(environment, critical, saved_local, sg, caller, mask, before, pe, eid, observed) */
    OS_ENTER_CRITICAL();
    /*@ pevent == event_addr(sg, eid) && valid_event_id(sg, eid) && mbox_del_profile(sg) &&
        mbox_pend_abort_save_result(environment, critical, saved_local, sg, caller, mask, cpu_sr, before, eid, observed)
        which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState),
        pevent == event_addr(sg, eid) &&
        mbox_pend_abort_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial) *
        data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, initial)) */
    if (pevent->OSEventGrp != 0u) {                        /* See if any tasks waiting on mailbox        */
        tasks_waiting = OS_TRUE;                           /* Yes                                      */
    } else {
        tasks_waiting = OS_FALSE;                          /* No                                       */
    }
    /*@ Assert exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState),
        pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 &&
        mbox_pend_abort_output_address(error_addr, perr) && opt == choice &&
        q_del_int_nesting(before) <= 0 && tasks_waiting == q_del_waiting(acquired, initial) &&
        mbox_del_safe(environment, critical, sg, caller, mask, pe, eid, choice, before, X) &&
        mbox_del_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, choice, before) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
          &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
        &OSEventFreeList == g_OSEventFreeList(sg) &&
        mbox_pend_abort_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial) *
        data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, initial)) *
        undef_data_at(perr, unsigned char) * undef_data_at(&pevent_return, OS_EVENT*) */
    /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState),
        pevent == event_addr(sg, eid) && q_del_int_nesting(before) <= 0 && tasks_waiting == q_del_waiting(acquired, initial) &&
        mbox_pend_abort_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial) *
        data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, initial))
        which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState),
        pevent == event_addr(sg, eid) &&
        mbox_del_loop_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired,
          eid, observed, initial, acquired, initial, nil, tasks_waiting) *
        data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, initial)) */
    switch (opt) {
        case OS_DEL_NO_PEND:                               /* Delete mailbox only if no task waiting     */
             if (tasks_waiting == OS_FALSE) {
#if OS_EVENT_NAME_EN > 0u
                 pevent->OSEventName    = (INT8U *)(void *)"?";
#endif
                 /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState),
                 pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && choice == 0 && tasks_waiting <= 0 &&
                 &OSEventFreeList == g_OSEventFreeList(sg) &&
                 mbox_del_loop_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, acquired, initial, nil, tasks_waiting) *
                 data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, initial))
                 which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState),
                 pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 &&
                 &OSEventFreeList == g_OSEventFreeList(sg) &&
                 mbox_del_recycle_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, acquired, initial, nil, tasks_waiting, choice) *
                 data_at(&pevent->OSEventType, unsigned char, 1) * undef_data_at(&pevent->OSEventPtr, void*) *
                 data_at(&pevent->OSEventCnt, unsigned short, q_del_event_count(initial)) *
                 data_at(&OSEventFreeList, OS_EVENT*, q_del_event_free_head(sg, acquired)) */
                 pevent->OSEventType = OS_EVENT_TYPE_UNUSED;
                 pevent->OSEventPtr  = OSEventFreeList;
                 pevent->OSEventCnt  = 0u;
                 OSEventFreeList     = pevent;
                 /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState),
                 pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 &&
                 &OSEventFreeList == g_OSEventFreeList(sg) &&
                 mbox_del_recycle_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, acquired, initial, nil, tasks_waiting, choice) *
                 data_at(&pevent->OSEventType, unsigned char, 0) *
                 data_at(&pevent->OSEventPtr, void*, q_del_event_free_head(sg, acquired)) *
                 data_at(&pevent->OSEventCnt, unsigned short, 0) * data_at(&OSEventFreeList, OS_EVENT*, pevent)
                 which implies exists (active: TaskResumeCaller) (acquired released: UCOS2_Verify_State),
                 pevent == pe && tasks_waiting == tasks_waiting &&
                 mbox_del_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr,
                   pe, eid, choice, before, acquired, released, 0, 0, 0) */
                 OS_EXIT_CRITICAL();
                 /*@ mbox_del_restore_post(environment, critical, saved_local, sg, caller, mask, pe, eid, choice, before, 0, 0, 0)
                     which implies mbox_del_finish_context(environment, critical, saved_local, sg, caller, mask, pe, eid, choice, before, 0, 0) */
                 *perr                  = OS_ERR_NONE;
                 pevent_return          = (OS_EVENT *)0;   /* Mailbox has been deleted                   */
             } else {
                 /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState),
                     pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && choice == 0 && tasks_waiting != 0 &&
                     mbox_del_loop_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired,
                       eid, observed, initial, acquired, initial, nil, tasks_waiting) *
                     data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, initial))
                     which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State),
                     pevent == pe && tasks_waiting == tasks_waiting &&
                     mbox_del_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr,
                       pe, eid, choice, before, acquired, acquired, pe, 73, 0) */
                 OS_EXIT_CRITICAL();
                 /*@ mbox_del_restore_post(environment, critical, saved_local, sg, caller, mask, pe, eid, choice, before, pe, 73, 0)
                     which implies mbox_del_finish_context(environment, critical, saved_local, sg, caller, mask, pe, eid, choice, before, pe, 73) */
                 *perr                  = OS_ERR_TASK_WAITING;
                 pevent_return          = pevent;
             }
             break;

        case OS_DEL_ALWAYS:                                /* Always delete the mailbox                  */
             /*@ Inv Assert exists (active: TaskResumeCaller) (acquired state: UCOS2_Verify_State)
                 (initial node: OSEventAbstractState) (processed: list Priority),
                 pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 &&
                 mbox_pend_abort_output_address(error_addr, perr) && opt == choice && choice == 1 &&
                 mbox_del_safe(environment, critical, sg, caller, mask, pe, eid, choice, before, X) &&
                 mbox_del_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, choice, before) &&
                 os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
                   &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
                 &OSEventFreeList == g_OSEventFreeList(sg) &&
                 mbox_del_loop_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired,
                   eid, observed, initial, state, node, processed, tasks_waiting) *
                 data_at(&pevent->OSEventGrp, unsigned char, q_post_group(state, node)) *
                 undef_data_at(perr, unsigned char) * undef_data_at(&pevent_return, OS_EVENT*) */
             while (pevent->OSEventGrp != 0u) {            /* Ready ALL tasks waiting for mailbox        */
                 /*@ exists (active: TaskResumeCaller) (acquired state: UCOS2_Verify_State)
                     (initial node: OSEventAbstractState) (processed: list Priority),
                     pevent == event_addr(sg, eid) && q_post_group(state, node) != 0 &&
                     mbox_del_loop_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired,
                       eid, observed, initial, state, node, processed, tasks_waiting) *
                     data_at(&pevent->OSEventGrp, unsigned char, q_post_group(state, node))
                     which implies exists (active: TaskResumeCaller) (acquired state: UCOS2_Verify_State)
                     (initial node: OSEventAbstractState) (processed: list Priority) (tid: TaskID) (old: TaskAbstractState),
                     pevent == event_addr(sg, eid) &&
                     mbox_del_loop_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired,
                       eid, observed, initial, state, node, processed, tasks_waiting, tid, old) *
                     event_task_rdy_pre(sg, TskState(state), eid, node, tid, old, 2, 2, q_post_sched_group(state), q_post_sched_rows(state)) */
                 (void)OS_EventTaskRdy(pevent, (void *)0, OS_STAT_MBOX, OS_STAT_PEND_ABORT);
                 /*@ Assert exists (active: TaskResumeCaller) (acquired state: UCOS2_Verify_State)
                     (initial node: OSEventAbstractState) (processed: list Priority) (tid: TaskID) (old: TaskAbstractState) (priority: Z),
                     pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 &&
                     mbox_pend_abort_output_address(error_addr, perr) && opt == choice && choice == 1 &&
                     mbox_del_safe(environment, critical, sg, caller, mask, pe, eid, choice, before, X) &&
                     mbox_del_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, choice, before) &&
                     os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
                       &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
                     &OSEventFreeList == g_OSEventFreeList(sg) &&
                     mbox_del_loop_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired,
                       eid, observed, initial, state, node, processed, tasks_waiting, tid, old) *
                     event_task_rdy_post(sg, TskState(state), eid, node, tid, old, 0, 2, 2, q_post_sched_group(state), q_post_sched_rows(state), priority) *
                     undef_data_at(perr, unsigned char) * undef_data_at(&pevent_return, OS_EVENT*) */
                 /*@ exists (active: TaskResumeCaller) (acquired state: UCOS2_Verify_State)
                     (initial node: OSEventAbstractState) (processed: list Priority) (tid: TaskID) (old: TaskAbstractState) (priority: Z),
                     pevent == event_addr(sg, eid) &&
                     mbox_del_loop_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired,
                       eid, observed, initial, state, node, processed, tasks_waiting, tid, old) *
                     event_task_rdy_post(sg, TskState(state), eid, node, tid, old, 0, 2, 2, q_post_sched_group(state), q_post_sched_rows(state), priority)
                     which implies exists (active: TaskResumeCaller) (acquired next: UCOS2_Verify_State)
                     (initial next_node: OSEventAbstractState) (next_processed: list Priority),
                     pevent == event_addr(sg, eid) &&
                     mbox_del_loop_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired,
                       eid, observed, initial, next, next_node, next_processed, tasks_waiting) *
                     data_at(&pevent->OSEventGrp, unsigned char, q_post_group(next, next_node)) */
             }
#if OS_EVENT_NAME_EN > 0u
             pevent->OSEventName    = (INT8U *)(void *)"?";
#endif
             /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: list Priority),
                 pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && choice == 1 && q_post_group(state, node) == 0 &&
                 &OSEventFreeList == g_OSEventFreeList(sg) &&
                 mbox_del_loop_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, state, node, processed, tasks_waiting) *
                 data_at(&pevent->OSEventGrp, unsigned char, q_post_group(state, node))
                 which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: list Priority),
                 pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 &&
                 &OSEventFreeList == g_OSEventFreeList(sg) &&
                 mbox_del_recycle_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, state, node, processed, tasks_waiting, choice) *
                 data_at(&pevent->OSEventType, unsigned char, 1) * undef_data_at(&pevent->OSEventPtr, void*) *
                 data_at(&pevent->OSEventCnt, unsigned short, q_del_event_count(node)) *
                 data_at(&OSEventFreeList, OS_EVENT*, q_del_event_free_head(sg, state)) */
                 pevent->OSEventType = OS_EVENT_TYPE_UNUSED;
                 pevent->OSEventPtr  = OSEventFreeList;
                 pevent->OSEventCnt  = 0u;
                 OSEventFreeList     = pevent;
                 /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: list Priority),
                 pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 &&
                 &OSEventFreeList == g_OSEventFreeList(sg) &&
                 mbox_del_recycle_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, state, node, processed, tasks_waiting, choice) *
                 data_at(&pevent->OSEventType, unsigned char, 0) *
                 data_at(&pevent->OSEventPtr, void*, q_del_event_free_head(sg, state)) *
                 data_at(&pevent->OSEventCnt, unsigned short, 0) * data_at(&OSEventFreeList, OS_EVENT*, pevent)
                 which implies exists (active: TaskResumeCaller) (acquired released: UCOS2_Verify_State),
                 pevent == pe && tasks_waiting == tasks_waiting &&
                 mbox_del_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr,
                   pe, eid, choice, before, acquired, released, 0, 0, tasks_waiting) */
                 OS_EXIT_CRITICAL();
             if (tasks_waiting == OS_TRUE) {               /* Reschedule only if task(s) were waiting  */
                 /*@ 1 <= tasks_waiting &&
                     mbox_del_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, choice, before) &&
                     mbox_del_restore_post(environment, critical, saved_local, sg, caller, mask, pe, eid, choice, before, 0, 0, tasks_waiting)
                     which implies exists (returned: TaskResumeCaller) (restored: UCOS2_Verify_State),
                     tasks_waiting == tasks_waiting &&
                     mbox_del_prefix_result(environment, critical, sg, caller, mask, pe, eid, choice, before, 0, 0, 1, returned, restored) &&
                     task_resume_sched_pre(environment, critical, saved_local, sg, returned, mask, restored) *
                     q_post_extra_tables(sg, returned) */
                 OS_Sched();                               /* Find highest priority task ready to run  */
                 /*@ exists (returned: TaskResumeCaller) (restored: UCOS2_Verify_State),
                     mbox_del_prefix_result(environment, critical, sg, caller, mask, pe, eid, choice, before, 0, 0, 1, returned, restored) &&
                     task_resume_sched_post(environment, critical, saved_local, sg, returned, mask, restored) *
                     q_post_extra_tables(sg, returned)
                     which implies mbox_del_finish_context(environment, critical, saved_local, sg, caller, mask, pe, eid, choice, before, 0, 0) */
             }
             /*@ Assert
                 pevent == pe && opt == choice &&
                 mbox_pend_abort_output_address(error_addr, perr) &&
                 mbox_del_safe(environment, critical, sg, caller, mask, pe, eid, choice, before, X) &&
                 mbox_del_after_schedule_context(environment, critical, saved_local, sg, caller, mask, pe, eid, choice, before, tasks_waiting) *
                 undef_data_at(perr, unsigned char) * undef_data_at(&pevent_return, OS_EVENT*) *
                 undef_data_at(&cpu_sr, unsigned int) */
             /*@ mbox_del_after_schedule_context(environment, critical, saved_local, sg, caller, mask, pe, eid, choice, before, tasks_waiting)
                 which implies tasks_waiting == tasks_waiting && mbox_del_finish_context(environment, critical, saved_local, sg, caller, mask, pe, eid, choice, before, 0, 0) */
             *perr                  = OS_ERR_NONE;
             pevent_return          = (OS_EVENT *)0;       /* Mailbox has been deleted                   */
             break;

        default:
             /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState),
                 pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && choice != 0 && choice != 1 &&
                 0 <= choice && choice <= 255 &&
                 mbox_del_loop_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired,
                   eid, observed, initial, acquired, initial, nil, tasks_waiting) *
                 data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, initial))
                 which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State),
                 pevent == pe && tasks_waiting == tasks_waiting &&
                 mbox_del_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr,
                   pe, eid, choice, before, acquired, acquired, pe, 7, 0) */
             OS_EXIT_CRITICAL();
             /*@ mbox_del_restore_post(environment, critical, saved_local, sg, caller, mask, pe, eid, choice, before, pe, 7, 0)
                 which implies mbox_del_finish_context(environment, critical, saved_local, sg, caller, mask, pe, eid, choice, before, pe, 7) */
             *perr                  = OS_ERR_INVALID_OPT;
             pevent_return          = pevent;
             break;
    }

    /*@ Assert exists (error: Z),
        pevent == pe && opt == choice &&
        mbox_pend_abort_output_address(error_addr, perr) &&
        mbox_del_safe(environment, critical, sg, caller, mask, pe, eid, choice, before, X) &&
        mbox_del_finish_context(environment, critical, saved_local, sg, caller, mask, pe, eid, choice, before, pevent_return, error) * data_at(perr, unsigned char, error) *
        undef_data_at(&cpu_sr, unsigned int) * undef_data_at(&tasks_waiting, unsigned char) */
    OS_TRACE_MBOX_DEL_EXIT(*perr);

    return (pevent_return);
}
