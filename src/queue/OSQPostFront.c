/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSQPostFront (OS_EVENT  *pevent,
                     void      *pmsg)
/*@ With (environment: TaskStackCallEnvironment) saved_local (critical: CriticalRegionResources)
    (sg: StableGlobVars) (caller: TaskResumeCaller) (mask: Z) (before: UCOS2_Verify_State)
    (eid: EventID) (observed: OSEventAbstractState) (pe message: addr) X
    Require pevent == pe && pmsg == message && q_post_profile(sg) && UCOS2_state_inv(sg, before) &&
      q_post_call_input(critical, sg, caller, pe, before, eid, observed) &&
      q_post_front_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, message, before) &&
      q_post_front_safe(environment, critical, sg, caller, mask, pe, eid, message, before, X) &&
      os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
        &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
      q_post_closed(environment, critical, saved_local, sg, caller, mask, before)
    Ensure q_post_front_post(environment, critical, saved_local, sg, caller, mask, pe, eid, message, before, __return, X)
*/
{
    OS_Q      *pq;
#if OS_CRITICAL_METHOD == 3u                          /* Allocate storage for CPU status register      */
    OS_CPU_SR  cpu_sr = 0u;
#endif



#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {                    /* Validate 'pevent'                             */
        return (OS_ERR_PEVENT_NULL);
    }
#endif

    OS_TRACE_Q_POST_FRONT_ENTER(pevent);

    /*@ pevent == pe && pevent != 0 && q_post_profile(sg) && UCOS2_state_inv(sg, before) &&
        q_post_call_input(critical, sg, caller, pe, before, eid, observed) &&
        q_post_closed(environment, critical, saved_local, sg, caller, mask, before)
        which implies
        pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && valid_event_id(sg, eid) &&
        q_post_profile(sg) && UCOS2_state_inv(sg, before) &&
        q_post_call_input(critical, sg, caller, pe, before, eid, observed) &&
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        q_post_type_context(environment, saved_local, sg, caller, mask, before, eid) */
    /*@ 0 <= event_slot_type_value(EventState(before), eid) && event_slot_type_value(EventState(before), eid) <= 255 by local */
    if (pevent->OSEventType != OS_EVENT_TYPE_Q) {     /* Validate event block type                     */
        OS_TRACE_Q_POST_FRONT_EXIT(OS_ERR_EVENT_TYPE);
        return (OS_ERR_EVENT_TYPE);
    }
    /*@ pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && valid_event_id(sg, eid) &&
        q_post_profile(sg) && UCOS2_state_inv(sg, before) &&
        q_post_call_input(critical, sg, caller, pe, before, eid, observed) &&
        event_slot_type_value(EventState(before), eid) == 2 &&
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        q_post_type_context(environment, saved_local, sg, caller, mask, before, eid)
        which implies pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 &&
        valid_event_id(sg, eid) && q_post_profile(sg) &&
        q_post_save_pre(environment, critical, saved_local, sg, caller, mask, before, pe, eid, observed) */
    OS_ENTER_CRITICAL();
    /*@ pevent == event_addr(sg, eid) && valid_event_id(sg, eid) && q_post_profile(sg) &&
        q_post_save_result(environment, critical, saved_local, sg, caller, mask, cpu_sr, before, eid, observed)
        which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState), pevent == event_addr(sg, eid) &&
        q_post_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current) * data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, current)) */
    if (pevent->OSEventGrp != 0u) {                   /* See if any task pending on queue              */
                                                      /* Ready highest priority task waiting on event  */
        /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState), pevent == event_addr(sg, eid) && q_post_group(acquired, current) != 0 &&
            q_post_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current) * data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, current))
            which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState),
            pevent == event_addr(sg, eid) &&
            q_post_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, tid, old) *
            event_task_rdy_pre(sg, TskState(acquired), eid, current, tid, old, 4, 0,
              q_post_sched_group(acquired), q_post_sched_rows(acquired)) */
        (void)OS_EventTaskRdy(pevent, pmsg, OS_STAT_Q, OS_STAT_PEND_OK);
        /*@ Assert exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState)
            (tid: TaskID) (old: TaskAbstractState) (priority: Z),
            pevent == pe && pevent != 0 && pmsg == message &&
            q_post_front_safe(environment, critical, sg, caller, mask, pe, eid, message, before, X) &&
            q_post_front_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, message, before) &&
            os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
              &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
            has_permission(&pq) *
            q_post_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, tid, old) *
            event_task_rdy_post(sg, TskState(acquired), eid, current, tid, old, message, 4, 0,
              q_post_sched_group(acquired), q_post_sched_rows(acquired), priority) */
        /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState) (priority: Z),
            pevent == pe && pevent != 0 && pmsg == message &&
            q_post_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, tid, old) *
            event_task_rdy_post(sg, TskState(acquired), eid, current, tid, old, message, 4, 0,
              q_post_sched_group(acquired), q_post_sched_rows(acquired), priority)
            which implies exists (active: TaskResumeCaller) (acquired released: UCOS2_Verify_State),
              pevent == pe && pmsg == message &&
              q_post_front_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, eid, message, before, acquired, released, 0, 1) */
        OS_EXIT_CRITICAL();
        /*@ q_post_front_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, message, before) &&
            q_post_front_restore_post(environment, critical, saved_local, sg, caller, mask, pe, eid, message, before, 0, 1)
            which implies exists (returned: TaskResumeCaller) (restored: UCOS2_Verify_State),
            q_post_front_prefix_result(environment, critical, sg, caller, mask, pe, eid, message, before, 0, 1, returned, restored) &&
            task_resume_sched_pre(environment, critical, saved_local, sg, returned, mask, restored) *
            q_post_extra_tables(sg, returned) */
        OS_Sched();                                   /* Find highest priority task ready to run       */
        OS_TRACE_Q_POST_FRONT_EXIT(OS_ERR_NONE);
        return (OS_ERR_NONE);
    }
    /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState), pevent == event_addr(sg, eid) && q_post_group(acquired, current) == 0 &&
        q_post_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current) * data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, current))
        which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields), pevent == event_addr(sg, eid) &&
        q_post_pointer_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q) * data_at(&pevent->OSEventPtr, void *, qcb_addr(sg, qID(q))) */
    pq = (OS_Q *)pevent->OSEventPtr;                  /* Point to queue control block                  */
    /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields), pq == qcb_addr(sg, qID(q)) && pevent == event_addr(sg, eid) &&
        q_post_pointer_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q) * data_at(&pevent->OSEventPtr, void *, qcb_addr(sg, qID(q)))
        which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)),
        pevent == event_addr(sg, eid) &&
        0 <= queue_entries(q) && queue_entries(q) <= 65535 && 0 <= qSize(q) && qSize(q) <= 65535 &&
        q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
        data_at(&pq->OSQStart, void **, qStart(q)) * q_post_front_qcb_readonly(pq, q) * queue_buffer_rep(q, slots) */
    if (pq->OSQEntries >= pq->OSQSize) {              /* Make sure queue is not full                   */
        /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)), pevent == pe && pevent != 0 && queue_entries(q) >= qSize(q) &&
            q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
        data_at(&pq->OSQStart, void **, qStart(q)) * q_post_front_qcb_readonly(pq, q) * queue_buffer_rep(q, slots)
            which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State),
              pevent == pe && pq == pq &&
              q_post_front_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, eid, message, before, acquired, acquired, 30, 0) */
        OS_EXIT_CRITICAL();
        OS_TRACE_Q_POST_FRONT_EXIT(OS_ERR_Q_FULL);
        return (OS_ERR_Q_FULL);
    }
    /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)), queue_entries(q) < qSize(q) &&
        q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
        data_at(&pq->OSQStart, void **, qStart(q)) * q_post_front_qcb_readonly(pq, q) * queue_buffer_rep(q, slots)
        which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)),
        0 <= queue_entries(q) && queue_entries(q) < 65535 &&
        qStart(q) <= q_post_front_next_out(q) && q_post_front_next_out(q) < queue_end_addr(q) &&
        q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
        data_at(&pq->OSQStart, void **, qStart(q)) * q_post_front_qcb_readonly(pq, q) *
        undef_data_at(q_post_front_next_out(q), void *) * q_post_front_slot_frame(q, slots) */
    if (pq->OSQOut == pq->OSQStart) {                 /* Wrap OUT ptr if we are at the 1st queue entry */
        pq->OSQOut = pq->OSQEnd;
    }
    /*@ Assert exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)),
        0 <= queue_entries(q) && queue_entries(q) < 65535 &&
        qStart(q) <= q_post_front_next_out(q) && q_post_front_next_out(q) < queue_end_addr(q) &&
        pevent == pe && pevent != 0 && pmsg == message &&
        q_post_front_next_out(q) == q_post_front_wrapped_out(q) - sizeof(void *) &&
        q_post_front_safe(environment, critical, sg, caller, mask, pe, eid, message, before, X) &&
        q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) *
        data_at(&pq->OSQOut, void **, q_post_front_wrapped_out(q)) *
        data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) *
        data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
        data_at(&pq->OSQStart, void **, qStart(q)) * q_post_front_qcb_readonly(pq, q) *
        undef_data_at(q_post_front_next_out(q), void *) * q_post_front_slot_frame(q, slots) */
    pq->OSQOut--;
    /*@ Assert exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)),
        0 <= queue_entries(q) && queue_entries(q) < 65535 &&
        qStart(q) <= q_post_front_next_out(q) && q_post_front_next_out(q) < queue_end_addr(q) &&
        pevent == pe && pevent != 0 && pmsg == message &&
        q_post_front_safe(environment, critical, sg, caller, mask, pe, eid, message, before, X) &&
        q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) *
        data_at(&pq->OSQOut, void **, q_post_front_next_out(q)) *
        data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) *
        data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
        data_at(&pq->OSQStart, void **, qStart(q)) * q_post_front_qcb_readonly(pq, q) *
        undef_data_at(q_post_front_next_out(q), void *) * q_post_front_slot_frame(q, slots) */
    *pq->OSQOut = pmsg;                               /* Insert message into queue                     */
    pq->OSQEntries++;                                 /* Update the nbr of entries in the queue        */
    /*@ Assert exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)), queue_entries(q) < qSize(q) && pmsg == message && pevent == pe && pevent != 0 &&
        q_post_front_safe(environment, critical, sg, caller, mask, pe, eid, message, before, X) &&
        q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQOut, void **, q_post_front_next_out(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q) + 1) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
        data_at(&pq->OSQStart, void **, qStart(q)) * q_post_front_qcb_readonly(pq, q) *
        data_at(q_post_front_next_out(q), void *, message) * q_post_front_slot_frame(q, slots) */
    /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)), pevent == pe && pevent != 0 && pmsg == message && queue_entries(q) < qSize(q) &&
        q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQOut, void **, q_post_front_next_out(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q) + 1) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
        data_at(&pq->OSQStart, void **, qStart(q)) * q_post_front_qcb_readonly(pq, q) *
        data_at(q_post_front_next_out(q), void *, message) * q_post_front_slot_frame(q, slots)
        which implies exists (active: TaskResumeCaller) (acquired released: UCOS2_Verify_State),
          pevent == pe && pmsg == message && pq == pq &&
          q_post_front_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, eid, message, before, acquired, released, 0, 0) */
    OS_EXIT_CRITICAL();
    OS_TRACE_Q_POST_FRONT_EXIT(OS_ERR_NONE);
    return (OS_ERR_NONE);
}
