/* Annotation carrier for pinned OSQAccept. Actual headers and profile are
 * supplied by the source projection. Postfix normalization is a separate patch. */
void *OSQAccept(OS_EVENT *pevent, INT8U *perr)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
    (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
    (mask: Z) (before: UCOS2_Verify_State) (eid: EventID)
    (observed: OSEventAbstractState) (pe errptr: addr) X
    Require pevent == pe && perr == errptr && q_accept_profile(sg) &&
      q_accept_call_input(critical, sg, invocation, pe, before, eid, observed) &&
      q_accept_api_safe(critical, sg, invocation, pe, before, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) * undef_data_at(perr, unsigned char)
    Ensure exists (after: UCOS2_Verify_State) (error: OSErrCode),
      q_accept_api_post(critical, sg, invocation, pe, before, __return, error, after) &&
      q_accept_return_safe(after, __return, error, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, after) * data_at(errptr, unsigned char, encode_os_err_code(error))
*/
{
    void *pmsg;
    OS_Q *pq;
#if OS_CRITICAL_METHOD == 3u
    OS_CPU_SR cpu_sr = 0u;
#endif
#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return ((void *)0);
    }
#endif
#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {
        *perr = OS_ERR_PEVENT_NULL;
        return ((void *)0);
    }
#endif
    /*@ pevent == pe && pevent != 0 && q_accept_profile(sg) &&
        q_accept_call_input(critical, sg, invocation, pe, before, eid, observed) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
        which implies
        pevent == pe && pevent == event_addr(sg, eid) && valid_event_id(sg, eid) &&
        q_accept_profile(sg) && UCOS2_state_inv(sg, before) &&
        q_query_public_slot(before, eid, observed) &&
        q_accept_call_input(critical, sg, invocation, pe, before, eid, observed) &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        q_accept_type_frame(sg, before, eid) */
    /*@ 0 <= event_slot_type_value(EventState(before), eid) && event_slot_type_value(EventState(before), eid) <= 255 by local */
    if (pevent->OSEventType != OS_EVENT_TYPE_Q) {
        /*@ UCOS2_state_inv(sg, before) && q_accept_profile(sg) && pevent == event_addr(sg, eid) && valid_event_id(sg, eid) &&
            data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
            q_accept_type_frame(sg, before, eid) *
            interrupt_platform_running(platform, invocation, origin, mask)
            which implies pevent == event_addr(sg, eid) &&
              mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) */
        *perr = OS_ERR_EVENT_TYPE;
        return ((void *)0);
    }
    /*@ pevent != 0 && pevent == pe && UCOS2_state_inv(sg, before) && q_accept_profile(sg) &&
        valid_event_id(sg, eid) && pevent == event_addr(sg, eid) &&
        q_query_public_slot(before, eid, observed) &&
        q_accept_call_input(critical, sg, invocation, pe, before, eid, observed) &&
        event_slot_type_value(EventState(before), eid) == 2 &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        q_accept_type_frame(sg, before, eid)
        which implies pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 &&
        valid_event_id(sg, eid) && q_accept_profile(sg) &&
        q_accept_save_pre(platform, critical, sg, invocation, origin, mask, before, eid, observed) */
    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        q_accept_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr, before, entry, observed, current) &&
        q_accept_profile(sg) && valid_event_id(sg, eid) && pevent == event_addr(sg, eid) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry)
        which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields),
        pevent == event_addr(sg, eid) &&
        q_accept_pointer_context(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q) * data_at(&pevent->OSEventPtr, void *, qcb_addr(sg, qID(q))) */
    pq = (OS_Q *)pevent->OSEventPtr;
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields),
        pq == qcb_addr(sg, qID(q)) && pevent == event_addr(sg, eid) &&
        q_accept_pointer_context(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q) * data_at(&pevent->OSEventPtr, void *, qcb_addr(sg, qID(q)))
        which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)),
        pevent == event_addr(sg, eid) && 0 <= queue_entries(q) && queue_entries(q) <= 65535 &&
        q_accept_store_context(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) * data_at(&pq->OSQStart, void **, qStart(q)) * q_accept_qcb_readonly(pq, q) * queue_buffer_rep(q, slots) */
    if (pq->OSQEntries > 0u) {
        /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)), queue_entries(q) > 0 &&
            q_accept_store_context(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) * data_at(&pq->OSQStart, void **, qStart(q)) * q_accept_qcb_readonly(pq, q) * queue_buffer_rep(q, slots)
            which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q next: QueueFields) (free: list QueueID) (slots: list (option addr)) (message: addr),
            0 < queue_entries(q) && queue_entries(q) <= 65535 &&
            q_accept_dequeue_context(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, next, free, slots, pq, message) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) * data_at(&pq->OSQStart, void **, qStart(q)) * q_accept_qcb_readonly(pq, q) *
            data_at(queue_out_addr(q), void *, message) * q_accept_head_slot(q, slots) */
        pmsg = *pq->OSQOut++;
        /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q next: QueueFields) (free: list QueueID) (slots: list (option addr)) (message: addr), pmsg == message &&
            q_accept_dequeue_context(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, next, free, slots, pq, message) * data_at(&pq->OSQOut, void **, queue_out_addr(q) + 4) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) * data_at(&pq->OSQStart, void **, qStart(q)) * q_accept_qcb_readonly(pq, q) *
            data_at(queue_out_addr(q), void *, message) * q_accept_head_slot(q, slots)
            which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q next: QueueFields) (free: list QueueID) (slots: list (option addr)) (message: addr), pmsg == message &&
            0 < queue_entries(q) && queue_entries(q) <= 65535 &&
            q_accept_dequeue_context(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, next, free, slots, pq, message) * data_at(&pq->OSQOut, void **, queue_out_addr(q) + 4) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) * data_at(&pq->OSQStart, void **, qStart(q)) * q_accept_qcb_readonly(pq, q) * queue_buffer_rep(q, slots) */
        pq->OSQEntries--;
        if (pq->OSQOut == pq->OSQEnd) {
            pq->OSQOut = pq->OSQStart;
        }
        /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q next: QueueFields) (free: list QueueID) (slots: list (option addr)) (message: addr), pmsg == message &&
            q_accept_dequeue_context(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, next, free, slots, pq, message) * data_at(&pq->OSQOut, void **, q_accept_next_out(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q) - 1) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) * data_at(&pq->OSQStart, void **, qStart(q)) * q_accept_qcb_readonly(pq, q) * queue_buffer_rep(q, slots)
            which implies exists (entry after: UCOS2_Verify_State) (current: OSEventAbstractState),
            pq == pq && q_accept_restore_pre(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, after, eid, observed, current, pmsg, q_accept_success) */
        *perr = OS_ERR_NONE;
    } else {
        /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)), queue_entries(q) <= 0 &&
            q_accept_store_context(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) * data_at(&pq->OSQStart, void **, qStart(q)) * q_accept_qcb_readonly(pq, q) * queue_buffer_rep(q, slots)
            which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
            pq == pq && q_accept_restore_pre(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, entry, eid, observed, current, 0, q_accept_empty) */
        *perr = OS_ERR_Q_EMPTY;
        pmsg = (void *)0;
    }
    OS_EXIT_CRITICAL();
    return (pmsg);
}
