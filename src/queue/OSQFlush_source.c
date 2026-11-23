/* Annotation carrier only: original pinned headers and selected profile
 * are supplied by the source projection, never by replacement typedefs. */
INT8U OSQFlush(OS_EVENT *pevent)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
    (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
    (mask: Z) (before: UCOS2_Verify_State) (eid: EventID)
    (observed: OSEventAbstractState) (pe: addr) (X: Z -> UCOS2_Verify_State -> Prop)
    Require pevent == pe && q_flush_profile(sg) &&
      q_flush_call_input(critical, sg, invocation, pe, before, eid, observed) &&
      q_flush_api_safe(critical, sg, invocation, pe, before, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
    Ensure exists (after: UCOS2_Verify_State),
      q_flush_api_post(critical, sg, invocation, pe, before, __return, after) &&
      q_flush_return_safe(after, __return, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, after)
*/
{
    OS_Q *pq;
#if OS_CRITICAL_METHOD == 3u
    OS_CPU_SR cpu_sr = 0u;
#endif
#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {
        return (OS_ERR_PEVENT_NULL);
    }
    /*@ pevent == pe && pevent != 0 && q_flush_profile(sg) &&
        q_flush_call_input(critical, sg, invocation, pe, before, eid, observed) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
        which implies
        pevent == pe && pe == event_addr(sg, eid) && valid_event_id(sg, eid) &&
        q_flush_profile(sg) && UCOS2_state_inv(sg, before) &&
        q_flush_public_slot(before, eid, observed) &&
        q_flush_call_input(critical, sg, invocation, pe, before, eid, observed) &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        q_flush_type_frame(sg, before, eid)
    */
    /*@ 0 <= event_slot_type_value(EventState(before), eid) && event_slot_type_value(EventState(before), eid) <= 255 by local */
    if (pevent->OSEventType != OS_EVENT_TYPE_Q) {
        return (OS_ERR_EVENT_TYPE);
    }
#endif
    /*@ UCOS2_state_inv(sg, before) && q_flush_public_slot(before, eid, observed) &&
        q_flush_call_input(critical, sg, invocation, pe, before, eid, observed) &&
        q_flush_profile(sg) && valid_event_id(sg, eid) &&
        pevent == pe && pe == event_addr(sg, eid) && pevent != 0 && event_slot_type_value(EventState(before), eid) == 2 &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        q_flush_type_frame(sg, before, eid)
        which implies
        q_flush_profile(sg) && valid_event_id(sg, eid) &&
        pevent == pe && pe == event_addr(sg, eid) &&
        q_flush_save_pre(platform, critical, sg, invocation, origin, mask, before, eid, observed)
    */
    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        q_flush_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr, before, entry, observed, current) &&
        q_flush_profile(sg) && valid_event_id(sg, eid) && pevent == pe && pe == event_addr(sg, eid) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry)
        which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields),
        pevent == pe && pe == event_addr(sg, eid) &&
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        q_flush_pointer_context(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q)
    */
    pq = (OS_Q *)pevent->OSEventPtr;
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields),
        pq == qcb_addr(sg, qID(q)) && pevent == pe && pe == event_addr(sg, eid) &&
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        q_flush_pointer_context(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q)
        which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields)
          (free: list QueueID) (slots: list (option addr)),
        pevent == pe && pe == event_addr(sg, eid) &&
        data_at(&pq->OSQStart, void **, qStart(q)) * data_at(&pq->OSQIn, void **, queue_in_addr(q)) *
        data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        q_flush_store_context(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, pq)
    */
    pq->OSQIn = pq->OSQStart;
    pq->OSQOut = pq->OSQStart;
    pq->OSQEntries = 0u;
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields)
          (free: list QueueID) (slots: list (option addr)),
        pevent == pe && pe == event_addr(sg, eid) &&
        data_at(&pq->OSQStart, void **, qStart(q)) * data_at(&pq->OSQIn, void **, qStart(q)) *
        data_at(&pq->OSQOut, void **, qStart(q)) * data_at(&pq->OSQEntries, unsigned short, 0) *
        q_flush_store_context(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, pq)
        which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (base: addr),
        pq == base && pevent == pe &&
        q_flush_restore_pre(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current)
    */
    OS_EXIT_CRITICAL();
    return (OS_ERR_NONE);
}
