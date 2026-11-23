/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSQPostOpt (OS_EVENT  *pevent,
                   void      *pmsg,
                   INT8U      opt)
/*@ With (environment: TaskStackCallEnvironment) saved_local (critical: CriticalRegionResources)
    (sg: StableGlobVars) (caller: TaskResumeCaller) (mask: Z) (before: UCOS2_Verify_State)
    (eid: EventID) (observed: OSEventAbstractState) (pe message: addr) (options: Z) X
    Require pevent == pe && pmsg == message && opt == options && q_post_profile(sg) && UCOS2_state_inv(sg, before) &&
      q_post_call_input(critical, sg, caller, pe, before, eid, observed) &&
      q_post_opt_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, message, options, before) &&
      q_post_opt_safe(environment, critical, sg, caller, mask, pe, eid, message, options, before, X) &&
      os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
        &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
      q_post_closed(environment, critical, saved_local, sg, caller, mask, before)
    Ensure q_post_opt_post(environment, critical, saved_local, sg, caller, mask, pe, eid, message, options, before, __return, X)
*/
{
    OS_Q      *pq;
#if OS_CRITICAL_METHOD == 3u
    OS_CPU_SR  cpu_sr = 0u;
#endif
    /*@ 0 <= options && options <= 255 by local */
#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {
        return (OS_ERR_PEVENT_NULL);
    }
#endif
    OS_TRACE_Q_POST_OPT_ENTER(pevent, opt);
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
    if (pevent->OSEventType != OS_EVENT_TYPE_Q) {
        OS_TRACE_Q_POST_OPT_EXIT(OS_ERR_EVENT_TYPE);
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
    if (pevent->OSEventGrp != 0x00u) {
        if ((opt & OS_POST_OPT_BROADCAST) != 0x00u) {
            /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState),
                pevent == event_addr(sg, eid) && q_post_group(acquired, initial) != 0 &&
                q_post_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial) *
                data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, initial))
                which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState),
                pevent == event_addr(sg, eid) &&
                q_post_opt_loop_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, message, state, node) * data_at(&pevent->OSEventGrp, unsigned char, q_post_group(state, node)) */
            /*@ Assert exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState),
                pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && pmsg == message && opt == options &&
                0 <= options && options <= 255 && (options & 1) != 0 &&
                q_post_opt_safe(environment, critical, sg, caller, mask, pe, eid, message, options, before, X) && q_post_opt_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, message, options, before) && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
              &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
                has_permission(&pq) * q_post_opt_loop_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, message, state, node) *
                data_at(&pevent->OSEventGrp, unsigned char, q_post_group(state, node)) */
            /*@ Inv exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState),
                pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && pmsg == message && opt == options &&
                0 <= options && options <= 255 && (options & 1) != 0 &&
                q_post_opt_safe(environment, critical, sg, caller, mask, pe, eid, message, options, before, X) && q_post_opt_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, message, options, before) && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
              &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
                has_permission(&pq) * q_post_opt_loop_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, message, state, node) *
                data_at(&pevent->OSEventGrp, unsigned char, q_post_group(state, node)) */
            while (pevent->OSEventGrp != 0u) {
                /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState),
                    pevent == event_addr(sg, eid) && q_post_group(state, node) != 0 &&
                    q_post_opt_loop_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, message, state, node) * data_at(&pevent->OSEventGrp, unsigned char, q_post_group(state, node))
                    which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState),
                    pevent == event_addr(sg, eid) && q_post_opt_loop_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, message, state, node, tid, old) * event_task_rdy_pre(sg, TskState(state), eid, node, tid, old, 4, 0, q_post_sched_group(state), q_post_sched_rows(state)) */
                (void)OS_EventTaskRdy(pevent, pmsg, OS_STAT_Q, OS_STAT_PEND_OK);
                /*@ Assert exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState) (priority: Z),
                    pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && pmsg == message && opt == options &&
                    0 <= options && options <= 255 && (options & 1) != 0 &&
                    q_post_opt_safe(environment, critical, sg, caller, mask, pe, eid, message, options, before, X) && q_post_opt_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, message, options, before) && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
              &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
                    has_permission(&pq) * q_post_opt_loop_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, message, state, node, tid, old) * event_task_rdy_post(sg, TskState(state), eid, node, tid, old, message, 4, 0, q_post_sched_group(state), q_post_sched_rows(state), priority) */
                /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState) (priority: Z),
                    pevent == event_addr(sg, eid) && pmsg == message && q_post_opt_loop_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, message, state, node, tid, old) * event_task_rdy_post(sg, TskState(state), eid, node, tid, old, message, 4, 0, q_post_sched_group(state), q_post_sched_rows(state), priority)
                    which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState),
                    pevent == event_addr(sg, eid) && pmsg == message &&
                    q_post_opt_loop_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, message, state, node) * data_at(&pevent->OSEventGrp, unsigned char, q_post_group(state, node)) */
            }
            /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState),
                pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && pmsg == message && (options & 1) != 0 && q_post_group(state, node) == 0 &&
                q_post_opt_loop_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, message, state, node) * data_at(&pevent->OSEventGrp, unsigned char, q_post_group(state, node))
                which implies exists (active: TaskResumeCaller) (acquired released: UCOS2_Verify_State),
                pevent == pe && pmsg == message &&
                q_post_opt_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, eid, message, options, before, acquired, released, 0, q_post_opt_schedule_flag(options)) */
        } else {
            /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState),
                pevent == event_addr(sg, eid) && q_post_group(acquired, current) != 0 &&
                q_post_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current) *
                data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, current))
                which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState),
                pevent == event_addr(sg, eid) &&
                q_post_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, tid, old) *
                event_task_rdy_pre(sg, TskState(acquired), eid, current, tid, old, 4, 0, q_post_sched_group(acquired), q_post_sched_rows(acquired)) */
            (void)OS_EventTaskRdy(pevent, pmsg, OS_STAT_Q, OS_STAT_PEND_OK);
            /*@ Assert exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState) (priority: Z),
                pevent == pe && pevent != 0 && pmsg == message && opt == options &&
                0 <= options && options <= 255 && (options & 1) == 0 &&
                q_post_opt_safe(environment, critical, sg, caller, mask, pe, eid, message, options, before, X) && q_post_opt_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, message, options, before) && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
              &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
                has_permission(&pq) *
                q_post_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, tid, old) *
                event_task_rdy_post(sg, TskState(acquired), eid, current, tid, old, message, 4, 0, q_post_sched_group(acquired), q_post_sched_rows(acquired), priority) */
            /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState) (priority: Z),
                pevent == pe && pevent != 0 && pmsg == message && (options & 1) == 0 &&
                q_post_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, tid, old) *
                event_task_rdy_post(sg, TskState(acquired), eid, current, tid, old, message, 4, 0, q_post_sched_group(acquired), q_post_sched_rows(acquired), priority)
                which implies exists (active: TaskResumeCaller) (acquired released: UCOS2_Verify_State),
                pevent == pe && pmsg == message &&
                q_post_opt_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, eid, message, options, before, acquired, released, 0, q_post_opt_schedule_flag(options)) */
        }
        OS_EXIT_CRITICAL();
        if ((opt & OS_POST_OPT_NO_SCHED) == 0u) {
            /*@ (options & 4) == 0 && q_post_opt_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, message, options, before) &&
                q_post_opt_restore_post(environment, critical, saved_local, sg, caller, mask, pe, eid, message, options, before, 0, q_post_opt_schedule_flag(options))
                which implies exists (returned: TaskResumeCaller) (restored: UCOS2_Verify_State),
                q_post_opt_prefix_result(environment, critical, sg, caller, mask, pe, eid, message, options, before, 0, 1, returned, restored) &&
                task_resume_sched_pre(environment, critical, saved_local, sg, returned, mask, restored) * q_post_extra_tables(sg, returned) */
            OS_Sched();
        }
        OS_TRACE_Q_POST_OPT_EXIT(OS_ERR_NONE);
        return (OS_ERR_NONE);
    }
    /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState), pevent == event_addr(sg, eid) && q_post_group(acquired, current) == 0 &&
        q_post_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current) * data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, current))
        which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields), pevent == event_addr(sg, eid) &&
        q_post_pointer_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q) * data_at(&pevent->OSEventPtr, void *, qcb_addr(sg, qID(q))) */
    pq = (OS_Q *)pevent->OSEventPtr;
    /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields), pq == qcb_addr(sg, qID(q)) && pevent == event_addr(sg, eid) &&
        q_post_pointer_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q) * data_at(&pevent->OSEventPtr, void *, qcb_addr(sg, qID(q)))
        which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)),
        pevent == event_addr(sg, eid) &&
        0 <= queue_entries(q) && queue_entries(q) <= 65535 && 0 <= qSize(q) && qSize(q) <= 65535 &&
        q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQIn, void **, queue_in_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
        data_at(&pq->OSQStart, void **, qStart(q)) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * undef_data_at(&pq->OSQPtr, OS_Q *) * queue_buffer_rep(q, slots) */
    if (pq->OSQEntries >= pq->OSQSize) {
        /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)), pevent == pe && pevent != 0 && queue_entries(q) >= qSize(q) &&
            q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQIn, void **, queue_in_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
        data_at(&pq->OSQStart, void **, qStart(q)) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * undef_data_at(&pq->OSQPtr, OS_Q *) * queue_buffer_rep(q, slots)
            which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State),
              pevent == pe && pq == pq &&
              q_post_opt_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, eid, message, options, before, acquired, acquired, 30, 0) */
        OS_EXIT_CRITICAL();
        OS_TRACE_Q_POST_OPT_EXIT(OS_ERR_Q_FULL);
        return (OS_ERR_Q_FULL);
    }

    /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)), queue_entries(q) < qSize(q) &&
        q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQIn, void **, queue_in_addr(q)) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) *
        data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
        data_at(&pq->OSQStart, void **, qStart(q)) * undef_data_at(&pq->OSQPtr, OS_Q *) * queue_buffer_rep(q, slots)
        which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)),
        0 <= queue_entries(q) && queue_entries(q) < 65535 && queue_entries(q) < qSize(q) &&
        queue_in_addr(q) + 4 <= queue_end_addr(q) &&
        qStart(q) <= q_post_opt_next_out(q) && q_post_opt_next_out(q) < queue_end_addr(q) &&
        q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQIn, void **, queue_in_addr(q)) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) *
        data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
        data_at(&pq->OSQStart, void **, qStart(q)) * undef_data_at(&pq->OSQPtr, OS_Q *) * queue_buffer_rep(q, slots) */
    if ((opt & OS_POST_OPT_FRONT) != 0x00u) {
        /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)), queue_entries(q) < qSize(q) &&
            q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQIn, void **, queue_in_addr(q)) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) *
            data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
            data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
            data_at(&pq->OSQStart, void **, qStart(q)) * undef_data_at(&pq->OSQPtr, OS_Q *) * queue_buffer_rep(q, slots)
            which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)),
            q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQIn, void **, queue_in_addr(q)) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) *
            data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
            data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
            data_at(&pq->OSQStart, void **, qStart(q)) * undef_data_at(&pq->OSQPtr, OS_Q *) * undef_data_at(q_post_opt_next_out(q), void *) * q_post_opt_front_slot_frame(q, slots) */
        if (pq->OSQOut == pq->OSQStart) {
            pq->OSQOut = pq->OSQEnd;
        }
        pq->OSQOut--;
        /*@ Assert exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)),
            opt == options && pmsg == message && pevent == pe && pevent != 0 &&
            0 <= options && options <= 255 && (options & 2) != 0 &&
            0 <= queue_entries(q) && queue_entries(q) < 65535 && queue_entries(q) < qSize(q) &&
            q_post_opt_safe(environment, critical, sg, caller, mask, pe, eid, message, options, before, X) && q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQIn, void **, queue_in_addr(q)) * data_at(&pq->OSQOut, void **, q_post_opt_next_out(q)) *
        data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
        data_at(&pq->OSQStart, void **, qStart(q)) * undef_data_at(&pq->OSQPtr, OS_Q *) *
            undef_data_at(q_post_opt_next_out(q), void *) * q_post_opt_front_slot_frame(q, slots) */
        *pq->OSQOut = pmsg;
    } else {
        /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)), queue_entries(q) < qSize(q) &&
            q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQIn, void **, queue_in_addr(q)) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) *
            data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
            data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
            data_at(&pq->OSQStart, void **, qStart(q)) * undef_data_at(&pq->OSQPtr, OS_Q *) * queue_buffer_rep(q, slots)
            which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)),
            q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQIn, void **, queue_in_addr(q)) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) *
            data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
            data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
            data_at(&pq->OSQStart, void **, qStart(q)) * undef_data_at(&pq->OSQPtr, OS_Q *) * undef_data_at(queue_in_addr(q), void *) * q_post_slot_frame(q, slots) */
        *pq->OSQIn++ = pmsg;                          /*      Insert message into queue                */
        if (pq->OSQIn == pq->OSQEnd) {
            pq->OSQIn = pq->OSQStart;
        }
    }
    /*@ Assert exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)),
        opt == options && pmsg == message && pevent == pe && pevent != 0 &&
        0 <= options && options <= 255 && 0 <= queue_entries(q) && queue_entries(q) < 65535 && queue_entries(q) < qSize(q) &&
        q_post_opt_safe(environment, critical, sg, caller, mask, pe, eid, message, options, before, X) && q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQIn, void **, q_post_opt_written_in(options, q)) * data_at(&pq->OSQOut, void **, q_post_opt_written_out(options, q)) *
        data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
        data_at(&pq->OSQStart, void **, qStart(q)) * undef_data_at(&pq->OSQPtr, OS_Q *) *
        q_post_opt_written_buffer(options, q, message, slots) */
    pq->OSQEntries++;
    /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)),
        pevent == pe && pevent != 0 && pmsg == message && queue_entries(q) < qSize(q) &&
        q_post_store_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQIn, void **, q_post_opt_written_in(options, q)) * data_at(&pq->OSQOut, void **, q_post_opt_written_out(options, q)) *
        data_at(&pq->OSQEntries, unsigned short, queue_entries(q) + 1) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
        data_at(&pq->OSQStart, void **, qStart(q)) * undef_data_at(&pq->OSQPtr, OS_Q *) *
        q_post_opt_written_buffer(options, q, message, slots)
        which implies exists (active: TaskResumeCaller) (acquired released: UCOS2_Verify_State),
        pevent == pe && pmsg == message && pq == pq &&
        q_post_opt_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, pe, eid, message, options, before, acquired, released, 0, 0) */
    OS_EXIT_CRITICAL();
    OS_TRACE_Q_POST_OPT_EXIT(OS_ERR_NONE);
    return (OS_ERR_NONE);
}
