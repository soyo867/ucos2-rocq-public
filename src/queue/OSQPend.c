/* OSQPend single-function carrier for pinned uC/OS-II V2.93.01.
 * The companion environment supplies the actual headers and callee contracts.
 * No executable source statement is changed by these annotations. */
void  *OSQPend (OS_EVENT  *pevent,
                INT32U     timeout,
                INT8U     *perr)
/*@ With (external: OsSchedExternalResources) (platform: InterruptPlatformResources)
         (critical: CriticalRegionResources) (sg: StableGlobVars) (context: OsSchedCallContext)
         (environment: option TaskStackCallEnvironment) saved_local
         (mask: Z) (before: UCOS2_Verify_State) (eid: EventID)
         (observed: OSEventAbstractState) (pe pd ticks: Z) X
    Require pevent == pe && timeout == ticks && perr == pd &&
      &OSTCBCur == sg.g_OSTCBCur &&
      sem_pend_profile(sg) && q_accept_profile(sg) &&
      kernel_tcb_stack_field_layout(sg) &&
      q_pend_api_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed) &&
      q_pend_api_admission(environment, critical, sg, context, pe, before, eid) &&
      q_pend_api_safe(external, environment, critical, sg, context, pe, eid, ticks, mask, before, X) &&
      sem_pend_continuation_save_input(external, platform, environment, critical, saved_local, sg, context, mask, before) *
      unmap_table_rep(sg) * undef_data_at(perr, unsigned char) &&
      (pe == 0 || (pe != 0 && event_object_layout_prop(sg, eid) &&
        event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt))) &&
      os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
        &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl)
    Ensure q_pend_api_post(external, platform, environment, critical, saved_local, sg, context,
      mask, pe, eid, ticks, pd, before, __return, X)
*/
{
    void      *pmsg;
    OS_Q      *pq;
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif


#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return ((void *)0);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {               /* Validate 'pevent'                                  */
        *perr = OS_ERR_PEVENT_NULL;
        return ((void *)0);
    }
#endif

    OS_TRACE_Q_PEND_ENTER(pevent, timeout);

    /*@ q_pend_api_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed) &&
        pevent == pe && pe != 0 &&
        event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt) &&
        sem_pend_continuation_save_input(external, platform, environment, critical, saved_local, sg, context, mask, before)
        which implies
        event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt) &&
        q_pend_api_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed) &&
        pevent == pe && pe == event_addr(sg, eid) && valid_event_id(sg, eid) &&
        q_query_public_slot(before, eid, observed) && UCOS2_state_inv(sg, before) &&
        interrupt_platform_running(platform, os_sched_call_invocation(context), os_sched_call_origin(context), mask) *
        os_sched_context_resources(external, context) *
        sem_pend_optional_continuation_resources(external, platform, environment, saved_local, context, before) *
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(before.EventState, eid)) *
        sem_query_type_frame(sg, before, eid)
    */
    /*@ 0 <= event_slot_type_value(before.EventState, eid) && event_slot_type_value(before.EventState, eid) <= 255 by local */
    if (pevent->OSEventType != OS_EVENT_TYPE_Q) {/* Validate event block type                          */
        *perr = OS_ERR_EVENT_TYPE;
        OS_TRACE_Q_PEND_EXIT(*perr);
        return ((void *)0);
    }
    /*@ pevent == pe && UCOS2_state_inv(sg, before) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
          &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt) &&
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(before.EventState, eid)) *
        sem_query_type_frame(sg, before, eid)
        which implies
        pevent == pe &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
          &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt) && UCOS2_state_inv(sg, before) &&
        data_at(&OSIntNesting, unsigned char, before.IntrState.intNesting) *
        data_at(&OSLockNesting, unsigned char, before.IntrState.lockNesting) * sem_pend_interrupt_frame(sg, before)
    */
    /*@ 0 <= before.IntrState.intNesting && before.IntrState.intNesting <= 255 by local */
    if (OSIntNesting > 0u) {                     /* See if called from ISR ...                         */
        *perr = OS_ERR_PEND_ISR;                 /* ... can't PEND from an ISR                         */
        OS_TRACE_Q_PEND_EXIT(*perr);
        return ((void *)0);
    }
    /*@ 0 <= before.IntrState.lockNesting && before.IntrState.lockNesting <= 255 by local */
    if (OSLockNesting > 0u) {                    /* See if called with scheduler locked ...            */
        *perr = OS_ERR_PEND_LOCKED;              /* ... can't PEND when locked                         */
        OS_TRACE_Q_PEND_EXIT(*perr);
        return ((void *)0);
    }
    /*@ UCOS2_state_inv(sg, before) &&
        q_pend_api_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed) &&
        q_pend_api_admission(environment, critical, sg, context, pe, before, eid) &&
        pe != 0 && event_slot_type_value(before.EventState, eid) == 2 &&
        before.IntrState.intNesting <= 0 && before.IntrState.lockNesting <= 0 &&
        interrupt_platform_running(platform, os_sched_call_invocation(context), os_sched_call_origin(context), mask) *
        os_sched_context_resources(external, context) *
        sem_pend_optional_continuation_resources(external, platform, environment, saved_local, context, before) *
        data_at(&OSIntNesting, unsigned char, before.IntrState.intNesting) *
        data_at(&OSLockNesting, unsigned char, before.IntrState.lockNesting) * sem_pend_interrupt_frame(sg, before) *
        unmap_table_rep(sg) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
          &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl)
        which implies os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr,
          OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && q_pend_api_prefix(pe, before, eid) &&
        q_pend_save_input(QueuePendAcquirePhase(pe, eid, observed), external, platform, environment,
          critical, saved_local, sg, context, mask, before)
    */
    OS_ENTER_CRITICAL();
    /*@ q_pend_save_output(QueuePendAcquirePhase(pe, eid, observed), external, platform, environment,
          critical, saved_local, sg, context, mask, cpu_sr, before) &&
        q_accept_profile(sg) && valid_event_id(sg, eid) &&
        pevent == event_addr(sg, eid)
        which implies exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State)
          (current: OSEventAbstractState) (q: QueueFields),
        pevent == event_addr(sg, eid) &&
        q_pend_first_owner(external, platform, environment, critical, saved_local, sg, context, entered,
          mask, cpu_sr, pe, before, entry, eid, observed) *
        q_accept_pointer_context(platform, critical, sg, os_sched_call_invocation(context),
          os_sched_call_origin(context), mask, cpu_sr, before, entry, eid, observed, current, q) *
        data_at(&pevent->OSEventPtr, void *, qcb_addr(sg, qID(q)))
    */
    pq = (OS_Q *)pevent->OSEventPtr;             /* Point at queue control block                       */
    /*@ exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields),
        pq == qcb_addr(sg, qID(q)) && pevent == event_addr(sg, eid) &&
        q_pend_first_owner(external, platform, environment, critical, saved_local, sg, context, entered,
            mask, cpu_sr, pe, before, entry, eid, observed) *
            q_accept_pointer_context(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, cpu_sr, before, entry, eid, observed, current, q) * data_at(&pevent->OSEventPtr, void *, qcb_addr(sg, qID(q)))
        which implies exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)),
        pevent == event_addr(sg, eid) && 0 <= queue_entries(q) && queue_entries(q) <= 65535 &&
        q_pend_first_owner(external, platform, environment, critical, saved_local, sg, context, entered,
            mask, cpu_sr, pe, before, entry, eid, observed) *
            q_accept_store_context(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) * data_at(&pq->OSQStart, void **, qStart(q)) * q_accept_qcb_readonly(pq, q) * queue_buffer_rep(q, slots) */
    if (pq->OSQEntries > 0u) {                   /* See if any messages in the queue                   */
    /*@ exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)), queue_entries(q) > 0 &&
            q_pend_first_owner(external, platform, environment, critical, saved_local, sg, context, entered,
            mask, cpu_sr, pe, before, entry, eid, observed) *
            q_accept_store_context(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, pq) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) * data_at(&pq->OSQStart, void **, qStart(q)) * q_accept_qcb_readonly(pq, q) * queue_buffer_rep(q, slots)
            which implies exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q next: QueueFields) (free: list QueueID) (slots: list (option addr)) (message: addr),
            0 < queue_entries(q) && queue_entries(q) <= 65535 &&
            q_pend_first_owner(external, platform, environment, critical, saved_local, sg, context, entered,
            mask, cpu_sr, pe, before, entry, eid, observed) *
            q_accept_dequeue_context(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, cpu_sr, before, entry, eid, observed, current, q, next, free, slots, pq, message) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) * data_at(&pq->OSQStart, void **, qStart(q)) * q_accept_qcb_readonly(pq, q) *
            data_at(queue_out_addr(q), void *, message) * q_accept_head_slot(q, slots) */
        pmsg = *pq->OSQOut++;                    /* Yes, extract oldest message from the queue         */
    /*@ exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q next: QueueFields) (free: list QueueID) (slots: list (option addr)) (message: addr), pmsg == message &&
            q_pend_first_owner(external, platform, environment, critical, saved_local, sg, context, entered,
            mask, cpu_sr, pe, before, entry, eid, observed) *
            q_accept_dequeue_context(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, cpu_sr, before, entry, eid, observed, current, q, next, free, slots, pq, message) * data_at(&pq->OSQOut, void **, queue_out_addr(q) + 4) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) * data_at(&pq->OSQStart, void **, qStart(q)) * q_accept_qcb_readonly(pq, q) *
            data_at(queue_out_addr(q), void *, message) * q_accept_head_slot(q, slots)
            which implies exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q next: QueueFields) (free: list QueueID) (slots: list (option addr)) (message: addr), pmsg == message &&
            0 < queue_entries(q) && queue_entries(q) <= 65535 &&
            q_pend_first_owner(external, platform, environment, critical, saved_local, sg, context, entered,
            mask, cpu_sr, pe, before, entry, eid, observed) *
            q_accept_dequeue_context(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, cpu_sr, before, entry, eid, observed, current, q, next, free, slots, pq, message) * data_at(&pq->OSQOut, void **, queue_out_addr(q) + 4) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) * data_at(&pq->OSQEnd, void **, queue_end_addr(q)) * data_at(&pq->OSQStart, void **, qStart(q)) * q_accept_qcb_readonly(pq, q) * queue_buffer_rep(q, slots) */
        pq->OSQEntries--;                        /* Update the number of entries in the queue          */
        if (pq->OSQOut == pq->OSQEnd) {          /* Wrap OUT pointer if we are at the end of the queue */
            pq->OSQOut = pq->OSQStart;
        }
        /*@ exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State)
          (current: OSEventAbstractState) (q next: QueueFields) (free: list QueueID)
          (slots: list (option addr)) (message: addr), pmsg == message &&
          q_pend_first_owner(external, platform, environment, critical, saved_local, sg, context, entered,
            mask, cpu_sr, pe, before, entry, eid, observed) *
          q_accept_dequeue_context(platform, critical, sg, os_sched_call_invocation(context),
            os_sched_call_origin(context), mask, cpu_sr, before, entry, eid, observed, current,
            q, next, free, slots, pq, message) *
          data_at(&pq->OSQOut, void **, q_accept_next_out(q)) *
          data_at(&pq->OSQEntries, unsigned short, queue_entries(q) - 1) *
          data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
          data_at(&pq->OSQStart, void **, qStart(q)) * q_accept_qcb_readonly(pq, q) * queue_buffer_rep(q, slots)
          which implies exists (entered: OsSchedCallContext) (entry checkpoint: UCOS2_Verify_State),
          pq == pq &&
          q_pend_immediate_checkpoint(external, environment, critical, sg, context, before,
            entered, entry, eid, ticks, pmsg, checkpoint) &&
          q_pend_restore_input(None, external, platform, environment, critical, saved_local,
            sg, entered, mask, cpu_sr, entry, checkpoint)
        */
        OS_EXIT_CRITICAL();
        *perr = OS_ERR_NONE;
        OS_TRACE_Q_PEND_EXIT(*perr);
        return (pmsg);                           /* Return message received                            */
    }
    /*@ exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State)
        (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)),
        queue_entries(q) <= 0 && timeout == ticks &&
        q_pend_first_owner(external, platform, environment, critical, saved_local, sg, context, entered,
          mask, cpu_sr, pe, before, entry, eid, observed) *
        q_accept_store_context(platform, critical, sg, os_sched_call_invocation(context),
          os_sched_call_origin(context), mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, pq) *
        data_at(&pq->OSQOut, void **, queue_out_addr(q)) *
        data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQEnd, void **, queue_end_addr(q)) *
        data_at(&pq->OSQStart, void **, qStart(q)) * q_accept_qcb_readonly(pq, q) * queue_buffer_rep(q, slots) &&
        event_object_layout_prop(sg, eid) &&
        &OSTCBCur == sg.g_OSTCBCur
        which implies exists (owned: TaskStackCallEnvironment) (entered: OsSchedCallContext)
          (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState),
        pq == pq && timeout == ticks &&
        environment == Some(owned) && external == task_stack_call_external(owned) &&
        platform == task_stack_call_platform(owned) && &OSTCBCur == sg.g_OSTCBCur &&
        q_pend_empty_snapshot(external, environment, critical, sg, context, entered,
          mask, cpu_sr, pe, before, entry, eid, observed, current, tid, old) &&
        q_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
          entered, cpu_sr, entry, entry) *
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBStat, unsigned char, encode_task_status(old.stat)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBStatPend, unsigned char, encode_pend_status(old.statPend)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBDly, unsigned int, old.dly) *
        sem_pend_prefix_frame(sg, entry, tid, old)
    */
    /*@ 0 <= OSTCBCur->OSTCBStat && OSTCBCur->OSTCBStat <= 255 by local */
    OSTCBCur->OSTCBStat     |= OS_STAT_Q;        /* Task will have to pend for a message to be posted  */
    OSTCBCur->OSTCBStatPend  = OS_STAT_PEND_OK;
    OSTCBCur->OSTCBDly       = timeout;          /* Load timeout into TCB                              */
    /*@ exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State)
        (current: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState),
        q_pend_empty_snapshot(external, environment, critical, sg, context, entered,
          mask, cpu_sr, pe, before, entry, eid, observed, current, tid, old) &&
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBStat, unsigned char, encode_task_status(old.stat) | 4) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBStatPend, unsigned char, 0) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBDly, unsigned int, timeout) *
        sem_pend_prefix_frame(sg, entry, tid, old) &&
        timeout == ticks && &OSTCBCur == sg.g_OSTCBCur && pevent == event_addr(sg, eid)
        which implies
        timeout == ticks &&
        q_pend_empty_snapshot(external, environment, critical, sg, context, entered,
          mask, cpu_sr, pe, before, entry, eid, observed, current, tid, old) &&
        q_pend_wait_entry(sg, entry, eid, current, tid, old) &&
        pevent == event_addr(sg, eid) && q_pend_wait_call_pre(sg, entry, eid, current, tid, old, ticks)
    */
    OS_EventTaskWait(pevent);                    /* Suspend task until event or timeout occurs         */
    /*@ exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State)
        (current: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState),
        q_pend_empty_snapshot(external, environment, critical, sg, context, entered,
          mask, cpu_sr, pe, before, entry, eid, observed, current, tid, old) &&
        kernel_tcb_stack_field_layout(sg) &&
        q_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
          entered, cpu_sr, entry, entry) * q_pend_wait_call_post(sg, entry, eid, current, tid, old, ticks)
        which implies exists (waiting: UCOS2_Verify_State),
        q_pend_first_wait_checkpoint(external, environment, critical, sg, context,
          before, entered, entry, eid, ticks, waiting) &&
        q_pend_restore_input(Some(QueuePendWaitPhase(context, mask, entry, current, eid, ticks, waiting)),
          external, platform, environment, critical, saved_local, sg, entered, mask, cpu_sr, entry, waiting)
    */
    OS_EXIT_CRITICAL();
    /*@ exists (entered: OsSchedCallContext) (entry waiting: UCOS2_Verify_State)
        (current: OSEventAbstractState),
        q_pend_first_wait_checkpoint(external, environment, critical, sg, context,
          before, entered, entry, eid, ticks, waiting) &&
        q_pend_restore_output(Some(QueuePendWaitPhase(context, mask, entry, current, eid, ticks, waiting)),
          external, platform, environment, critical, saved_local, sg, entered, mask, waiting)
        which implies exists (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State),
        q_pend_scheduling_checkpoint(external, environment, critical, sg, context,
          before, entry, eid, ticks, waiting, released, unmasked) &&
        q_pend_sched_admitted(environment, critical) &&
        q_pend_continuation_phase_sched_input(QueuePendWaitPhase(context, mask, entry, current, eid, ticks, waiting),
          external, platform, environment, critical, saved_local, sg, released, mask, unmasked)
    */
    OS_Sched();                                  /* Find next highest priority task ready to run       */
    /*@ exists (released: OsSchedCallContext) (entry waiting unmasked: UCOS2_Verify_State)
        (current: OSEventAbstractState),
        q_pend_scheduling_checkpoint(external, environment, critical, sg, context,
          before, entry, eid, ticks, waiting, released, unmasked) &&
        q_pend_sched_admitted(environment, critical) &&
        q_pend_continuation_phase_sched_output(QueuePendWaitPhase(context, mask, entry, current, eid, ticks, waiting),
          external, platform, environment, critical, saved_local, sg, released, mask, unmasked)
        which implies exists (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State),
        q_pend_scheduled_checkpoint(external, environment, critical, sg, context,
          before, eid, ticks, scheduled, selected) &&
        q_pend_save_input(QueuePendResumePhase(QueuePendWaitPhase(context, mask, entry, current, eid, ticks, waiting)),
          external, platform, environment, critical, saved_local, sg, scheduled, mask, selected)
    */
    OS_ENTER_CRITICAL();
    /*@ exists (entry waiting selected: UCOS2_Verify_State) (current: OSEventAbstractState)
        (scheduled: OsSchedCallContext),
        q_pend_scheduled_checkpoint(external, environment, critical, sg, context,
          before, eid, ticks, scheduled, selected) &&
        q_pend_save_output(QueuePendResumePhase(QueuePendWaitPhase(context, mask, entry, current, eid, ticks, waiting)),
          external, platform, environment, critical, saved_local, sg, scheduled, mask, cpu_sr, selected) &&
        &OSTCBCur == sg.g_OSTCBCur
        which implies exists (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State)
          (resume_tid: TaskID) (node: TaskAbstractState),
        q_pend_resume_checkpoint(external, environment, critical, sg, context,
          before, eid, ticks, resumed, resume_entry) &&
        interrupt_saved_value(mask, cpu_sr) &&
        sem_pend_resume_entry(sg, resume_entry, eid, resume_tid, node) &&
        q_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
          resumed, cpu_sr, resume_entry, resume_entry) *
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStat, unsigned char, encode_task_status(node.stat)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStatPend, unsigned char, encode_pend_status(node.statPend)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBEventPtr, OS_EVENT *, encode_event_link(sg, node.eventPtr)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBMsg, void *, encode_msg(node.msg)) *
        q_pend_cleanup_frame(sg, resume_entry, resume_tid, node)
    */
    switch (OSTCBCur->OSTCBStatPend) {                /* See if we timed-out or aborted                */
        case OS_STAT_PEND_OK:                         /* Extract message from TCB (Put there by QPost) */
             pmsg =  OSTCBCur->OSTCBMsg;
            *perr =  OS_ERR_NONE;
             break;

        case OS_STAT_PEND_ABORT:
             pmsg = (void *)0;
            *perr =  OS_ERR_PEND_ABORT;               /* Indicate that we aborted                      */
             break;

        case OS_STAT_PEND_TO:
        default:
             /*@ exists (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State)
                 (resume_tid: TaskID) (node: TaskAbstractState),
                 sem_pend_resume_entry(sg, resume_entry, eid, resume_tid, node) &&
                 encode_pend_status(node.statPend) != 0 && encode_pend_status(node.statPend) != 2 &&
                 event_object_layout_prop(sg, eid) &&
                 q_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
                   resumed, cpu_sr, resume_entry, resume_entry) *
                 data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStat, unsigned char, encode_task_status(node.stat)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStatPend, unsigned char, encode_pend_status(node.statPend)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBEventPtr, OS_EVENT *, encode_event_link(sg, node.eventPtr)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBMsg, void *, encode_msg(node.msg)) *
                 q_pend_cleanup_frame(sg, resume_entry, resume_tid, node) && &OSTCBCur == sg.g_OSTCBCur
                 which implies exists (current: OSEventAbstractState),
                 sem_pend_resume_entry(sg, resume_entry, eid, resume_tid, node) &&
                 node.statPend == PendTimeout && mutex_query_lookup(resume_entry, eid, current) &&
                 event_object_layout_prop(sg, eid) && &OSTCBCur == sg.g_OSTCBCur &&
                 q_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
                   resumed, cpu_sr, resume_entry, resume_entry) *
                 data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
                 event_task_remove_pre(task_slot_addr(sg, resume_tid),
                   &((OS_EVENT *)event_addr(sg, eid))->OSEventGrp,
                   &((OS_EVENT *)event_addr(sg, eid))->OSEventTbl[0],
                   node.curPrio / 8, tcb_bit_x_of_prio(node.curPrio), tcb_bit_y_of_prio(node.curPrio),
                   encode_event_wait_tbl_at_or(current.waitList, resume_entry.TskState, node.curPrio / 8),
                   encode_event_wait_grp(current.waitList, resume_entry.TskState)) *
                 sem_pend_remove_call_frame(sg, resume_entry, eid, current, resume_tid, node) */
             OS_EventTaskRemove(OSTCBCur, pevent);
             /*@ exists (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State)
                 (resume_tid: TaskID) (node: TaskAbstractState) (current: OSEventAbstractState),
                 sem_pend_resume_entry(sg, resume_entry, eid, resume_tid, node) &&
                 node.statPend == PendTimeout && mutex_query_lookup(resume_entry, eid, current) &&
                 event_object_layout_prop(sg, eid) && &OSTCBCur == sg.g_OSTCBCur &&
                 q_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
                   resumed, cpu_sr, resume_entry, resume_entry) *
                 data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
                 event_task_remove_post(task_slot_addr(sg, resume_tid),
                   &((OS_EVENT *)event_addr(sg, eid))->OSEventGrp,
                   &((OS_EVENT *)event_addr(sg, eid))->OSEventTbl[0],
                   node.curPrio / 8, tcb_bit_x_of_prio(node.curPrio), tcb_bit_y_of_prio(node.curPrio),
                   encode_event_wait_tbl_at_or(current.waitList, resume_entry.TskState, node.curPrio / 8),
                   encode_event_wait_grp(current.waitList, resume_entry.TskState)) *
                 sem_pend_remove_call_frame(sg, resume_entry, eid, current, resume_tid, node)
                 which implies exists (cleaning: UCOS2_Verify_State) (cleaned_node: TaskAbstractState),
                 q_pend_cleanup_observation(sg, resume_entry, eid, 0, 10, cleaning, resume_tid, cleaned_node) &&
                 &OSTCBCur == sg.g_OSTCBCur &&
                 q_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
                   resumed, cpu_sr, resume_entry, cleaning) *
                 data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStat, unsigned char, encode_task_status(cleaned_node.stat)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStatPend, unsigned char, encode_pend_status(cleaned_node.statPend)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBEventPtr, OS_EVENT *, encode_event_link(sg, cleaned_node.eventPtr)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBMsg, void *, encode_msg(cleaned_node.msg)) *
                 q_pend_cleanup_frame(sg, cleaning, resume_tid, cleaned_node)
             */
             pmsg = (void *)0;
            *perr =  OS_ERR_TIMEOUT;                  /* Indicate that we didn't get event within TO   */
             break;
    }
    /*@ Assert exists (resumed: OsSchedCallContext) (resume_entry cleaning: UCOS2_Verify_State)
        (resume_tid: TaskID) (node: TaskAbstractState) (code: Z),
        pq == pq && pevent == pevent && timeout == timeout && perr == pd &&
        q_pend_api_safe(external, environment, critical, sg, context, pe, eid, ticks, mask, before, X) &&
        q_pend_api_prefix(pe, before, eid) &&
        q_pend_resume_checkpoint(external, environment, critical, sg, context,
          before, eid, ticks, resumed, resume_entry) &&
        q_pend_cleanup_observation(sg, resume_entry, eid, pmsg, code, cleaning, resume_tid, node) &&
        interrupt_saved_value(mask, cpu_sr) && &OSTCBCur == sg.g_OSTCBCur &&
        q_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
          resumed, cpu_sr, resume_entry, cleaning) * data_at(perr, unsigned char, code) *
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStat, unsigned char, encode_task_status(node.stat)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStatPend, unsigned char, encode_pend_status(node.statPend)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBEventPtr, OS_EVENT *, encode_event_link(sg, node.eventPtr)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBMsg, void *, encode_msg(node.msg)) *
        q_pend_cleanup_frame(sg, cleaning, resume_tid, node)
    */
    OSTCBCur->OSTCBStat          =  OS_STAT_RDY;      /* Set   task  status to ready                   */
    OSTCBCur->OSTCBStatPend      =  OS_STAT_PEND_OK;  /* Clear pend  status                            */
    OSTCBCur->OSTCBEventPtr      = (OS_EVENT  *)0;    /* Clear event pointers                          */
#if (OS_EVENT_MULTI_EN > 0u)
    OSTCBCur->OSTCBEventMultiPtr = (OS_EVENT **)0;
    OSTCBCur->OSTCBEventMultiRdy = (OS_EVENT  *)0;
#endif
    OSTCBCur->OSTCBMsg           = (void      *)0;    /* Clear  received message                       */
    /*@ exists (resumed: OsSchedCallContext) (resume_entry cleaning: UCOS2_Verify_State)
        (resume_tid: TaskID) (node: TaskAbstractState) (code: Z),
        q_pend_cleanup_observation(sg, resume_entry, eid, pmsg, code, cleaning, resume_tid, node) &&
        interrupt_saved_value(mask, cpu_sr) &&
        q_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
          resumed, cpu_sr, resume_entry, cleaning) * data_at(perr, unsigned char, code) *
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStat, unsigned char, 0) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStatPend, unsigned char, 0) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBEventPtr, OS_EVENT *, 0) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBMsg, void *, 0) *
        q_pend_cleanup_frame(sg, cleaning, resume_tid, node) && &OSTCBCur == sg.g_OSTCBCur
        which implies exists (checkpoint: UCOS2_Verify_State),
        q_pend_resume_result(sg, eid, resume_entry, pmsg, code, checkpoint) &&
        q_pend_restore_input(None, external, platform, environment, critical, saved_local,
          sg, resumed, mask, cpu_sr, resume_entry, checkpoint) * data_at(perr, unsigned char, code)
    */
    OS_EXIT_CRITICAL();
    OS_TRACE_Q_PEND_EXIT(*perr);

    return (pmsg);                                    /* Return received message                       */
}
