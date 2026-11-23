/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  *OSMboxPend (OS_EVENT  *pevent,
                INT32U     timeout,
                INT8U     *perr)
/*@ With (external: OsSchedExternalResources) (platform: InterruptPlatformResources)
         (critical: CriticalRegionResources) (sg: StableGlobVars) (context: OsSchedCallContext)
         (environment: option TaskStackCallEnvironment) saved_local
         (mask: Z) (before: UCOS2_Verify_State) (eid: EventID)
         (observed: OSEventAbstractState) (pe pd ticks: Z) X
    Require pevent == pe && timeout == ticks && perr == pd &&
      &OSTCBCur == sg.g_OSTCBCur &&
      sem_pend_profile(sg) && mbox_accept_profile(sg) &&
      kernel_tcb_stack_field_layout(sg) &&
      mbox_pend_api_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed) &&
      mbox_pend_api_admission(environment, critical, sg, context, pe, before, eid) &&
      mbox_pend_api_safe(external, environment, critical, sg, context, pe, eid, ticks, mask, before, X) &&
      sem_pend_continuation_save_input(external, platform, environment, critical, saved_local, sg, context, mask, before) *
      unmap_table_rep(sg) * undef_data_at(perr, unsigned char) &&
      (pe == 0 || (pe != 0 && event_object_layout_prop(sg, eid) &&
        event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt))) &&
      os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
        &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl)
    Ensure mbox_pend_api_post(external, platform, environment, critical, saved_local, sg, context,
      mask, pe, eid, ticks, pd, before, __return, X)
*/
{
    void      *pmsg;
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

    OS_TRACE_MBOX_PEND_ENTER(pevent, timeout);

    /*@ mbox_pend_api_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed) &&
        pevent == pe && pe != 0 &&
        event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt) &&
        sem_pend_continuation_save_input(external, platform, environment, critical, saved_local, sg, context, mask, before)
        which implies
        event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt) &&
        mbox_pend_api_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed) &&
        pevent == pe && pe == event_addr(sg, eid) && valid_event_id(sg, eid) &&
        q_query_public_slot(before, eid, observed) && UCOS2_state_inv(sg, before) &&
        interrupt_platform_running(platform, os_sched_call_invocation(context), os_sched_call_origin(context), mask) *
        os_sched_context_resources(external, context) *
        sem_pend_optional_continuation_resources(external, platform, environment, saved_local, context, before) *
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(before.EventState, eid)) *
        sem_query_type_frame(sg, before, eid)
    */
    /*@ 0 <= event_slot_type_value(before.EventState, eid) && event_slot_type_value(before.EventState, eid) <= 255 by local */
    if (pevent->OSEventType != OS_EVENT_TYPE_MBOX) {/* Validate event block type                          */
        *perr = OS_ERR_EVENT_TYPE;
        OS_TRACE_MBOX_PEND_EXIT(*perr);
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
        OS_TRACE_MBOX_PEND_EXIT(*perr);
        return ((void *)0);
    }
    /*@ 0 <= before.IntrState.lockNesting && before.IntrState.lockNesting <= 255 by local */
    if (OSLockNesting > 0u) {                    /* See if called with scheduler locked ...            */
        *perr = OS_ERR_PEND_LOCKED;              /* ... can't PEND when locked                         */
        OS_TRACE_MBOX_PEND_EXIT(*perr);
        return ((void *)0);
    }
    /*@ UCOS2_state_inv(sg, before) &&
        mbox_pend_api_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed) &&
        mbox_pend_api_admission(environment, critical, sg, context, pe, before, eid) &&
        pe != 0 && event_slot_type_value(before.EventState, eid) == 1 &&
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
          OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && mbox_pend_api_prefix(pe, before, eid) &&
        mbox_pend_save_input(MboxPendAcquirePhase(pe, eid, observed), external, platform, environment,
          critical, saved_local, sg, context, mask, before)
    */
    OS_ENTER_CRITICAL();
    /*@ mbox_pend_save_output(MboxPendAcquirePhase(pe, eid, observed), external, platform, environment,
          critical, saved_local, sg, context, mask, cpu_sr, before) &&
        mbox_accept_profile(sg) && valid_event_id(sg, eid) &&
        event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt) &&
        pevent == event_addr(sg, eid)
        which implies exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State)
          (current: OSEventAbstractState) (mailbox: MboxFields),
        pevent == event_addr(sg, eid) &&
        mbox_pend_message_frame(external, platform, environment, critical, saved_local, sg, context, entered,
          mask, cpu_sr, pe, before, entry, eid, observed, current, mailbox) *
        data_at(&pevent->OSEventPtr, void *, mbox_message_ptr(mailbox))
    */
    pmsg = pevent->OSEventPtr;
    if (pmsg != (void *)0) {                          /* See if there is already a message             */
        pevent->OSEventPtr = (void *)0;               /* Clear the mailbox                             */
        /*@ exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State)
          (current: OSEventAbstractState) (mailbox: MboxFields),
          pmsg == mbox_message_ptr(mailbox) && pmsg != 0 &&
          pevent == event_addr(sg, eid) && mbox_accept_profile(sg) &&
          mbox_pend_message_frame(external, platform, environment, critical, saved_local, sg, context, entered,
            mask, cpu_sr, pe, before, entry, eid, observed, current, mailbox) *
          data_at(&pevent->OSEventPtr, void *, 0)
          which implies exists (entered: OsSchedCallContext) (entry checkpoint: UCOS2_Verify_State),
          pevent == event_addr(sg, eid) &&
          mbox_pend_immediate_checkpoint(external, environment, critical, sg, context, before,
            entered, entry, eid, ticks, pmsg, checkpoint) &&
          mbox_pend_restore_input(None, external, platform, environment, critical, saved_local,
            sg, entered, mask, cpu_sr, entry, checkpoint)
        */
        OS_EXIT_CRITICAL();
        *perr = OS_ERR_NONE;
        OS_TRACE_MBOX_PEND_EXIT(*perr);
        return (pmsg);                                /* Return the message received (or NULL)         */
    }
    /*@ exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State)
        (current: OSEventAbstractState) (mailbox: MboxFields),
        pmsg == mbox_message_ptr(mailbox) && pmsg == 0 && timeout == ticks &&
        pevent == event_addr(sg, eid) && mbox_accept_profile(sg) &&
        mbox_pend_message_frame(external, platform, environment, critical, saved_local, sg, context, entered,
          mask, cpu_sr, pe, before, entry, eid, observed, current, mailbox) *
        data_at(&pevent->OSEventPtr, void *, mbox_message_ptr(mailbox)) &&
        event_object_layout_prop(sg, eid) && &OSTCBCur == sg.g_OSTCBCur
        which implies exists (owned: TaskStackCallEnvironment) (entered: OsSchedCallContext)
          (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState),
        timeout == ticks && pevent == event_addr(sg, eid) && pmsg == 0 &&
        environment == Some(owned) && external == task_stack_call_external(owned) &&
        platform == task_stack_call_platform(owned) && &OSTCBCur == sg.g_OSTCBCur &&
        mbox_pend_empty_snapshot(external, environment, critical, sg, context, entered,
          mask, cpu_sr, pe, before, entry, eid, observed, current, tid, old) &&
        mbox_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
          entered, cpu_sr, entry, entry) *
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBStat, unsigned char, encode_task_status(old.stat)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBStatPend, unsigned char, encode_pend_status(old.statPend)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBDly, unsigned int, old.dly) *
        sem_pend_prefix_frame(sg, entry, tid, old)
    */
    /*@ 0 <= OSTCBCur->OSTCBStat && OSTCBCur->OSTCBStat <= 255 by local */
    OSTCBCur->OSTCBStat     |= OS_STAT_MBOX;        /* Task will have to pend for a message to be posted  */
    OSTCBCur->OSTCBStatPend  = OS_STAT_PEND_OK;
    OSTCBCur->OSTCBDly       = timeout;          /* Load timeout into TCB                              */
    /*@ exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State)
        (current: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState),
        mbox_pend_empty_snapshot(external, environment, critical, sg, context, entered,
          mask, cpu_sr, pe, before, entry, eid, observed, current, tid, old) &&
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBStat, unsigned char, encode_task_status(old.stat) | 2) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBStatPend, unsigned char, 0) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBDly, unsigned int, timeout) *
        sem_pend_prefix_frame(sg, entry, tid, old) &&
        timeout == ticks && &OSTCBCur == sg.g_OSTCBCur && pevent == event_addr(sg, eid)
        which implies
        timeout == ticks &&
        mbox_pend_empty_snapshot(external, environment, critical, sg, context, entered,
          mask, cpu_sr, pe, before, entry, eid, observed, current, tid, old) &&
        mbox_pend_wait_entry(sg, entry, eid, current, tid, old) &&
        pevent == event_addr(sg, eid) && mbox_pend_wait_call_pre(sg, entry, eid, current, tid, old, ticks)
    */
    OS_EventTaskWait(pevent);                    /* Suspend task until event or timeout occurs         */
    /*@ exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State)
        (current: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState),
        mbox_pend_empty_snapshot(external, environment, critical, sg, context, entered,
          mask, cpu_sr, pe, before, entry, eid, observed, current, tid, old) &&
        kernel_tcb_stack_field_layout(sg) &&
        mbox_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
          entered, cpu_sr, entry, entry) * mbox_pend_wait_call_post(sg, entry, eid, current, tid, old, ticks)
        which implies exists (waiting: UCOS2_Verify_State),
        mbox_pend_first_wait_checkpoint(external, environment, critical, sg, context,
          before, entered, eid, ticks, waiting) &&
        mbox_pend_restore_input(Some(MboxPendWaitPhase(context, mask, eid)),
          external, platform, environment, critical, saved_local, sg, entered, mask, cpu_sr, entry, waiting)
    */
    OS_EXIT_CRITICAL();
    /*@ exists (entered: OsSchedCallContext) (waiting: UCOS2_Verify_State),
        mbox_pend_first_wait_checkpoint(external, environment, critical, sg, context,
          before, entered, eid, ticks, waiting) &&
        mbox_pend_restore_output(Some(MboxPendWaitPhase(context, mask, eid)),
          external, platform, environment, critical, saved_local, sg, entered, mask, waiting)
        which implies exists (owned: TaskStackCallEnvironment) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State),
        environment == Some(owned) && external == task_stack_call_external(owned) &&
        platform == task_stack_call_platform(owned) &&
        mbox_pend_scheduling_checkpoint(external, environment, critical, sg, context,
          before, eid, ticks, released, unmasked) &&
        mbox_pend_sched_admitted(environment, critical) &&
        mbox_sched_continuation_phase_sched_input(MboxPendWaitPhase(context, mask, eid),
          task_stack_call_external(owned), task_stack_call_platform(owned), Some(owned),
          critical, saved_local, sg, released, mask, unmasked)
    */
    OS_Sched();                                  /* Find next highest priority task ready to run       */
    /*@ exists (owned: TaskStackCallEnvironment) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State),
        environment == Some(owned) && external == task_stack_call_external(owned) &&
        platform == task_stack_call_platform(owned) &&
        mbox_pend_scheduling_checkpoint(external, environment, critical, sg, context,
          before, eid, ticks, released, unmasked) &&
        mbox_pend_sched_admitted(environment, critical) &&
        mbox_sched_continuation_phase_sched_output(MboxPendWaitPhase(context, mask, eid),
          task_stack_call_external(owned), task_stack_call_platform(owned), Some(owned),
          critical, saved_local, sg, released, mask, unmasked)
        which implies exists (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State),
        mbox_pend_scheduled_checkpoint(external, environment, critical, sg, context,
          before, eid, ticks, scheduled, selected) &&
        mbox_pend_save_input(MboxPendResumePhase(MboxPendWaitPhase(context, mask, eid)),
          external, platform, environment, critical, saved_local, sg, scheduled, mask, selected)
    */
    OS_ENTER_CRITICAL();
    /*@ exists (selected: UCOS2_Verify_State)
        (scheduled: OsSchedCallContext),
        mbox_pend_scheduled_checkpoint(external, environment, critical, sg, context,
          before, eid, ticks, scheduled, selected) &&
        mbox_pend_save_output(MboxPendResumePhase(MboxPendWaitPhase(context, mask, eid)),
          external, platform, environment, critical, saved_local, sg, scheduled, mask, cpu_sr, selected) &&
        &OSTCBCur == sg.g_OSTCBCur
        which implies exists (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State)
          (resume_tid: TaskID) (node: TaskAbstractState),
        mbox_pend_resume_checkpoint(external, environment, critical, sg, context,
          before, eid, ticks, resumed, resume_entry) &&
        interrupt_saved_value(mask, cpu_sr) &&
        sem_pend_resume_entry(sg, resume_entry, eid, resume_tid, node) &&
        mbox_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
          resumed, cpu_sr, resume_entry, resume_entry) *
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStat, unsigned char, encode_task_status(node.stat)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStatPend, unsigned char, encode_pend_status(node.statPend)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBEventPtr, OS_EVENT *, encode_event_link(sg, node.eventPtr)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBMsg, void *, encode_msg(node.msg)) *
        q_pend_cleanup_frame(sg, resume_entry, resume_tid, node)
    */
    switch (OSTCBCur->OSTCBStatPend) {                /* See if we timed-out or aborted                */
        case OS_STAT_PEND_OK:                         /* Extract message delivered to the TCB */
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
                 mbox_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
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
                 mbox_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
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
                 mbox_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
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
                 mbox_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
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
        pevent == pevent && timeout == timeout && perr == pd &&
        mbox_pend_api_safe(external, environment, critical, sg, context, pe, eid, ticks, mask, before, X) &&
        mbox_pend_api_prefix(pe, before, eid) &&
        mbox_pend_resume_checkpoint(external, environment, critical, sg, context,
          before, eid, ticks, resumed, resume_entry) &&
        q_pend_cleanup_observation(sg, resume_entry, eid, pmsg, code, cleaning, resume_tid, node) &&
        interrupt_saved_value(mask, cpu_sr) && &OSTCBCur == sg.g_OSTCBCur &&
        mbox_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
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
        mbox_pend_masked_frame(external, platform, environment, critical, saved_local, sg,
          resumed, cpu_sr, resume_entry, cleaning) * data_at(perr, unsigned char, code) *
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStat, unsigned char, 0) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStatPend, unsigned char, 0) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBEventPtr, OS_EVENT *, 0) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBMsg, void *, 0) *
        q_pend_cleanup_frame(sg, cleaning, resume_tid, node) && &OSTCBCur == sg.g_OSTCBCur
        which implies exists (checkpoint: UCOS2_Verify_State),
        q_pend_resume_result(sg, eid, resume_entry, pmsg, code, checkpoint) &&
        mbox_pend_restore_input(None, external, platform, environment, critical, saved_local,
          sg, resumed, mask, cpu_sr, resume_entry, checkpoint) * data_at(perr, unsigned char, code)
    */
    OS_EXIT_CRITICAL();
    OS_TRACE_MBOX_PEND_EXIT(*perr);

    return (pmsg);                                    /* Return received message                       */
}
