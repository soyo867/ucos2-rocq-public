/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSSemPendAbort (OS_EVENT  *pevent,
                     INT8U      opt,
                     INT8U     *perr)
/*@ With (environment: TaskStackCallEnvironment) saved_local (critical: CriticalRegionResources)
    (sg: StableGlobVars) (caller: TaskResumeCaller) (mask: Z) (before: UCOS2_Verify_State)
    (eid: EventID) (observed: OSEventAbstractState) (pe error_addr: addr) (option: Z) X
    Require pevent == pe && sem_pend_abort_source_output_address(error_addr, perr) && opt == option &&
      sem_pend_abort_source_profile(sg) && UCOS2_state_inv(sg, before) &&
      sem_pend_abort_source_call_input(critical, sg, caller, pe, before, eid, observed) &&
      sem_pend_abort_source_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, option, before) &&
      sem_pend_abort_source_safe(environment, critical, sg, caller, mask, pe, eid, option, before, X) &&
      os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
        &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
      q_post_closed(environment, critical, saved_local, sg, caller, mask, before) * undef_data_at(perr, unsigned char)
    Ensure sem_pend_abort_source_post(environment, critical, saved_local, sg, caller, mask, pe, eid, option, before, error_addr, __return, X)
*/
{
    INT8U      nbr_tasks;
#if OS_CRITICAL_METHOD == 3u                               /* Allocate storage for CPU status register */
    OS_CPU_SR  cpu_sr = 0u;
#endif
#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return (0u);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {                         /* Validate 'pevent'                        */
        *perr = OS_ERR_PEVENT_NULL;
        return (0u);
    }
#endif
    /*@ pevent == pe && pevent != 0 && sem_pend_abort_source_profile(sg) && UCOS2_state_inv(sg, before) &&
        sem_pend_abort_source_call_input(critical, sg, caller, pe, before, eid, observed) &&
        q_post_closed(environment, critical, saved_local, sg, caller, mask, before)
        which implies
        pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && valid_event_id(sg, eid) &&
        sem_pend_abort_source_profile(sg) && UCOS2_state_inv(sg, before) &&
        sem_pend_abort_source_call_input(critical, sg, caller, pe, before, eid, observed) &&
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        sem_pend_abort_source_type_context(environment, saved_local, sg, caller, mask, before, eid) */
    /*@ 0 <= event_slot_type_value(EventState(before), eid) && event_slot_type_value(EventState(before), eid) <= 255 by local */
    if (pevent->OSEventType != OS_EVENT_TYPE_SEM) {          /* Validate event block type                */
        *perr = OS_ERR_EVENT_TYPE;
        return (0u);
    }
    /*@ pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && valid_event_id(sg, eid) &&
        sem_pend_abort_source_profile(sg) && UCOS2_state_inv(sg, before) &&
        sem_pend_abort_source_call_input(critical, sg, caller, pe, before, eid, observed) &&
        event_slot_type_value(EventState(before), eid) == 3 &&
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        sem_pend_abort_source_type_context(environment, saved_local, sg, caller, mask, before, eid)
        which implies pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 &&
        valid_event_id(sg, eid) && sem_pend_abort_source_profile(sg) &&
        sem_pend_abort_source_save_pre(environment, critical, saved_local, sg, caller, mask, before, pe, eid, observed) */
    OS_ENTER_CRITICAL();
    /*@ pevent == event_addr(sg, eid) && valid_event_id(sg, eid) && sem_pend_abort_source_profile(sg) &&
        sem_pend_abort_source_save_result(environment, critical, saved_local, sg, caller, mask, cpu_sr, before, eid, observed)
        which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState),
        pevent == event_addr(sg, eid) &&
        sem_pend_abort_source_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial) *
        data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, initial)) */
    if (pevent->OSEventGrp != 0u) {                        /* See if any task waiting on queue?        */
        nbr_tasks = 0u;
        /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState),
            pevent == event_addr(sg, eid) && q_post_group(acquired, initial) != 0 && nbr_tasks == 0 &&
            sem_pend_abort_source_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial) *
            data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, initial))
            which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState),
            pevent == event_addr(sg, eid) && nbr_tasks == 0 &&
            sem_pend_abort_source_loop_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, acquired, initial, nil, 0) *
            data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, initial)) */
        switch (opt) {
            case OS_PEND_OPT_BROADCAST:                    /* Do we need to abort ALL waiting tasks?   */
                 /*@ Inv Assert exists (active: TaskResumeCaller) (acquired state: UCOS2_Verify_State)
                     (initial node: OSEventAbstractState) (processed: list Priority),
                     pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 &&
                     sem_pend_abort_source_output_address(error_addr, perr) && opt == option && option == 1 &&
                     sem_pend_abort_source_safe(environment, critical, sg, caller, mask, pe, eid, option, before, X) &&
                     sem_pend_abort_source_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, option, before) &&
                     os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
                       &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
                     sem_pend_abort_source_loop_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, state, node, processed, nbr_tasks) *
                     data_at(&pevent->OSEventGrp, unsigned char, q_post_group(state, node)) *
                     undef_data_at(perr, unsigned char) */
                 while (pevent->OSEventGrp != 0u) {        /* Yes, ready ALL tasks waiting on queue    */
                     /*@ exists (active: TaskResumeCaller) (acquired state: UCOS2_Verify_State)
                         (initial node: OSEventAbstractState) (processed: list Priority),
                         pevent == event_addr(sg, eid) && q_post_group(state, node) != 0 &&
                         sem_pend_abort_source_loop_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, state, node, processed, nbr_tasks) *
                         data_at(&pevent->OSEventGrp, unsigned char, q_post_group(state, node))
                         which implies exists (active: TaskResumeCaller) (acquired state: UCOS2_Verify_State)
                         (initial node: OSEventAbstractState) (processed: list Priority) (tid: TaskID) (old: TaskAbstractState),
                         pevent == event_addr(sg, eid) && 0 <= nbr_tasks && nbr_tasks < 255 &&
                         sem_pend_abort_source_loop_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, state, node, processed, nbr_tasks, tid, old) *
                         event_task_rdy_pre(sg, TskState(state), eid, node, tid, old, 1, 2, q_post_sched_group(state), q_post_sched_rows(state)) */
                     (void)OS_EventTaskRdy(pevent, (void *)0, OS_STAT_SEM, OS_STAT_PEND_ABORT);
                     /*@ Assert exists (active: TaskResumeCaller) (acquired state: UCOS2_Verify_State)
                         (initial node: OSEventAbstractState) (processed: list Priority) (tid: TaskID) (old: TaskAbstractState) (priority: Z),
                         pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 &&
                         sem_pend_abort_source_output_address(error_addr, perr) && opt == option && option == 1 &&
                         0 <= nbr_tasks && nbr_tasks < 255 &&
                         sem_pend_abort_source_safe(environment, critical, sg, caller, mask, pe, eid, option, before, X) &&
                         sem_pend_abort_source_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, option, before) &&
                         os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
                           &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
                         sem_pend_abort_source_loop_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, state, node, processed, nbr_tasks, tid, old) *
                         event_task_rdy_post(sg, TskState(state), eid, node, tid, old, 0, 1, 2, q_post_sched_group(state), q_post_sched_rows(state), priority) *
                         undef_data_at(perr, unsigned char) */
                     /*@ exists (active: TaskResumeCaller) (acquired state: UCOS2_Verify_State)
                         (initial node: OSEventAbstractState) (processed: list Priority) (tid: TaskID) (old: TaskAbstractState) (priority: Z),
                         pevent == event_addr(sg, eid) && 0 <= nbr_tasks && nbr_tasks < 255 &&
                         sem_pend_abort_source_loop_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, state, node, processed, nbr_tasks, tid, old) *
                         event_task_rdy_post(sg, TskState(state), eid, node, tid, old, 0, 1, 2, q_post_sched_group(state), q_post_sched_rows(state), priority)
                         which implies exists (active: TaskResumeCaller) (acquired next: UCOS2_Verify_State)
                         (initial next_node: OSEventAbstractState) (next_processed: list Priority),
                         pevent == event_addr(sg, eid) && 0 <= nbr_tasks && nbr_tasks < 255 &&
                         sem_pend_abort_source_loop_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, next, next_node, next_processed, nbr_tasks + 1) *
                         data_at(&pevent->OSEventGrp, unsigned char, q_post_group(next, next_node)) */
                     nbr_tasks++;
                 }
                 /*@ exists (active: TaskResumeCaller) (acquired state: UCOS2_Verify_State)
                     (initial node: OSEventAbstractState) (processed: list Priority),
                     pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && option == 1 &&
                     q_post_group(state, node) == 0 &&
                     sem_pend_abort_source_loop_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, state, node, processed, nbr_tasks) *
                     data_at(&pevent->OSEventGrp, unsigned char, q_post_group(state, node))
                     which implies exists (active: TaskResumeCaller) (acquired released: UCOS2_Verify_State),
                     pevent == pe && nbr_tasks == nbr_tasks &&
                     sem_pend_abort_source_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr,
                       pe, eid, option, before, acquired, released, nbr_tasks, 14, 1) */
                 break;

            case OS_PEND_OPT_NONE:
            default:                                       /* No,  ready HPT       waiting on queue    */
                 /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState),
                     pevent == event_addr(sg, eid) && nbr_tasks == 0 &&
                     sem_pend_abort_source_loop_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, acquired, initial, nil, 0) *
                     data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, initial))
                     which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState),
                     pevent == event_addr(sg, eid) && nbr_tasks == 0 &&
                     sem_pend_abort_source_loop_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, acquired, initial, nil, 0, tid, old) *
                     event_task_rdy_pre(sg, TskState(acquired), eid, initial, tid, old, 1, 2, q_post_sched_group(acquired), q_post_sched_rows(acquired)) */
                 (void)OS_EventTaskRdy(pevent, (void *)0, OS_STAT_SEM, OS_STAT_PEND_ABORT);
                 /*@ Assert exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState)
                     (tid: TaskID) (old: TaskAbstractState) (priority: Z),
                     pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && sem_pend_abort_source_output_address(error_addr, perr) && opt == option && option != 1 &&
                     nbr_tasks == 0 && 0 <= option && option <= 255 &&
                     sem_pend_abort_source_safe(environment, critical, sg, caller, mask, pe, eid, option, before, X) &&
                     sem_pend_abort_source_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, option, before) &&
                     os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
                       &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
                     sem_pend_abort_source_loop_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, acquired, initial, nil, 0, tid, old) *
                     event_task_rdy_post(sg, TskState(acquired), eid, initial, tid, old, 0, 1, 2, q_post_sched_group(acquired), q_post_sched_rows(acquired), priority) *
                     undef_data_at(perr, unsigned char) */
                 /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState)
                     (tid: TaskID) (old: TaskAbstractState) (priority: Z),
                     pevent == pe && pevent != 0 && option != 1 && 0 <= option && option <= 255 && nbr_tasks == 0 &&
                     sem_pend_abort_source_loop_wake_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial, acquired, initial, nil, 0, tid, old) *
                     event_task_rdy_post(sg, TskState(acquired), eid, initial, tid, old, 0, 1, 2, q_post_sched_group(acquired), q_post_sched_rows(acquired), priority)
                     which implies exists (active: TaskResumeCaller) (acquired released: UCOS2_Verify_State),
                     pevent == pe && nbr_tasks == 0 &&
                     sem_pend_abort_source_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr,
                       pe, eid, option, before, acquired, released, 1, 14, 1) */
                 nbr_tasks++;
                 break;
        }
        /*@ Assert exists (active: TaskResumeCaller) (acquired released: UCOS2_Verify_State),
            pevent == pe && sem_pend_abort_source_output_address(error_addr, perr) && opt == option &&
            sem_pend_abort_source_safe(environment, critical, sg, caller, mask, pe, eid, option, before, X) &&
            sem_pend_abort_source_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, option, before) &&
            os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
              &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
            sem_pend_abort_source_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr,
              pe, eid, option, before, acquired, released, nbr_tasks, 14, 1) * undef_data_at(perr, unsigned char) */
        OS_EXIT_CRITICAL();
        /*@ sem_pend_abort_source_schedule_protocol(environment, critical, sg, caller, mask, pe, eid, option, before) &&
            sem_pend_abort_source_restore_post(environment, critical, saved_local, sg, caller, mask, pe, eid, option, before, nbr_tasks, 14, 1)
            which implies exists (returned: TaskResumeCaller) (restored: UCOS2_Verify_State),
            nbr_tasks == nbr_tasks &&
            sem_pend_abort_source_prefix_result(environment, critical, sg, caller, mask, pe, eid, option, before, nbr_tasks, 14, 1, returned, restored) &&
            task_resume_sched_pre(environment, critical, saved_local, sg, returned, mask, restored) *
            q_post_extra_tables(sg, returned) */
        OS_Sched();                                        /* Find HPT ready to run                    */
        *perr = OS_ERR_PEND_ABORT;
        return (nbr_tasks);
    }
    /*@ exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState),
        pevent == pe && pevent == event_addr(sg, eid) && pevent != 0 && q_post_group(acquired, initial) == 0 &&
        sem_pend_abort_source_group_context(environment, critical, saved_local, sg, caller, active, mask, cpu_sr, before, acquired, eid, observed, initial) *
        data_at(&pevent->OSEventGrp, unsigned char, q_post_group(acquired, initial))
        which implies exists (active: TaskResumeCaller) (acquired: UCOS2_Verify_State),
        pevent == pe &&
        sem_pend_abort_source_restore_pre(environment, critical, saved_local, sg, caller, active, mask, cpu_sr,
          pe, eid, option, before, acquired, acquired, 0, 0, 0) */
    OS_EXIT_CRITICAL();
    *perr = OS_ERR_NONE;
    return (0u);                                           /* No tasks waiting on queue                */
}
