/* Annotation carrier for OSSemPend, pinned uC/OS-II V2.93.01.
 * Original headers, configuration and callee declarations: ../../overlays/sem/pend*.patch.
 * Reproduce the canonical translation unit using the module README; do not expand macros here.
 */
void  OSSemPend (OS_EVENT  *pevent,
                 INT32U     timeout,
                 INT8U     *perr)
/*@ With (external: OsSchedExternalResources) (platform: InterruptPlatformResources)
         (critical: CriticalRegionResources) (sg: StableGlobVars) (context: OsSchedCallContext)
         (environment: option TaskStackCallEnvironment) saved_local
         (mask: Z) (before: UCOS2_Verify_State) (eid: EventID)
         (observed: OSEventAbstractState) (pe pd ticks: Z) X
    Require pevent == pe && timeout == ticks && perr == pd && coq_prop(sem_pend_runtime_nonblocking(critical, sg, context, environment, pe, before, eid)) && coq_prop(sem_pend_observed_admission(environment, critical, sg, context, pe, before, eid)) &&
coq_prop(sem_pend_profile(sg)) && coq_prop(kernel_tcb_stack_field_layout(sg)) && coq_prop(sem_pend_call_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed)) &&
      safeExec(LastSeen(before), bind(atomic_cmd(sem_pend_runtime_program(external, platform, environment, critical, sg, context, pe, ticks)),
                                    sem_query_observe_error), X) &&
      mutex_query_closed(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, before) * os_sched_context_resources(external, context) * unmap_table_rep(sg) *
      sem_pend_error_cell(pd) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, context, before) &&
      (pe == 0 || (pe != 0 && &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
        (event_slot_type_value(before.EventState, eid) != 3 || (event_slot_type_value(before.EventState, eid) == 3 && &OSIntNesting == sg.g_OSIntNesting &&
          (before.IntrState.intNesting > 0 || (before.IntrState.intNesting <= 0 &&
           &OSLockNesting == sg.g_OSLockNesting &&
           (before.IntrState.lockNesting > 0 || (before.IntrState.lockNesting <= 0 &&
            &((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
            coq_prop(sem_pend_observed_blocking_layout(environment, critical, sg, context, before, eid, &OSTCBCur, &OSRdyGrp, &OSRdyTbl)))))))))) &&
      coq_prop(os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl))
    Ensure sem_pend_continuation_call_post(external, platform, environment, critical, saved_local, sg, context, mask, pe, ticks, pd, before, X)
*/
{
#if OS_CRITICAL_METHOD == 3u                          /* Allocate storage for CPU status register      */
    OS_CPU_SR  cpu_sr = 0u;
#endif



/*@ perr == pd && timeout == ticks && sem_pend_error_cell(pd)
which implies perr == pd && timeout == ticks && undef_data_at(perr, unsigned char) */
#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return;
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {                    /* Validate 'pevent'                             */
        *perr = OS_ERR_PEVENT_NULL;
        return;
    }
#endif

    OS_TRACE_SEM_PEND_ENTER(pevent, timeout);

    
/*@ coq_prop(sem_pend_call_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed)) && pevent == pe && pe != 0 &&
&((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off && mutex_query_closed(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, before)
which implies
coq_prop(sem_pend_call_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed)) && pevent == pe && pe == event_addr(sg, eid) &&
coq_prop(valid_event_id(sg, eid)) && coq_prop(sem_query_public_slot(before, eid, observed)) &&
coq_prop(UCOS2_state_inv(sg, before)) &&
&((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
interrupt_platform_running(platform, os_sched_call_invocation(context), os_sched_call_origin(context), mask) * data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(before.EventState, eid)) * sem_query_type_frame(sg, before, eid) */

/*@ 0 <= event_slot_type_value(before.EventState, eid) && event_slot_type_value(before.EventState, eid) <= 255 by local */
if (pevent->OSEventType != OS_EVENT_TYPE_SEM) {   /* Validate event block type                     */
        *perr = OS_ERR_EVENT_TYPE;
        OS_TRACE_SEM_PEND_EXIT(*perr);
        return;
    }
    
/*@ coq_prop(UCOS2_state_inv(sg, before)) && &OSIntNesting == sg.g_OSIntNesting &&
&((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off && data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(before.EventState, eid)) * sem_query_type_frame(sg, before, eid)
which implies coq_prop(UCOS2_state_inv(sg, before)) &&
&OSIntNesting == sg.g_OSIntNesting &&
data_at(&OSIntNesting, unsigned char, before.IntrState.intNesting) *
data_at(sg.g_OSLockNesting, unsigned char, before.IntrState.lockNesting) * sem_pend_interrupt_frame(sg, before) */

/*@ 0 <= before.IntrState.intNesting && before.IntrState.intNesting <= 255 by local */
if (OSIntNesting > 0u) {                          /* See if called from ISR ...                    */
        *perr = OS_ERR_PEND_ISR;                      /* ... can't PEND from an ISR                    */
        OS_TRACE_SEM_PEND_EXIT(*perr);
        return;
    }
    
/*@ &OSLockNesting == sg.g_OSLockNesting && data_at(sg.g_OSLockNesting, unsigned char, before.IntrState.lockNesting)
which implies &OSLockNesting == sg.g_OSLockNesting && data_at(&OSLockNesting, unsigned char, before.IntrState.lockNesting) */

/*@ 0 <= before.IntrState.lockNesting && before.IntrState.lockNesting <= 255 by local */
if (OSLockNesting > 0u) {                         /* See if called with scheduler locked ...       */
        *perr = OS_ERR_PEND_LOCKED;                   /* ... can't PEND when locked                    */
        OS_TRACE_SEM_PEND_EXIT(*perr);
        return;
    }
    
/*@ coq_prop(UCOS2_state_inv(sg, before)) &&
&OSIntNesting == sg.g_OSIntNesting && &OSLockNesting == sg.g_OSLockNesting &&
interrupt_platform_running(platform, os_sched_call_invocation(context), os_sched_call_origin(context), mask) * data_at(&OSIntNesting, unsigned char, before.IntrState.intNesting) *
data_at(&OSLockNesting, unsigned char, before.IntrState.lockNesting) * sem_pend_interrupt_frame(sg, before)
which implies coq_prop(UCOS2_state_inv(sg, before)) && mutex_query_closed(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, before) */
/*@ coq_prop(sem_pend_call_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed)) &&
coq_prop(sem_pend_observed_admission(environment, critical, sg, context, pe, before, eid)) &&
coq_prop(sem_pend_runtime_nonblocking(critical, sg, context, environment, pe, before, eid)) &&
coq_prop(UCOS2_state_inv(sg, before)) && pe != 0 && event_slot_type_value(before.EventState, eid) == 3 &&
before.IntrState.intNesting <= 0 && before.IntrState.lockNesting <= 0 &&
mutex_query_closed(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, before) *
os_sched_context_resources(external, context) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, context, before)
which implies coq_prop(sem_pend_call_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed)) &&
coq_prop(sem_pend_observed_admission(environment, critical, sg, context, pe, before, eid)) &&
coq_prop(sem_pend_runtime_nonblocking(critical, sg, context, environment, pe, before, eid)) &&
coq_prop(UCOS2_state_inv(sg, before)) &&
sem_pend_continuation_phase_save_input(SemPendAcquirePhase(pe, eid, observed), external, platform, environment, critical, saved_local, sg, context, mask, before) */
OS_ENTER_CRITICAL();
/*@ sem_pend_continuation_phase_save_output(SemPendAcquirePhase(pe, eid, observed), external, platform, environment, critical, saved_local, sg, context, mask, cpu_sr, before)
which implies exists (entry: UCOS2_Verify_State) (first_returned: OsSchedCallContext),
coq_prop(sem_pend_stack_save_observation(critical, sg, context, first_returned, environment, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_save_phase_observation(SemPendAcquirePhase(pe, eid, observed), environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry)) &&
critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry) *
os_sched_context_resources(external, first_returned) * UCOS2_inv(sg, entry) *
sem_pend_optional_continuation_resources(external, platform, environment, saved_local, first_returned, entry) */
    
/*@ exists (entry: UCOS2_Verify_State) (first_returned: OsSchedCallContext),
coq_prop(sem_pend_stack_save_observation(critical, sg, context, first_returned, environment, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_save_phase_observation(SemPendAcquirePhase(pe, eid, observed), environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry)) &&
coq_prop(UCOS2_state_inv(sg, before)) &&
coq_prop(sem_pend_call_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed)) && event_slot_type_value(before.EventState, eid) == 3 && before.IntrState.intNesting <= 0 && before.IntrState.lockNesting <= 0 &&
pevent == pe && pe != 0 && pe == event_addr(sg, eid) &&
&((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off && critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry) * UCOS2_inv(sg, entry) * os_sched_context_resources(external, first_returned) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, first_returned, entry)
which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (first_returned: OsSchedCallContext),
coq_prop(sem_pend_stack_save_observation(critical, sg, context, first_returned, environment, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_save_phase_observation(SemPendAcquirePhase(pe, eid, observed), environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry)) &&
coq_prop(interrupt_saved_value(mask, cpu_sr)) &&
coq_prop(sem_pend_optional_acquire_observation(environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry, eid, observed, current)) &&
coq_prop(UCOS2_state_inv(sg, entry)) && coq_prop(mutex_query_lookup(entry, eid, current)) &&
encode_event_type(eventType(current)) == 3 && 0 <= encode_event_cnt_value(current) && encode_event_cnt_value(current) <= 65535 &&
pevent == pe && pe == event_addr(sg, eid) &&
critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, encode_event_cnt_value(current)) *
sem_post_count_frame(sg, entry, eid, current) * os_sched_context_resources(external, first_returned) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, first_returned, entry) */
if (pevent->OSEventCnt > 0u) {                    /* If sem. is positive, resource available ...   */
        pevent->OSEventCnt--;                         /* ... decrement semaphore only if positive.     */
        
/*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (first_returned: OsSchedCallContext),
coq_prop(sem_pend_stack_save_observation(critical, sg, context, first_returned, environment, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_save_phase_observation(SemPendAcquirePhase(pe, eid, observed), environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry)) &&
coq_prop(interrupt_saved_value(mask, cpu_sr)) &&
coq_prop(sem_pend_optional_acquire_observation(environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry, eid, observed, current)) &&
coq_prop(UCOS2_state_inv(sg, entry)) && coq_prop(mutex_query_lookup(entry, eid, current)) &&
encode_event_type(eventType(current)) == 3 && encode_event_cnt_value(current) > 0 &&
&((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry) *
os_sched_context_resources(external, first_returned) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, first_returned, entry) *
data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, encode_event_cnt_value(current) - 1) * sem_post_count_frame(sg, entry, eid, current)
which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (first_returned: OsSchedCallContext),
coq_prop(interrupt_saved_value(mask, cpu_sr)) &&
coq_prop(sem_pend_optional_acquire_observation(environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry, eid, observed, current)) &&
coq_prop(kernel_stack_call_same_call(first_returned, context)) && encode_event_cnt_value(current) > 0 &&
sem_pend_continuation_phase_restore_input(SemPendReturnPhase, external, platform, environment, critical, saved_local, sg, first_returned, mask, cpu_sr, entry,
sem_count_update_state(entry, eid, current, encode_event_cnt_value(current) - 1)) */
OS_EXIT_CRITICAL();
        *perr = OS_ERR_NONE;
        OS_TRACE_SEM_PEND_EXIT(*perr);
        return;
    }
                                                      /* Otherwise, must wait until event occurs       */
    
/*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (first_returned: OsSchedCallContext),
coq_prop(sem_pend_stack_save_observation(critical, sg, context, first_returned, environment, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_save_phase_observation(SemPendAcquirePhase(pe, eid, observed), environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_observed_blocking_layout(environment, critical, sg, context, before, eid, &OSTCBCur, &OSRdyGrp, &OSRdyTbl)) &&
coq_prop(sem_pend_optional_acquire_observation(environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry, eid, observed, current)) &&
coq_prop(UCOS2_state_inv(sg, entry)) && coq_prop(mutex_query_lookup(entry, eid, current)) &&
encode_event_type(eventType(current)) == 3 &&
0 <= encode_event_cnt_value(current) && encode_event_cnt_value(current) <= 0 &&
&((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, encode_event_cnt_value(current)) *
sem_post_count_frame(sg, entry, eid, current) * os_sched_context_resources(external, first_returned) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, first_returned, entry) * critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry)
which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (first_returned: OsSchedCallContext),
coq_prop(sem_pend_stack_save_observation(critical, sg, context, first_returned, environment, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_save_phase_observation(SemPendAcquirePhase(pe, eid, observed), environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_optional_acquire_observation(environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry, eid, observed, current)) &&
coq_prop(UCOS2_state_inv(sg, entry)) && coq_prop(mutex_query_lookup(entry, eid, current)) &&
encode_event_type(eventType(current)) == 3 && encode_event_cnt_value(current) == 0 &&
&OSTCBCur == sg.g_OSTCBCur && &OSRdyGrp == sg.g_OSRdyGrp && &OSRdyTbl == sg.g_OSRdyTbl &&
coq_prop(event_object_layout_prop(sg, eid)) &&
data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, encode_event_cnt_value(current)) *
sem_post_count_frame(sg, entry, eid, current) * os_sched_context_resources(external, first_returned) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, first_returned, entry) * critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry) */

/*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (first_returned: OsSchedCallContext),
coq_prop(sem_pend_stack_save_observation(critical, sg, context, first_returned, environment, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_save_phase_observation(SemPendAcquirePhase(pe, eid, observed), environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry)) &&
coq_prop(UCOS2_state_inv(sg, entry)) && coq_prop(mutex_query_lookup(entry, eid, current)) &&
coq_prop(sem_pend_optional_acquire_observation(environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry, eid, observed, current)) &&
encode_event_type(eventType(current)) == 3 && encode_event_cnt_value(current) <= 0 &&
coq_prop(sem_pend_observed_admission(environment, critical, sg, context, pe, before, eid)) &&
coq_prop(sem_pend_runtime_nonblocking(critical, sg, context, environment, pe, before, eid)) &&
pe != 0 && event_slot_type_value(before.EventState, eid) == 3 &&
before.IntrState.intNesting <= 0 && before.IntrState.lockNesting <= 0 &&
&((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
&OSTCBCur == sg.g_OSTCBCur && coq_prop(event_object_layout_prop(sg, eid)) &&
data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, encode_event_cnt_value(current)) *
sem_post_count_frame(sg, entry, eid, current) * os_sched_context_resources(external, first_returned) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, first_returned, entry) * critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry)
which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (first_returned: OsSchedCallContext),
coq_prop(sem_pend_stack_save_observation(critical, sg, context, first_returned, environment, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_save_phase_observation(SemPendAcquirePhase(pe, eid, observed), environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_has_stack(environment)) &&
coq_prop(sem_pend_task_call_stage(sg, context, entry)) &&
coq_prop(UCOS2_state_inv(sg, entry)) && coq_prop(mutex_query_lookup(entry, eid, current)) &&
coq_prop(sem_pend_optional_acquire_observation(environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry, eid, observed, current)) &&
encode_event_type(eventType(current)) == 3 && encode_event_cnt_value(current) <= 0 &&
coq_prop(sem_pend_observed_admission(environment, critical, sg, context, pe, before, eid)) &&
coq_prop(sem_pend_runtime_nonblocking(critical, sg, context, environment, pe, before, eid)) &&
pe != 0 && event_slot_type_value(before.EventState, eid) == 3 &&
before.IntrState.intNesting <= 0 && before.IntrState.lockNesting <= 0 &&
&((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
&OSTCBCur == sg.g_OSTCBCur && coq_prop(event_object_layout_prop(sg, eid)) &&
data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, encode_event_cnt_value(current)) *
sem_post_count_frame(sg, entry, eid, current) * os_sched_context_resources(external, first_returned) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, first_returned, entry) * critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry) */
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (first_returned: OsSchedCallContext),
coq_prop(sem_pend_stack_save_observation(critical, sg, context, first_returned, environment, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_save_phase_observation(SemPendAcquirePhase(pe, eid, observed), environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_has_stack(environment)) &&
coq_prop(sem_pend_task_call_stage(sg, context, entry)) &&
coq_prop(UCOS2_state_inv(sg, entry)) && coq_prop(mutex_query_lookup(entry, eid, current)) &&
coq_prop(sem_pend_optional_acquire_observation(environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry, eid, observed, current)) &&
encode_event_type(eventType(current)) == 3 && encode_event_cnt_value(current) <= 0 &&
coq_prop(sem_pend_observed_admission(environment, critical, sg, context, pe, before, eid)) &&
coq_prop(sem_pend_runtime_nonblocking(critical, sg, context, environment, pe, before, eid)) &&
pe != 0 && event_slot_type_value(before.EventState, eid) == 3 &&
before.IntrState.intNesting <= 0 && before.IntrState.lockNesting <= 0 &&
&((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
&OSTCBCur == sg.g_OSTCBCur && coq_prop(event_object_layout_prop(sg, eid)) &&
data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, encode_event_cnt_value(current)) *
sem_post_count_frame(sg, entry, eid, current) * os_sched_context_resources(external, first_returned) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, first_returned, entry) * critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry)
which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (first_returned: OsSchedCallContext)
(tid: TaskID) (old: TaskAbstractState),
coq_prop(sem_pend_has_stack(environment)) &&
coq_prop(sem_pend_stack_save_observation(critical, sg, context, first_returned, environment, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_save_phase_observation(SemPendAcquirePhase(pe, eid, observed), environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_optional_acquire_observation(environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry, eid, observed, current)) &&
coq_prop(sem_pend_wait_entry(sg, entry, eid, current, tid, old)) &&
os_sched_call_origin(context) == RunningInvocation(tid, old.taskGeneration) &&
coq_prop(kernel_call_task_source(context, entry)) &&
coq_prop(sched_current_consistency(entry.TskState, entry.SchedState)) &&
coq_prop(event_object_layout_prop(sg, eid)) &&
0 <= encode_task_status(old.stat) && encode_task_status(old.stat) <= 255 &&
data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStat), unsigned char, encode_task_status(old.stat)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStatPend), unsigned char, encode_pend_status(old.statPend)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBDly), unsigned int, old.dly) *
sem_pend_prefix_frame(sg, entry, tid, old) * os_sched_context_resources(external, first_returned) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, first_returned, entry) * critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry) */
OSTCBCur->OSTCBStat     |= OS_STAT_SEM;           /* Resource not available, pend on semaphore     */
    OSTCBCur->OSTCBStatPend  = OS_STAT_PEND_OK;
    OSTCBCur->OSTCBDly       = timeout;               /* Store pend timeout in TCB                     */
    
/*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (first_returned: OsSchedCallContext) (tid: TaskID) (old: TaskAbstractState),
coq_prop(sem_pend_stack_save_observation(critical, sg, context, first_returned, environment, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_save_phase_observation(SemPendAcquirePhase(pe, eid, observed), environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_optional_acquire_observation(environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry, eid, observed, current)) &&
coq_prop(sem_pend_wait_entry(sg, entry, eid, current, tid, old)) &&
os_sched_call_origin(context) == RunningInvocation(tid, old.taskGeneration) &&
coq_prop(kernel_call_task_source(context, entry)) &&
coq_prop(sched_current_consistency(entry.TskState, entry.SchedState)) && timeout == ticks &&
pe == event_addr(sg, eid) && &OSTCBCur == sg.g_OSTCBCur && &OSRdyGrp == sg.g_OSRdyGrp && &OSRdyTbl == sg.g_OSRdyTbl &&
data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStat), unsigned char, encode_task_status(old.stat) | 1) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStatPend), unsigned char, 0) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBDly), unsigned int, timeout) *
sem_pend_prefix_frame(sg, entry, tid, old) * os_sched_context_resources(external, first_returned) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, first_returned, entry) * critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry)
which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (first_returned: OsSchedCallContext) (tid: TaskID) (old: TaskAbstractState),
timeout == ticks && coq_prop(sem_pend_stack_save_observation(critical, sg, context, first_returned, environment, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_save_phase_observation(SemPendAcquirePhase(pe, eid, observed), environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_observed_wait_origin(environment, critical, sg, context, first_returned, mask, cpu_sr, before, observed, entry, eid, current, tid, old)) && 0 <= old.curPrio / 8 && old.curPrio / 8 < 8 && data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBEventPtr), OS_EVENT *, 0) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBY), unsigned char, old.curPrio / 8) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBBitX), unsigned char, tcb_bit_x_of_prio(old.curPrio)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBBitY), unsigned char, tcb_bit_y_of_prio(old.curPrio)) *
data_at(&((OS_EVENT *)pe)->OSEventTbl[old.curPrio / 8], unsigned char, encode_event_wait_tbl_at_or(current.waitList, entry.TskState, old.curPrio / 8)) *
data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, encode_event_wait_grp(current.waitList, entry.TskState)) *
data_at(pointer_offset(&OSRdyTbl, old.curPrio / 8, unsigned char), unsigned char, encode_ready_tbl_at_or(entry.SchedState.readyList, entry.TskState, old.curPrio / 8)) * data_at(&OSRdyGrp, unsigned char, encode_ready_grp(entry.SchedState.readyList, entry.TskState)) *
sem_pend_wait_call_frame(sg, entry, eid, current, tid, old, ticks) * os_sched_context_resources(external, first_returned) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, first_returned, entry) * critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry) */
OS_EventTaskWait(pevent)
/*@ where frame = unmap_table_rep(sg) */
;                         /* Suspend task until event or timeout occurs    */
    
/*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: TaskID) (old: TaskAbstractState) (saved: Z) (first_returned: OsSchedCallContext),
cpu_sr == saved && coq_prop(sem_pend_has_stack(environment)) && coq_prop(sem_pend_observed_wait_origin(environment, critical, sg, context, first_returned, mask, cpu_sr, before, observed, entry, eid, current, tid, old)) &&
coq_prop(kernel_tcb_stack_field_layout(sg)) &&
coq_prop(sem_pend_stack_save_observation(critical, sg, context, first_returned, environment, mask, cpu_sr, before, entry)) &&
coq_prop(sem_pend_save_phase_observation(SemPendAcquirePhase(pe, eid, observed), environment, critical, sg, context, first_returned, mask, cpu_sr, before, entry)) &&
pevent == pe && pe == event_addr(sg, eid) &&
&OSTCBCur == sg.g_OSTCBCur && &OSRdyGrp == sg.g_OSRdyGrp && &OSRdyTbl == sg.g_OSRdyTbl &&
critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry) *
os_sched_context_resources(external, first_returned) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, first_returned, entry) *
event_task_wait_post(&OSTCBCur, task_slot_addr(sg, tid), pevent, &OSRdyGrp, &OSRdyTbl,
old.curPrio / 8, tcb_bit_x_of_prio(old.curPrio), tcb_bit_y_of_prio(old.curPrio), encode_event_wait_tbl_at_or(current.waitList, entry.TskState, old.curPrio / 8), encode_event_wait_grp(current.waitList, entry.TskState), encode_ready_tbl_at_or(entry.SchedState.readyList, entry.TskState, old.curPrio / 8), encode_ready_grp(entry.SchedState.readyList, entry.TskState)) * sem_pend_wait_call_frame(sg, entry, eid, current, tid, old, ticks)
which implies exists (waiting: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (saved: Z) (first_returned: OsSchedCallContext),
cpu_sr == saved && pevent == pe && coq_prop(sem_pend_observed_wait_history(environment, critical, sg, context, mask, before, observed, eid, ticks, waiting)) &&
coq_prop(UCOS2_state_inv(sg, waiting)) && coq_prop(kernel_stack_call_same_call(first_returned, context)) &&
coq_prop(kernel_call_task_source(first_returned, waiting)) &&
sem_pend_continuation_phase_restore_input(SemPendWaitPhase(context, mask, before, observed, eid, ticks, waiting), external, platform, environment, critical, saved_local, sg, first_returned, mask, cpu_sr, entry, waiting) */
OS_EXIT_CRITICAL();
    
/*@ exists (waiting: UCOS2_Verify_State) (first_returned: OsSchedCallContext),
coq_prop(sem_pend_observed_wait_history(environment, critical, sg, context, mask, before, observed, eid, ticks, waiting)) &&
coq_prop(UCOS2_state_inv(sg, waiting)) && coq_prop(kernel_stack_call_same_call(first_returned, context)) &&
coq_prop(kernel_call_task_source(first_returned, waiting)) &&
pe != 0 && event_slot_type_value(before.EventState, eid) == 3 && before.IntrState.intNesting <= 0 && before.IntrState.lockNesting <= 0 &&
coq_prop(os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl)) &&
sem_pend_continuation_phase_restore_output(SemPendWaitPhase(context, mask, before, observed, eid, ticks, waiting), external, platform, environment, critical, saved_local, sg, first_returned, mask, waiting) * unmap_table_rep(sg)
which implies exists (waiting sched_entry: UCOS2_Verify_State) (restored_call: OsSchedCallContext),
coq_prop(os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl)) &&
coq_prop(sem_pend_observed_wait_history(environment, critical, sg, context, mask, before, observed, eid, ticks, waiting)) &&
coq_prop(UCOS2_state_inv(sg, sched_entry)) && coq_prop(kernel_stack_call_same_call(restored_call, context)) &&
coq_prop(kernel_call_task_source(restored_call, sched_entry)) &&
coq_prop(sem_pend_wait_sched_entry(sg, restored_call, sched_entry)) &&
sem_pend_continuation_phase_sched_input(SemPendWaitPhase(context, mask, before, observed, eid, ticks, waiting), external, platform, environment, critical, saved_local, sg, restored_call, mask, sched_entry) */
OS_Sched();                                       /* Find next highest priority task ready         */
    
/*@ exists (waiting sched_entry: UCOS2_Verify_State) (restored_call: OsSchedCallContext),
coq_prop(sem_pend_observed_wait_history(environment, critical, sg, context, mask, before, observed, eid, ticks, waiting)) &&
coq_prop(kernel_stack_call_same_call(restored_call, context)) && coq_prop(kernel_call_task_source(restored_call, sched_entry)) &&
sem_pend_continuation_phase_sched_output(SemPendWaitPhase(context, mask, before, observed, eid, ticks, waiting), external, platform, environment, critical, saved_local, sg, restored_call, mask, sched_entry)
which implies exists (waiting scheduled: UCOS2_Verify_State) (returned: OsSchedCallContext),
coq_prop(sem_pend_observed_wait_history(environment, critical, sg, context, mask, before, observed, eid, ticks, waiting)) &&
coq_prop(kernel_stack_call_same_call(returned, context)) &&
coq_prop(UCOS2_state_inv(sg, scheduled)) &&
sem_pend_continuation_phase_save_input(SemPendWaitPhase(context, mask, before, observed, eid, ticks, waiting), external, platform, environment, critical, saved_local, sg, returned, mask, scheduled) * unmap_table_rep(sg) */

OS_ENTER_CRITICAL();
/*@ exists (waiting scheduled: UCOS2_Verify_State) (returned: OsSchedCallContext),
coq_prop(sem_pend_observed_wait_history(environment, critical, sg, context, mask, before, observed, eid, ticks, waiting)) &&
coq_prop(kernel_stack_call_same_call(returned, context)) &&
sem_pend_continuation_phase_save_output(SemPendWaitPhase(context, mask, before, observed, eid, ticks, waiting), external, platform, environment, critical, saved_local, sg, returned, mask, cpu_sr, scheduled)
which implies exists (waiting scheduled resumed: UCOS2_Verify_State) (returned second_returned: OsSchedCallContext),
coq_prop(sem_pend_observed_wait_history(environment, critical, sg, context, mask, before, observed, eid, ticks, waiting)) &&
coq_prop(kernel_stack_call_same_call(returned, context)) && coq_prop(kernel_stack_call_same_call(second_returned, context)) &&
coq_prop(sem_pend_stack_save_observation(critical, sg, returned, second_returned, environment, mask, cpu_sr, scheduled, resumed)) &&
coq_prop(sem_pend_save_phase_observation(SemPendWaitPhase(context, mask, before, observed, eid, ticks, waiting), environment, critical, sg, returned, second_returned, mask, cpu_sr, scheduled, resumed)) &&
critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, resumed) *
os_sched_context_resources(external, second_returned) * UCOS2_inv(sg, resumed) *
sem_pend_optional_continuation_resources(external, platform, environment, saved_local, second_returned, resumed) */
    
/*@ exists (waiting scheduled resumed: UCOS2_Verify_State) (returned second_returned: OsSchedCallContext),
coq_prop(sem_pend_observed_wait_history(environment, critical, sg, context, mask, before, observed, eid, ticks, waiting)) &&
coq_prop(kernel_stack_call_same_call(returned, context)) && coq_prop(kernel_stack_call_same_call(second_returned, context)) &&
coq_prop(sem_pend_stack_save_observation(critical, sg, returned, second_returned, environment, mask, cpu_sr, scheduled, resumed)) &&
coq_prop(sem_pend_save_phase_observation(SemPendWaitPhase(context, mask, before, observed, eid, ticks, waiting), environment, critical, sg, returned, second_returned, mask, cpu_sr, scheduled, resumed)) &&
&OSTCBCur == sg.g_OSTCBCur && critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, resumed) * UCOS2_inv(sg, resumed) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, second_returned, resumed) * os_sched_context_resources(external, second_returned)
which implies exists (resumed: UCOS2_Verify_State) (tid: TaskID) (old: TaskAbstractState) (second_returned: OsSchedCallContext),
coq_prop(kernel_stack_call_same_call(second_returned, context)) &&
coq_prop(interrupt_saved_value(mask, cpu_sr)) && coq_prop(sem_pend_observed_resume_origin(environment, critical, sg, context, mask, before, observed, eid, ticks, resumed, tid, old)) &&
critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, resumed) * data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStat), unsigned char, encode_task_status(old.stat)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStatPend), unsigned char, encode_pend_status(old.statPend)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBEventPtr), OS_EVENT *, encode_event_link(sg, old.eventPtr)) *
sem_pend_cleanup_frame(sg, resumed, tid, old) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, second_returned, resumed) * os_sched_context_resources(external, second_returned) */
switch (OSTCBCur->OSTCBStatPend) {                /* See if we timed-out or aborted                */
        case OS_STAT_PEND_OK:
             *perr = OS_ERR_NONE;
             
/*@ exists (resumed: UCOS2_Verify_State) (tid: TaskID) (old: TaskAbstractState) (second_returned: OsSchedCallContext),
coq_prop(kernel_stack_call_same_call(second_returned, context)) &&
coq_prop(sem_pend_observed_resume_origin(environment, critical, sg, context, mask, before, observed, eid, ticks, resumed, tid, old)) && encode_pend_status(old.statPend) == 0 && data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStat), unsigned char, encode_task_status(old.stat)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStatPend), unsigned char, encode_pend_status(old.statPend)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBEventPtr), OS_EVENT *, encode_event_link(sg, old.eventPtr)) *
sem_pend_cleanup_frame(sg, resumed, tid, old) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, second_returned, resumed) * os_sched_context_resources(external, second_returned)
which implies exists (cleaning: UCOS2_Verify_State) (tid: TaskID) (node: TaskAbstractState) (second_returned: OsSchedCallContext),
coq_prop(kernel_stack_call_same_call(second_returned, context)) &&
coq_prop(sem_pend_observed_cleanup_origin(environment, critical, sg, context, mask, before, observed, eid, ticks, 0, cleaning, tid, node)) && data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStat), unsigned char, encode_task_status(node.stat)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStatPend), unsigned char, encode_pend_status(node.statPend)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBEventPtr), OS_EVENT *, encode_event_link(sg, node.eventPtr)) *
sem_pend_cleanup_frame(sg, cleaning, tid, node) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, second_returned, cleaning) * os_sched_context_resources(external, second_returned) */
break;

        case OS_STAT_PEND_ABORT:
             *perr = OS_ERR_PEND_ABORT;               /* Indicate that we aborted                      */
             
/*@ exists (resumed: UCOS2_Verify_State) (tid: TaskID) (old: TaskAbstractState) (second_returned: OsSchedCallContext),
coq_prop(kernel_stack_call_same_call(second_returned, context)) &&
coq_prop(sem_pend_observed_resume_origin(environment, critical, sg, context, mask, before, observed, eid, ticks, resumed, tid, old)) && encode_pend_status(old.statPend) == 2 && data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStat), unsigned char, encode_task_status(old.stat)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStatPend), unsigned char, encode_pend_status(old.statPend)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBEventPtr), OS_EVENT *, encode_event_link(sg, old.eventPtr)) *
sem_pend_cleanup_frame(sg, resumed, tid, old) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, second_returned, resumed) * os_sched_context_resources(external, second_returned)
which implies exists (cleaning: UCOS2_Verify_State) (tid: TaskID) (node: TaskAbstractState) (second_returned: OsSchedCallContext),
coq_prop(kernel_stack_call_same_call(second_returned, context)) &&
coq_prop(sem_pend_observed_cleanup_origin(environment, critical, sg, context, mask, before, observed, eid, ticks, 14, cleaning, tid, node)) && data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStat), unsigned char, encode_task_status(node.stat)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStatPend), unsigned char, encode_pend_status(node.statPend)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBEventPtr), OS_EVENT *, encode_event_link(sg, node.eventPtr)) *
sem_pend_cleanup_frame(sg, cleaning, tid, node) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, second_returned, cleaning) * os_sched_context_resources(external, second_returned) */
break;

        case OS_STAT_PEND_TO:
        default:
             
/*@ exists (resumed: UCOS2_Verify_State) (tid: TaskID) (old: TaskAbstractState) (second_returned: OsSchedCallContext),
coq_prop(kernel_stack_call_same_call(second_returned, context)) &&
coq_prop(sem_pend_observed_resume_origin(environment, critical, sg, context, mask, before, observed, eid, ticks, resumed, tid, old)) &&
encode_pend_status(old.statPend) != 0 && encode_pend_status(old.statPend) != 2 &&
pe == event_addr(sg, eid) && coq_prop(event_object_layout_prop(sg, eid)) && &OSTCBCur == sg.g_OSTCBCur &&
data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStat), unsigned char, encode_task_status(old.stat)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStatPend), unsigned char, encode_pend_status(old.statPend)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBEventPtr), OS_EVENT *, encode_event_link(sg, old.eventPtr)) *
sem_pend_cleanup_frame(sg, resumed, tid, old) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, second_returned, resumed) * os_sched_context_resources(external, second_returned)
which implies exists (resumed: UCOS2_Verify_State) (tid: TaskID) (old: TaskAbstractState) (second_returned: OsSchedCallContext) (current: OSEventAbstractState),
coq_prop(kernel_stack_call_same_call(second_returned, context)) &&
coq_prop(sem_pend_observed_resume_origin(environment, critical, sg, context, mask, before, observed, eid, ticks, resumed, tid, old)) && encode_pend_status(old.statPend) != 0 && encode_pend_status(old.statPend) != 2 &&
coq_prop(mutex_query_lookup(resumed, eid, current)) &&
pe == event_addr(sg, eid) && coq_prop(event_object_layout_prop(sg, eid)) && &OSTCBCur == sg.g_OSTCBCur &&
data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
event_task_remove_pre(task_slot_addr(sg, tid), &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0],
old.curPrio / 8, tcb_bit_x_of_prio(old.curPrio), tcb_bit_y_of_prio(old.curPrio),
encode_event_wait_tbl_at_or(current.waitList, resumed.TskState, old.curPrio / 8),
encode_event_wait_grp(current.waitList, resumed.TskState)) *
sem_pend_remove_call_frame(sg, resumed, eid, current, tid, old) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, second_returned, resumed) * os_sched_context_resources(external, second_returned) */
OS_EventTaskRemove(OSTCBCur, pevent);
             
/*@ exists (resumed: UCOS2_Verify_State) (tid: TaskID) (old: TaskAbstractState) (second_returned: OsSchedCallContext) (current: OSEventAbstractState),
coq_prop(kernel_stack_call_same_call(second_returned, context)) &&
coq_prop(sem_pend_observed_resume_origin(environment, critical, sg, context, mask, before, observed, eid, ticks, resumed, tid, old)) && encode_pend_status(old.statPend) != 0 && encode_pend_status(old.statPend) != 2 &&
coq_prop(mutex_query_lookup(resumed, eid, current)) &&
pe == event_addr(sg, eid) && coq_prop(event_object_layout_prop(sg, eid)) && &OSTCBCur == sg.g_OSTCBCur &&
data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
event_task_remove_post(task_slot_addr(sg, tid), &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0],
old.curPrio / 8, tcb_bit_x_of_prio(old.curPrio), tcb_bit_y_of_prio(old.curPrio),
encode_event_wait_tbl_at_or(current.waitList, resumed.TskState, old.curPrio / 8),
encode_event_wait_grp(current.waitList, resumed.TskState)) *
sem_pend_remove_call_frame(sg, resumed, eid, current, tid, old) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, second_returned, resumed) * os_sched_context_resources(external, second_returned)
which implies exists (cleaning: UCOS2_Verify_State) (tid: TaskID) (node: TaskAbstractState) (second_returned: OsSchedCallContext),
coq_prop(kernel_stack_call_same_call(second_returned, context)) &&
coq_prop(sem_pend_observed_cleanup_origin(environment, critical, sg, context, mask, before, observed, eid, ticks, 10, cleaning, tid, node)) && data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStat), unsigned char, encode_task_status(node.stat)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStatPend), unsigned char, encode_pend_status(node.statPend)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBEventPtr), OS_EVENT *, encode_event_link(sg, node.eventPtr)) *
sem_pend_cleanup_frame(sg, cleaning, tid, node) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, second_returned, cleaning) * os_sched_context_resources(external, second_returned) */
*perr = OS_ERR_TIMEOUT;                  /* Indicate that we didn't get event within TO   */
             break;
    }
    OSTCBCur->OSTCBStat          =  OS_STAT_RDY;      /* Set   task  status to ready                   */
    OSTCBCur->OSTCBStatPend      =  OS_STAT_PEND_OK;  /* Clear pend  status                            */
    OSTCBCur->OSTCBEventPtr      = (OS_EVENT  *)0;    /* Clear event pointers                          */
#if (OS_EVENT_MULTI_EN > 0u)
    OSTCBCur->OSTCBEventMultiPtr = (OS_EVENT **)0;
    OSTCBCur->OSTCBEventMultiRdy = (OS_EVENT  *)0;
#endif
    
/*@ exists (cleaning: UCOS2_Verify_State) (tid: TaskID) (node: TaskAbstractState) (error: Z) (acquired: UCOS2_Verify_State) (second_returned: OsSchedCallContext),
coq_prop(kernel_stack_call_same_call(second_returned, context)) &&
coq_prop(interrupt_saved_value(mask, cpu_sr)) &&
coq_prop(sem_pend_observed_cleanup_origin(environment, critical, sg, context, mask, before, observed, eid, ticks, error, cleaning, tid, node)) && perr == pd &&
pe != 0 && pe == event_addr(sg, eid) && coq_prop(valid_event_id(sg, eid)) &&
coq_prop(sem_query_public_slot(before, eid, observed)) && event_slot_type_value(before.EventState, eid) == 3 &&
before.IntrState.intNesting == 0 && before.IntrState.lockNesting == 0 &&
&OSTCBCur == sg.g_OSTCBCur && data_at(pd, unsigned char, error) *
data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStat), unsigned char, 0) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBStatPend), unsigned char, 0) *
data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBEventPtr), OS_EVENT *, 0) *
sem_pend_cleanup_frame(sg, cleaning, tid, node)
* critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, acquired) *
os_sched_context_resources(external, second_returned) * sem_pend_optional_continuation_resources(external, platform, environment, saved_local, second_returned, cleaning)
which implies exists (after acquired: UCOS2_Verify_State) (error: Z) (second_returned: OsSchedCallContext), perr == pd &&
coq_prop(sem_pend_checkpoint_result(environment, critical, sg, context, pe, ticks, before, error, after)) &&
coq_prop(kernel_stack_call_same_call(second_returned, context)) &&
data_at(pd, unsigned char, error) *
sem_pend_continuation_phase_restore_input(SemPendReturnPhase, external, platform, environment, critical, saved_local, sg, second_returned, mask, cpu_sr, acquired, after) */
OS_EXIT_CRITICAL();

    OS_TRACE_SEM_PEND_EXIT(*perr);
}
