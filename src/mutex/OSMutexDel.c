/* Single-function annotation carrier; compose before canonical QCP.
 * The environment retains the pinned headers, configuration and callees.
 * Formatting and documented frontend form match the checked C input.
 */

OS_EVENT  *OSMutexDel (OS_EVENT  *pevent,
                       INT8U      opt,
                       INT8U     *perr)
/*@ With (source_env: MutexDelCallEnvironment) (external: OsSchedExternalResources) (platform: InterruptPlatformResources)
 (configuration: MutexProgramConfiguration) (saved_local: Armv7aContinuation -> Assertion) (sg: StableGlobVars) (context: OsSchedCallContext)
 (mask: Z) (before: UCOS2_Verify_State) (eid: Z) (observed: OSEventAbstractState)
 (pe opt_in err_in pd: Z) X
 Require pevent == pe && opt == opt_in && perr == pd && perr != 0 &&
   mutex_del_api_refinement_pre(source_env, mutex_program_region(configuration), sg, context, pe, opt_in, eid, before, X) &&
   mutex_del_parent_layout(sg) && mutex_del_parent_input(sg, pe, before, eid, observed) &&
   mutex_del_scheduler_admission(sg, configuration, pe, before, eid, opt_in) &&
   mutex_del_continuation_call_admission(context, before, pe, eid) &&
   mutex_del_continuation_entry(source_env, external, platform, saved_local, sg, context, mask, before) * data_at(perr, unsigned char, err_in)
 Ensure exists code,
   mutex_del_api_return_post(source_env, external, platform, mutex_program_region(configuration), saved_local, sg, context, mask, before,
     pe, opt_in, eid, __return, code, X) * data_at(pd, unsigned char, code)
*/
{
    BOOLEAN    tasks_waiting;
    OS_EVENT  *pevent_return;
    INT8U      pcp;                                        /* Priority ceiling priority                */
    INT8U      prio;
    OS_TCB    *ptcb;
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

    OS_TRACE_MUTEX_DEL_ENTER(pevent, opt);

    
/*@
 mutex_del_continuation_entry(source_env, external, platform, saved_local, sg, context, mask, before)
 which implies
 mutex_query_closed(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, before) *
 mutex_del_continuation_entry_support(source_env, external, platform, saved_local, sg, context, before)
*/

/*@
 mutex_del_parent_layout(sg) &&
 pe != 0 && mutex_del_parent_input(sg, pe, before, eid, observed) && mutex_query_closed(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, before) * data_at(&pevent, OS_EVENT *, pe)
 which implies
 pe == event_addr(sg, eid) && valid_event_id(sg, eid) && UCOS2_state_inv(sg, before) && data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(before.EventState, eid)) * sem_query_type_frame(sg, before, eid) * interrupt_platform_running(platform, os_sched_call_invocation(context), os_sched_call_origin(context), mask) * data_at(&pevent, OS_EVENT *, pe)
*/
if (pevent->OSEventType != OS_EVENT_TYPE_MUTEX) {      /* Validate event block type                */
        
/*@
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 UCOS2_state_inv(sg, before) &&
 data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(before.EventState, eid)) * sem_query_type_frame(sg, before, eid) * interrupt_platform_running(platform, os_sched_call_invocation(context), os_sched_call_origin(context), mask) * data_at(&pevent, OS_EVENT *, pe)
 which implies
 mutex_query_closed(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, before) * data_at(&pevent, OS_EVENT *, pe)
*/

/*@
 mutex_query_closed(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, before) *
 mutex_del_continuation_entry_support(source_env, external, platform, saved_local, sg, context, before)
 which implies
 mutex_del_continuation_entry(source_env, external, platform, saved_local, sg, context, mask, before)
*/
*perr = OS_ERR_EVENT_TYPE;
        OS_TRACE_MUTEX_DEL_EXIT(*perr);
        return (pevent);
    }
    
/*@
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 UCOS2_state_inv(sg, before) &&
 data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(before.EventState, eid)) * sem_query_type_frame(sg, before, eid) * interrupt_platform_running(platform, os_sched_call_invocation(context), os_sched_call_origin(context), mask) * data_at(&pevent, OS_EVENT *, pe)
 which implies
 data_at(&OSIntNesting, unsigned char, intNesting(before.IntrState)) * interrupt_inv_no_int_nesting(sg, before.IntrState) * mutex_query_whole_frame(sg, before) * interrupt_platform_running(platform, os_sched_call_invocation(context), os_sched_call_origin(context), mask) * data_at(&pevent, OS_EVENT *, pe)
*/
if (OSIntNesting > 0u) {                               /* See if called from ISR ...               */
        
/*@
 mutex_del_parent_layout(sg) &&
 UCOS2_state_inv(sg, before) &&
 data_at(&OSIntNesting, unsigned char, intNesting(before.IntrState)) * interrupt_inv_no_int_nesting(sg, before.IntrState) * mutex_query_whole_frame(sg, before) * interrupt_platform_running(platform, os_sched_call_invocation(context), os_sched_call_origin(context), mask)
 which implies
 mutex_query_closed(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, before)
*/

/*@
 mutex_query_closed(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, before) *
 mutex_del_continuation_entry_support(source_env, external, platform, saved_local, sg, context, before)
 which implies
 mutex_del_continuation_entry(source_env, external, platform, saved_local, sg, context, mask, before)
*/
*perr = OS_ERR_DEL_ISR;                            /* ... can't DELETE from an ISR             */
        OS_TRACE_MUTEX_DEL_EXIT(*perr);
        return (pevent);
    }
    
/*@
 mutex_del_parent_layout(sg) &&
 UCOS2_state_inv(sg, before) &&
 pe != 0 && unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
 unsigned_last_nbits(intNesting(before.IntrState), 32) <= 0 &&
 data_at(&OSIntNesting, unsigned char, intNesting(before.IntrState)) * interrupt_inv_no_int_nesting(sg, before.IntrState) * mutex_query_whole_frame(sg, before) * interrupt_platform_running(platform, os_sched_call_invocation(context), os_sched_call_origin(context), mask)
 which implies
 mutex_del_parent_prefix_ok(pe, before, eid) &&
 mutex_query_closed(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, before)
*/

/*@
 mutex_query_closed(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, before) *
 mutex_del_continuation_entry_support(source_env, external, platform, saved_local, sg, context, before)
 which implies
 mutex_del_continuation_entry(source_env, external, platform, saved_local, sg, context, mask, before)
*/

/*@
 mutex_del_continuation_entry(source_env, external, platform, saved_local, sg, context, mask, before)
 which implies
 mutex_program_selected_reachable(sg, before) &&
 mutex_del_continuation_entry(source_env, external, platform, saved_local, sg, context, mask, before)
*/

/*@
 mutex_del_continuation_call_admission(context, before, pe, eid) && mutex_del_parent_prefix_ok(pe, before, eid) &&
 mutex_del_scheduler_admission(sg, configuration, pe, before, eid, opt_in) &&
 mutex_del_continuation_entry(source_env, external, platform, saved_local, sg, context, mask, before)
 which implies
 mutex_del_scheduler_admission(sg, configuration, pe, before, eid, opt_in) &&
 mutex_del_continuation_source_save_pre(source_env, external, platform, mutex_program_region(configuration), saved_local, sg, context, mask, before)
*/
OS_ENTER_CRITICAL();
    /* The earlier type observation may have expired before interrupts were masked. */
    
/*@ Assert
 mutex_del_api_refinement_pre(source_env, mutex_program_region(configuration), sg, context, pe, opt_in, eid, before, X) &&
 pevent == pe && perr == pd && opt == opt_in && perr != 0 && pe == event_addr(sg, eid) &&
 mutex_del_scheduler_admission(sg, configuration, pe, before, eid, opt_in) && mutex_del_parent_layout(sg) && valid_event_id(sg, eid) && mutex_del_parent_prefix_ok(pe, before, eid) && mutex_del_parent_input(sg, pe, before, eid, observed) && UCOS2_state_inv(sg, before) &&
 mutex_program_selected_reachable(sg, before) &&
 mutex_del_continuation_source_save_post(source_env, external, platform, mutex_program_region(configuration), saved_local, sg, context, mask, cpu_sr, before) *
 data_at(pd, unsigned char, err_in) * undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&prio, INT8U) * undef_data_at(&pcp, INT8U) * undef_data_at(&pevent_return, OS_EVENT *) * undef_data_at(&tasks_waiting, BOOLEAN)
*/

/*@ exists saved_v,
 mutex_del_continuation_source_save_post(source_env, external, platform, mutex_program_region(configuration), saved_local, sg, context, mask, saved_v, before) *
 data_at(&cpu_sr, OS_CPU_SR, saved_v)
 which implies
 exists (entry: UCOS2_Verify_State),
 mutex_del_call_stage(context, entry) && kernel_call_stack_available(context, entry) &&
 mutex_del_runtime_save_facts(sg, mask, saved_v, before, entry) &&
 critical_region_masked(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), saved_v, entry) *
 kernel_program_inv(sg, entry) * mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, context, entry) *
 data_at(&cpu_sr, OS_CPU_SR, saved_v)
*/

/*@ exists (entry: UCOS2_Verify_State),
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) && pe == event_addr(sg, eid) &&
 kernel_program_inv(sg, entry) * mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, context, entry)
 which implies
 exists kind,
 data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, kind) *
 mutex_del_continuation_type_frame(source_env, external, platform, saved_local, sg, context, eid, entry, kind)
*/
if (pevent->OSEventType != OS_EVENT_TYPE_MUTEX) {
        
/*@ exists (entry: UCOS2_Verify_State) kind saved_v,
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) && pe == event_addr(sg, eid) &&
 kind != 4 &&
 mutex_del_runtime_save_facts(sg, mask, saved_v, before, entry) &&
 data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, kind) *
 mutex_del_continuation_type_frame(source_env, external, platform, saved_local, sg, context, eid, entry, kind) *
 critical_region_masked(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), saved_v, entry) * data_at(&cpu_sr, OS_CPU_SR, saved_v)
 which implies
 kind != 4 && mutex_del_runtime_type_observation(sg, eid, entry, kind) &&
 mutex_del_runtime_save_facts(sg, mask, saved_v, before, entry) &&
 mutex_del_runtime_program_restore_pre(platform, mutex_program_region(configuration), sg, context, mask, saved_v, before, entry, entry) *
 mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, context, entry) * data_at(&cpu_sr, OS_CPU_SR, saved_v)
*/

/*@ exists (entry: UCOS2_Verify_State) saved_v,
 mutex_del_call_stage(context, entry) && kernel_call_stack_available(context, entry) &&
 mutex_del_runtime_program_restore_pre(platform, mutex_program_region(configuration), sg, context, mask, saved_v, before, entry, entry) *
 mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, context, entry)
 which implies
 mutex_del_call_stage(context, entry) && kernel_call_stack_available(context, entry) &&
 mutex_del_continuation_source_restore_pre(source_env, external, platform, mutex_program_region(configuration), saved_local, sg, context, mask, saved_v, entry, entry)
*/
OS_EXIT_CRITICAL();
        *perr = OS_ERR_EVENT_TYPE;
        OS_TRACE_MUTEX_DEL_EXIT(*perr);
        return (pevent);
    }
    
/*@ exists (entry: UCOS2_Verify_State) kind,
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) && pe == event_addr(sg, eid) &&
 unsigned_last_nbits(kind, 32) == 4 &&
 data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, kind) *
 mutex_del_continuation_type_frame(source_env, external, platform, saved_local, sg, context, eid, entry, kind)
 which implies
 exists (acquired: OSEventAbstractState) (mutex: MutexFields),
 mutex_del_parent_entry(sg, eid, entry, acquired, mutex) &&
 UCOS2_raw_rep(sg, entry) * unmap_table_rep(sg) *
 mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, context, entry)
*/

/*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (mutex: MutexFields),
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 mutex_del_parent_entry(sg, eid, entry, current, mutex) && UCOS2_raw_rep(sg, entry) * data_at(&pevent, OS_EVENT *, pe)
 which implies
 exists initial_group, initial_group == encode_event_wait_grp(waitList(current), entry.TskState) && data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, initial_group) * mutex_del_event_group_frame(sg, entry, eid, current) * data_at(&pevent, OS_EVENT *, pe)
*/
if (pevent->OSEventGrp != 0u) {                        /* See if any tasks waiting on mutex        */
        tasks_waiting = OS_TRUE;                           /* Yes                                      */
    } else {
        tasks_waiting = OS_FALSE;                          /* No                                       */
    }
    
/*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (initial_group: Z),
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 UCOS2_state_inv(sg, entry) &&
 mutex_query_lookup(entry, eid, current) &&
 eq(initial_group, encode_event_wait_grp(waitList(current), entry.TskState)) &&
 data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, initial_group) * mutex_del_event_group_frame(sg, entry, eid, current) * data_at(&pevent, OS_EVENT *, pe)
 which implies
 UCOS2_inv(sg, entry) * data_at(&pevent, OS_EVENT *, pe)
*/
switch (opt) {
        case OS_DEL_NO_PEND:                               /* DELETE MUTEX ONLY IF NO TASK WAITING --- */
             if (tasks_waiting == OS_FALSE) {
#if OS_EVENT_NAME_EN > 0u
                 pevent->OSEventName   = (INT8U *)(void *)"?";
#endif
                 
/*@ exists (entry: UCOS2_Verify_State),
 UCOS2_inv(sg, entry)
 which implies
 UCOS2_raw_rep(sg, entry)
*/

/*@ exists (mutex: MutexFields) (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 mutex_del_parent_entry(sg, eid, entry, current, mutex) && UCOS2_raw_rep(sg, entry) * data_at(&pevent, OS_EVENT *, pe)
 which implies
 exists kind pointer count group free, mutex_del_parent_event_values(sg, entry, eid, current, kind, pointer, count, group, free) && data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, kind) * data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, pointer) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, count) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, group) * data_at(&OSEventFreeList, OS_EVENT *, free) * mutex_del_parent_event_rest(sg, entry, eid, current) * data_at(&pevent, OS_EVENT *, pe)
*/
pcp                   = (INT8U)(pevent->OSEventCnt >> 8u);
                 if (pcp != OS_PRIO_MUTEX_CEIL_DIS) {
                     ptcb = (OS_TCB *)pevent->OSEventPtr;
                     
/*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (kind: Z) (pointer: Z) (count: Z) (group: Z) (free: Z),
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 mutex_query_lookup(entry, eid, current) &&
 mutex_del_parent_event_values(sg, entry, eid, current, kind, pointer, count, group, free) &&
 data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, kind) * data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, pointer) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, count) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, group) * data_at(&OSEventFreeList, OS_EVENT *, free) * mutex_del_parent_event_rest(sg, entry, eid, current) * data_at(&pevent, OS_EVENT *, pe)
 which implies
 UCOS2_raw_rep(sg, entry) * data_at(&pevent, OS_EVENT *, pe)
*/

/*@ exists (entry: UCOS2_Verify_State), exists pcp_v,
 mutex_del_parent_layout(sg) &&
 pcp_v != 255 &&
 mutex_del_parent_ceiling_at(sg, eid, entry, pcp_v) &&
 UCOS2_raw_rep(sg, entry) * data_at(&pcp, INT8U, pcp_v)
 which implies
 exists old_slot, 0 <= pcp_v && pcp_v < 64 && mutex_del_parent_ceiling_at(sg, eid, entry, pcp_v) && data_at(pointer_offset(OSTCBPrioTbl, pcp_v, OS_TCB *), OS_TCB *, old_slot) * store_prio_tbl_missing_i(sg, entry.TskState.prioTbl, pcp_v) * UCOS2_raw_rep_missing_priority_table(sg, entry) * data_at(&pcp, INT8U, pcp_v)
*/
OSTCBPrioTbl[pcp] = (OS_TCB *)0;      /* Free up the PCP                          */
                     
/*@ exists (entry: UCOS2_Verify_State), exists pcp_v,
 mutex_del_parent_layout(sg) &&
 0 <= pcp_v &&
 pcp_v < 64 &&
 data_at(pointer_offset(OSTCBPrioTbl, pcp_v, OS_TCB *), OS_TCB *, 0) * store_prio_tbl_missing_i(sg, entry.TskState.prioTbl, pcp_v) * UCOS2_raw_rep_missing_priority_table(sg, entry) * data_at(&pcp, INT8U, pcp_v)
 which implies
 mutex_del_released_resources(sg, entry, pcp_v) * data_at(&pcp, INT8U, pcp_v)
*/
if (ptcb != (OS_TCB *)0) {
                         
/*@ exists (entry: UCOS2_Verify_State), exists pcp_v ptcb_v,
 mutex_del_parent_layout(sg) &&
 mutex_del_parent_owner_pointer(sg, eid, entry, pcp_v, ptcb_v) &&
 ptcb_v != 0 && mutex_del_released_resources(sg, entry, pcp_v) * data_at(&pcp, INT8U, pcp_v) * data_at(&ptcb, OS_TCB *, ptcb_v)
 which implies
 exists owner (node: TaskAbstractState), eq(ptcb_v, task_slot_addr(sg, owner)) && eq(entry.TskState.inUsedTaskStates(owner), Some(node)) && mutex_del_priority_input(sg, entry, pcp_v, owner, node) * mutex_del_priority_frame(sg, entry, owner) * data_at(&pcp, INT8U, pcp_v) * data_at(&ptcb, OS_TCB *, ptcb_v)
*/

/*@ exists (entry: UCOS2_Verify_State) (node: TaskAbstractState) (owner: Z), exists pcp_v ptcb_v,
 mutex_del_parent_layout(sg) &&
 eq(ptcb_v, task_slot_addr(sg, owner)) &&
 UCOS2_state_inv(sg, entry) &&
 eq(entry.TskState.inUsedTaskStates(owner), Some(node)) &&
 mutex_del_priority_input(sg, entry, pcp_v, owner, node) * data_at(&pcp, INT8U, pcp_v) * data_at(&ptcb, OS_TCB *, ptcb_v)
 which implies
 mutex_priority_image_fields(task_tcb64_image(sg, node), curPrio(node), tcb_x_of_prio(curPrio(node)), tcb_y_of_prio(curPrio(node)), tcb_bit_x_of_prio(curPrio(node)), tcb_bit_y_of_prio(curPrio(node))) && mutex_priority_fallback(task_tcb64_image(sg, node), curPrio(node)) && 0 <= curPrio(node) && curPrio(node) < 64 && 0 <= tcb_y_of_prio(curPrio(node)) && tcb_y_of_prio(curPrio(node)) < 8 && Zlength(mutex_del_priority_values(sg, mutex_del_released_table(entry, pcp_v))) == 64 && Zlength(sched_row_values(entry.TskState, entry.SchedState.readyList)) == 8 && mutex_del_scan_pre(ptcb_v, task_tcb64_image(sg, node), mutex_del_priority_values(sg, mutex_del_released_table(entry, pcp_v)), curPrio(node)) * UCharArray::full(&OSRdyTbl, 8, sched_row_values(entry.TskState, entry.SchedState.readyList)) * data_at(&OSRdyGrp, OS_PRIO, encode_ready_grp(entry.SchedState.readyList, entry.TskState)) * data_at(&OSTCBCur, OS_TCB *, encode_task_link(sg, entry.SchedState.curTaskID)) * data_at(&OSPrioCur, INT8U, sched_priority_byte(entry.SchedState.curSchedPrio)) * data_at(&pcp, INT8U, pcp_v) * data_at(&ptcb, OS_TCB *, ptcb_v)
*/
prio = OSMutex_EffectivePrio(ptcb);
                         
/*@ exists (node: TaskAbstractState), exists ptcb_v,
 tcb64_storage_rep(ptcb_v, task_tcb64_image(sg, node)) * data_at(&ptcb, OS_TCB *, ptcb_v)
 which implies
 data_at(&((OS_TCB *)ptcb_v)->OSTCBPrio, unsigned char, curPrio(node)) * tcb64_storage_without(ptcb_v, TCBPrio, task_tcb64_image(sg, node)) * data_at(&ptcb, OS_TCB *, ptcb_v)
*/
if (ptcb->OSTCBPrio != prio) {
                             OS_TRACE_MUTEX_TASK_PRIO_DISINHERIT(ptcb, prio);
                             
/*@ exists (node: TaskAbstractState), exists ptcb_v,
 data_at(&((OS_TCB *)ptcb_v)->OSTCBPrio, unsigned char, curPrio(node)) * tcb64_storage_without(ptcb_v, TCBPrio, task_tcb64_image(sg, node)) * data_at(&ptcb, OS_TCB *, ptcb_v)
 which implies
 tcb64_storage_rep(ptcb_v, task_tcb64_image(sg, node)) * data_at(&ptcb, OS_TCB *, ptcb_v)
*/

/*@ exists (owner: Z) (entry: UCOS2_Verify_State) (node: TaskAbstractState) pcp_v ptcb_v prio_v,
 mutex_del_parent_layout(sg) &&
 0 <= curPrio(node) && curPrio(node) < 64 &&
 mutex_effective_priority_result(mutex_del_priority_values(sg, mutex_del_released_table(entry, pcp_v)), ptcb_v, curPrio(node), prio_v) &&
 tcb64_storage_rep(ptcb_v, task_tcb64_image(sg, node)) *
 PtrArray::full(&OSTCBPrioTbl, 64, mutex_del_priority_values(sg, mutex_del_released_table(entry, pcp_v))) * UCharArray::full(&OSRdyTbl, 8, sched_row_values(entry.TskState, entry.SchedState.readyList)) *
 data_at(&OSRdyGrp, OS_PRIO, encode_ready_grp(entry.SchedState.readyList, entry.TskState)) * data_at(&OSTCBCur, OS_TCB *, encode_task_link(sg, entry.SchedState.curTaskID)) *
 data_at(&OSPrioCur, INT8U, sched_priority_byte(entry.SchedState.curSchedPrio)) * data_at(&pcp, INT8U, pcp_v) * data_at(&ptcb, OS_TCB *, ptcb_v) * data_at(&prio, INT8U, prio_v) * mutex_del_priority_frame(sg, entry, owner)
 which implies
 mutex_del_rdy_pre(ptcb_v, prio_v, task_tcb64_image(sg, node), mutex_del_priority_values(sg, mutex_del_released_table(entry, pcp_v)), sched_row_values(entry.TskState, entry.SchedState.readyList),
   curPrio(node), tcb_x_of_prio(curPrio(node)), tcb_y_of_prio(curPrio(node)), tcb_bit_x_of_prio(curPrio(node)), tcb_bit_y_of_prio(curPrio(node)), encode_ready_grp(entry.SchedState.readyList, entry.TskState), encode_task_link(sg, entry.SchedState.curTaskID), sched_priority_byte(entry.SchedState.curSchedPrio)) * data_at(&pcp, INT8U, pcp_v) * data_at(&ptcb, OS_TCB *, ptcb_v) * data_at(&prio, INT8U, prio_v) * mutex_del_priority_frame(sg, entry, owner)
*/
OSMutex_RdyAtPrio(ptcb, prio);
                         }
                     }
                 }
                 
/*@ Assert exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (mutex: MutexFields), exists (prepared: UCOS2_Verify_State),
 mutex_del_api_refinement_pre(source_env, mutex_program_region(configuration), sg, context, pe, opt_in, eid, before, X) &&
 pevent == pe && perr == pd && opt == opt_in && opt_in == 0 && pe == event_addr(sg, eid) && tasks_waiting == 0 && encode_event_wait_grp(waitList(current), entry.TskState) == 0 &&
 mutex_del_scheduler_admission(sg, configuration, pe, before, eid, opt_in) && mutex_del_parent_layout(sg) && valid_event_id(sg, eid) && mutex_del_parent_prefix_ok(pe, before, eid) &&
 mutex_del_call_stage(context, entry) && kernel_call_stack_available(context, entry) &&
 mutex_del_runtime_save_facts(sg, mask, cpu_sr, before, entry) && mutex_del_parent_entry(sg, eid, entry, current, mutex) &&
 mutex_del_prepare(sg, mutex, entry, prepared) &&
 mutex_del_parent_prepared(sg, eid, entry, prepared, current, mutex) * unmap_table_rep(sg) *
 mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, context, entry) *
 critical_region_masked(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry) * data_at(pd, unsigned char, err_in) * undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&prio, INT8U) * undef_data_at(&pcp, INT8U) * undef_data_at(&pevent_return, OS_EVENT *)
*/

/*@ exists (entry prepared: UCOS2_Verify_State) (current: OSEventAbstractState) (mutex: MutexFields),
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 mutex_del_parent_prepared(sg, eid, entry, prepared, current, mutex)
 which implies
 exists kind pointer count group free,
 mutex_del_parent_entry(sg, eid, entry, current, mutex) &&
 mutex_del_prepare(sg, mutex, entry, prepared) &&
 mutex_del_wake_state_inv(sg, eid, mutex, prepared) &&
 mutex_del_parent_event_values(sg, prepared, eid, current, kind, pointer, count, group, free) &&
 data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, kind) * data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, pointer) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, count) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, group) * data_at(&OSEventFreeList, OS_EVENT *, free) *
 mutex_del_parent_recycle_rest(sg, eid, entry, prepared, current, mutex)
*/
pevent->OSEventType   = OS_EVENT_TYPE_UNUSED;
                 pevent->OSEventPtr    = OSEventFreeList;  /* Return Event Control Block to free list  */
                 pevent->OSEventCnt    = 0u;
                 OSEventFreeList       = pevent;
                 
/*@ exists (entry prepared: UCOS2_Verify_State) (current: OSEventAbstractState) (mutex: MutexFields)
 group free saved_v,
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 mutex_del_parent_recycle_values(sg, prepared, current, group, free) &&
 opt_in == 0 && encode_event_wait_grp(waitList(current), entry.TskState) == 0 &&
 mutex_del_parent_entry(sg, eid, entry, current, mutex) &&
 mutex_del_prepare(sg, mutex, entry, prepared) &&
 mutex_del_wake_state_inv(sg, eid, mutex, prepared) &&
 mutex_del_runtime_save_facts(sg, mask, saved_v, before, entry) &&
 data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, 0) * data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, free) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, 0) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, group) * data_at(&OSEventFreeList, OS_EVENT *, pe) * mutex_del_parent_recycle_rest(sg, eid, entry, prepared, current, mutex) *
 unmap_table_rep(sg) * critical_region_masked(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), saved_v, entry) * data_at(&cpu_sr, OS_CPU_SR, saved_v)
 which implies
 exists (checkpoint: UCOS2_Verify_State),
 mutex_del_parent_critical_observation(sg, eid, opt_in, 0, 0, 0, entry, checkpoint) &&
 mutex_del_runtime_save_facts(sg, mask, saved_v, before, entry) &&
 mutex_del_runtime_program_restore_pre(platform, mutex_program_region(configuration), sg, context, mask, saved_v, before, entry, checkpoint) *
 data_at(&cpu_sr, OS_CPU_SR, saved_v)
*/

/*@ exists (entry checkpoint : UCOS2_Verify_State) saved_v result_v error_v request_v,
 mutex_del_call_stage(context, entry) && kernel_call_stack_available(context, entry) &&
 mutex_del_parent_critical_observation(sg, eid, opt_in, result_v, error_v, request_v, entry, checkpoint) &&
 mutex_del_runtime_program_restore_pre(platform, mutex_program_region(configuration), sg, context, mask, saved_v, before, entry, checkpoint) *
 mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, context, entry)
 which implies
 mutex_del_call_stage(context, entry) && kernel_call_stack_available(context, entry) &&
 mutex_del_schedule_request(context, request_v) &&
 mutex_del_continuation_source_restore_pre(source_env, external, platform, mutex_program_region(configuration), saved_local, sg, context, mask, saved_v, entry, checkpoint)
*/
OS_EXIT_CRITICAL();
                 
/*@ exists (checkpoint: UCOS2_Verify_State),
 mutex_del_api_restore_source_post(source_env, external, platform, mutex_program_region(configuration), saved_local, sg, context, mask, checkpoint)
 which implies
 exists (returned: OsSchedCallContext) (current: UCOS2_Verify_State),
 mutex_api_restore_history(source_env, mutex_program_region(configuration), sg, context, checkpoint, returned, current) &&
 kernel_stack_call_same_call(returned, context) &&
 mutex_del_continuation_source_return_at(source_env, external, platform, saved_local, sg, context, mask, returned, current)
*/
*perr                 = OS_ERR_NONE;
                 pevent_return         = (OS_EVENT *)0;    /* Mutex has been deleted                   */
             } else {
                 
/*@ exists (entry: UCOS2_Verify_State) saved_v,
 mutex_del_call_stage(context, entry) && kernel_call_stack_available(context, entry) &&
 mutex_del_parent_layout(sg) &&
 pe == event_addr(sg, eid) &&
 opt_in == 0 && mutex_del_parent_waiting(sg, eid, entry) &&
 mutex_del_runtime_save_facts(sg, mask, saved_v, before, entry) &&
 UCOS2_inv(sg, entry) * unmap_table_rep(sg) * critical_region_masked(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), saved_v, entry) *
 data_at(&cpu_sr, OS_CPU_SR, saved_v)
 which implies
 mutex_del_parent_critical_observation(sg, eid, opt_in, pe, 73, 0, entry, entry) &&
 mutex_del_runtime_save_facts(sg, mask, saved_v, before, entry) &&
 mutex_del_runtime_program_restore_pre(platform, mutex_program_region(configuration), sg, context, mask, saved_v, before, entry, entry) *
 data_at(&cpu_sr, OS_CPU_SR, saved_v)
*/

/*@ exists (entry : UCOS2_Verify_State) saved_v,
 mutex_del_call_stage(context, entry) && kernel_call_stack_available(context, entry) &&
 mutex_del_runtime_program_restore_pre(platform, mutex_program_region(configuration), sg, context, mask, saved_v, before, entry, entry) *
 mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, context, entry)
 which implies
 mutex_del_call_stage(context, entry) && kernel_call_stack_available(context, entry) &&
 mutex_del_continuation_source_restore_pre(source_env, external, platform, mutex_program_region(configuration), saved_local, sg, context, mask, saved_v, entry, entry)
*/
OS_EXIT_CRITICAL();
                 
/*@ exists (checkpoint: UCOS2_Verify_State),
 mutex_del_api_restore_source_post(source_env, external, platform, mutex_program_region(configuration), saved_local, sg, context, mask, checkpoint)
 which implies
 exists (returned: OsSchedCallContext) (current: UCOS2_Verify_State),
 mutex_api_restore_history(source_env, mutex_program_region(configuration), sg, context, checkpoint, returned, current) &&
 kernel_stack_call_same_call(returned, context) &&
 mutex_del_continuation_source_return_at(source_env, external, platform, saved_local, sg, context, mask, returned, current)
*/
*perr                 = OS_ERR_TASK_WAITING;
                 pevent_return         = pevent;
             }
             break;

        case OS_DEL_ALWAYS:                                /* ALWAYS DELETE THE MUTEX ---------------- */
             
/*@ exists (entry: UCOS2_Verify_State),
 UCOS2_inv(sg, entry)
 which implies
 UCOS2_raw_rep(sg, entry)
*/

/*@ exists (mutex: MutexFields) (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 mutex_del_parent_entry(sg, eid, entry, current, mutex) && UCOS2_raw_rep(sg, entry) * data_at(&pevent, OS_EVENT *, pe)
 which implies
 exists kind pointer count group free, mutex_del_parent_event_values(sg, entry, eid, current, kind, pointer, count, group, free) && data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, kind) * data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, pointer) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, count) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, group) * data_at(&OSEventFreeList, OS_EVENT *, free) * mutex_del_parent_event_rest(sg, entry, eid, current) * data_at(&pevent, OS_EVENT *, pe)
*/
pcp  = (INT8U)(pevent->OSEventCnt >> 8u);                       /* Get PCP of mutex       */
             if (pcp != OS_PRIO_MUTEX_CEIL_DIS) {
                 ptcb = (OS_TCB *)pevent->OSEventPtr;
                 
/*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (kind: Z) (pointer: Z) (count: Z) (group: Z) (free: Z),
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 mutex_query_lookup(entry, eid, current) &&
 mutex_del_parent_event_values(sg, entry, eid, current, kind, pointer, count, group, free) &&
 data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, kind) * data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, pointer) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, count) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, group) * data_at(&OSEventFreeList, OS_EVENT *, free) * mutex_del_parent_event_rest(sg, entry, eid, current) * data_at(&pevent, OS_EVENT *, pe)
 which implies
 UCOS2_raw_rep(sg, entry) * data_at(&pevent, OS_EVENT *, pe)
*/

/*@ exists (entry: UCOS2_Verify_State), exists pcp_v,
 mutex_del_parent_layout(sg) &&
 pcp_v != 255 &&
 mutex_del_parent_ceiling_at(sg, eid, entry, pcp_v) &&
 UCOS2_raw_rep(sg, entry) * data_at(&pcp, INT8U, pcp_v)
 which implies
 exists old_slot, 0 <= pcp_v && pcp_v < 64 && mutex_del_parent_ceiling_at(sg, eid, entry, pcp_v) && data_at(pointer_offset(OSTCBPrioTbl, pcp_v, OS_TCB *), OS_TCB *, old_slot) * store_prio_tbl_missing_i(sg, entry.TskState.prioTbl, pcp_v) * UCOS2_raw_rep_missing_priority_table(sg, entry) * data_at(&pcp, INT8U, pcp_v)
*/
OSTCBPrioTbl[pcp] = (OS_TCB *)0;
                 
/*@ exists (entry: UCOS2_Verify_State), exists pcp_v,
 mutex_del_parent_layout(sg) &&
 0 <= pcp_v &&
 pcp_v < 64 &&
 data_at(pointer_offset(OSTCBPrioTbl, pcp_v, OS_TCB *), OS_TCB *, 0) * store_prio_tbl_missing_i(sg, entry.TskState.prioTbl, pcp_v) * UCOS2_raw_rep_missing_priority_table(sg, entry) * data_at(&pcp, INT8U, pcp_v)
 which implies
 mutex_del_released_resources(sg, entry, pcp_v) * data_at(&pcp, INT8U, pcp_v)
*/
if (ptcb != (OS_TCB *)0) {                /* See if any task owns the mutex           */
                     
/*@ exists (entry: UCOS2_Verify_State), exists pcp_v ptcb_v,
 mutex_del_parent_layout(sg) &&
 mutex_del_parent_owner_pointer(sg, eid, entry, pcp_v, ptcb_v) &&
 ptcb_v != 0 && mutex_del_released_resources(sg, entry, pcp_v) * data_at(&pcp, INT8U, pcp_v) * data_at(&ptcb, OS_TCB *, ptcb_v)
 which implies
 exists owner (node: TaskAbstractState), eq(ptcb_v, task_slot_addr(sg, owner)) && eq(entry.TskState.inUsedTaskStates(owner), Some(node)) && mutex_del_priority_input(sg, entry, pcp_v, owner, node) * mutex_del_priority_frame(sg, entry, owner) * data_at(&pcp, INT8U, pcp_v) * data_at(&ptcb, OS_TCB *, ptcb_v)
*/

/*@ exists (entry: UCOS2_Verify_State) (node: TaskAbstractState) (owner: Z), exists pcp_v ptcb_v,
 mutex_del_parent_layout(sg) &&
 eq(ptcb_v, task_slot_addr(sg, owner)) &&
 UCOS2_state_inv(sg, entry) &&
 eq(entry.TskState.inUsedTaskStates(owner), Some(node)) &&
 mutex_del_priority_input(sg, entry, pcp_v, owner, node) * data_at(&pcp, INT8U, pcp_v) * data_at(&ptcb, OS_TCB *, ptcb_v)
 which implies
 mutex_priority_image_fields(task_tcb64_image(sg, node), curPrio(node), tcb_x_of_prio(curPrio(node)), tcb_y_of_prio(curPrio(node)), tcb_bit_x_of_prio(curPrio(node)), tcb_bit_y_of_prio(curPrio(node))) && mutex_priority_fallback(task_tcb64_image(sg, node), curPrio(node)) && 0 <= curPrio(node) && curPrio(node) < 64 && 0 <= tcb_y_of_prio(curPrio(node)) && tcb_y_of_prio(curPrio(node)) < 8 && Zlength(mutex_del_priority_values(sg, mutex_del_released_table(entry, pcp_v))) == 64 && Zlength(sched_row_values(entry.TskState, entry.SchedState.readyList)) == 8 && mutex_del_scan_pre(ptcb_v, task_tcb64_image(sg, node), mutex_del_priority_values(sg, mutex_del_released_table(entry, pcp_v)), curPrio(node)) * UCharArray::full(&OSRdyTbl, 8, sched_row_values(entry.TskState, entry.SchedState.readyList)) * data_at(&OSRdyGrp, OS_PRIO, encode_ready_grp(entry.SchedState.readyList, entry.TskState)) * data_at(&OSTCBCur, OS_TCB *, encode_task_link(sg, entry.SchedState.curTaskID)) * data_at(&OSPrioCur, INT8U, sched_priority_byte(entry.SchedState.curSchedPrio)) * data_at(&pcp, INT8U, pcp_v) * data_at(&ptcb, OS_TCB *, ptcb_v)
*/
prio = OSMutex_EffectivePrio(ptcb);
                     
/*@ exists (node: TaskAbstractState), exists ptcb_v,
 tcb64_storage_rep(ptcb_v, task_tcb64_image(sg, node)) * data_at(&ptcb, OS_TCB *, ptcb_v)
 which implies
 data_at(&((OS_TCB *)ptcb_v)->OSTCBPrio, unsigned char, curPrio(node)) * tcb64_storage_without(ptcb_v, TCBPrio, task_tcb64_image(sg, node)) * data_at(&ptcb, OS_TCB *, ptcb_v)
*/
if (ptcb->OSTCBPrio != prio) {
                         OS_TRACE_MUTEX_TASK_PRIO_DISINHERIT(ptcb, prio);
                         
/*@ exists (node: TaskAbstractState), exists ptcb_v,
 data_at(&((OS_TCB *)ptcb_v)->OSTCBPrio, unsigned char, curPrio(node)) * tcb64_storage_without(ptcb_v, TCBPrio, task_tcb64_image(sg, node)) * data_at(&ptcb, OS_TCB *, ptcb_v)
 which implies
 tcb64_storage_rep(ptcb_v, task_tcb64_image(sg, node)) * data_at(&ptcb, OS_TCB *, ptcb_v)
*/

/*@ exists (owner: Z) (entry: UCOS2_Verify_State) (node: TaskAbstractState) pcp_v ptcb_v prio_v,
 mutex_del_parent_layout(sg) &&
 0 <= curPrio(node) && curPrio(node) < 64 &&
 mutex_effective_priority_result(mutex_del_priority_values(sg, mutex_del_released_table(entry, pcp_v)), ptcb_v, curPrio(node), prio_v) &&
 tcb64_storage_rep(ptcb_v, task_tcb64_image(sg, node)) *
 PtrArray::full(&OSTCBPrioTbl, 64, mutex_del_priority_values(sg, mutex_del_released_table(entry, pcp_v))) * UCharArray::full(&OSRdyTbl, 8, sched_row_values(entry.TskState, entry.SchedState.readyList)) *
 data_at(&OSRdyGrp, OS_PRIO, encode_ready_grp(entry.SchedState.readyList, entry.TskState)) * data_at(&OSTCBCur, OS_TCB *, encode_task_link(sg, entry.SchedState.curTaskID)) *
 data_at(&OSPrioCur, INT8U, sched_priority_byte(entry.SchedState.curSchedPrio)) * data_at(&pcp, INT8U, pcp_v) * data_at(&ptcb, OS_TCB *, ptcb_v) * data_at(&prio, INT8U, prio_v) * mutex_del_priority_frame(sg, entry, owner)
 which implies
 mutex_del_rdy_pre(ptcb_v, prio_v, task_tcb64_image(sg, node), mutex_del_priority_values(sg, mutex_del_released_table(entry, pcp_v)), sched_row_values(entry.TskState, entry.SchedState.readyList),
   curPrio(node), tcb_x_of_prio(curPrio(node)), tcb_y_of_prio(curPrio(node)), tcb_bit_x_of_prio(curPrio(node)), tcb_bit_y_of_prio(curPrio(node)), encode_ready_grp(entry.SchedState.readyList, entry.TskState), encode_task_link(sg, entry.SchedState.curTaskID), sched_priority_byte(entry.SchedState.curSchedPrio)) * data_at(&pcp, INT8U, pcp_v) * data_at(&ptcb, OS_TCB *, ptcb_v) * data_at(&prio, INT8U, prio_v) * mutex_del_priority_frame(sg, entry, owner)
*/
OSMutex_RdyAtPrio(ptcb, prio);
                     }
                 }
             }
             
/*@ Assert exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (mutex: MutexFields), exists (prepared: UCOS2_Verify_State),
 mutex_del_api_refinement_pre(source_env, mutex_program_region(configuration), sg, context, pe, opt_in, eid, before, X) &&
 pevent == pe && perr == pd && opt == opt_in && opt_in == 1 && pe == event_addr(sg, eid) &&
 mutex_del_parent_waiting_flag(entry, current, tasks_waiting) &&
 mutex_del_scheduler_admission(sg, configuration, pe, before, eid, opt_in) && mutex_del_parent_layout(sg) && valid_event_id(sg, eid) && mutex_del_parent_prefix_ok(pe, before, eid) &&
 mutex_del_call_stage(context, entry) && kernel_call_stack_available(context, entry) &&
 mutex_del_runtime_save_facts(sg, mask, cpu_sr, before, entry) && mutex_del_parent_entry(sg, eid, entry, current, mutex) &&
 mutex_del_prepare(sg, mutex, entry, prepared) &&
 mutex_del_parent_prepared(sg, eid, entry, prepared, current, mutex) * unmap_table_rep(sg) *
 mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, context, entry) *
 critical_region_masked(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry) * data_at(pd, unsigned char, err_in) * undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&prio, INT8U) * undef_data_at(&pcp, INT8U) * undef_data_at(&pevent_return, OS_EVENT *)
*/

/*@ exists (entry prepared: UCOS2_Verify_State) (current: OSEventAbstractState) (mutex: MutexFields),
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 mutex_del_parent_prepared(sg, eid, entry, prepared, current, mutex) * unmap_table_rep(sg)
 which implies
 mutex_del_parent_loop_rest(sg, eid, entry, prepared, prepared, current, current, mutex, nil) *
 data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, encode_event_wait_grp(waitList(current), prepared.TskState))
*/

/*@ Inv exists (entry prepared state: UCOS2_Verify_State) (current event: OSEventAbstractState) (mutex: MutexFields) (priorities: list Z),
 mutex_del_api_refinement_pre(source_env, mutex_program_region(configuration), sg, context, pe, opt_in, eid, before, X) &&
 pevent == pe && perr == pd && opt == opt_in && opt_in == 1 &&
 pe == event_addr(sg, eid) && mutex_del_scheduler_admission(sg, configuration, pe, before, eid, opt_in) && mutex_del_parent_layout(sg) && valid_event_id(sg, eid) && mutex_del_parent_prefix_ok(pe, before, eid) &&
 mutex_del_parent_waiting_flag(entry, current, tasks_waiting) &&
 mutex_del_call_stage(context, entry) && kernel_call_stack_available(context, entry) &&
 mutex_del_runtime_save_facts(sg, mask, cpu_sr, before, entry) &&
 mutex_del_parent_loop_rest(sg, eid, entry, prepared, state, current, event, mutex, priorities) *
 data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, encode_event_wait_grp(waitList(event), state.TskState)) *
 mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, context, entry) *
 critical_region_masked(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry) *
 data_at(pd, unsigned char, err_in) * undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&prio, INT8U) * undef_data_at(&pcp, INT8U) * undef_data_at(&pevent_return, OS_EVENT *)
*/
while (pevent->OSEventGrp != 0u) {            /* Ready ALL tasks waiting for mutex        */
                 
/*@ exists (entry prepared state: UCOS2_Verify_State) (current event: OSEventAbstractState) (mutex: MutexFields) (priorities: list Z),
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 encode_event_wait_grp(waitList(event), state.TskState) != 0 &&
 mutex_del_parent_loop_rest(sg, eid, entry, prepared, state, current, event, mutex, priorities) *
 data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, encode_event_wait_grp(waitList(event), state.TskState))
 which implies
 exists tid (old: TaskAbstractState),
 event_task_rdy_pre(sg, state.TskState, eid, event, tid, old, 16, 2, encode_ready_grp(state.SchedState.readyList, state.TskState), sched_row_values(state.TskState, state.SchedState.readyList)) *
 mutex_del_parent_wake_call_rest(sg, eid, entry, prepared, state, current, event, mutex, priorities, tid, old)
*/
(void)OS_EventTaskRdy(pevent, (void *)0, OS_STAT_MUTEX, OS_STAT_PEND_ABORT);
             
/*@ exists (entry prepared state: UCOS2_Verify_State) (current event: OSEventAbstractState) (mutex: MutexFields) (priorities: list Z), exists tid (old: TaskAbstractState) priority,
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 event_task_rdy_post(sg, state.TskState, eid, event, tid, old, 0, 16, 2, encode_ready_grp(state.SchedState.readyList, state.TskState), sched_row_values(state.TskState, state.SchedState.readyList), priority) *
 mutex_del_parent_wake_call_rest(sg, eid, entry, prepared, state, current, event, mutex, priorities, tid, old)
 which implies
 exists (after: UCOS2_Verify_State) (next: OSEventAbstractState) (done: list Z),
 mutex_del_parent_loop_rest(sg, eid, entry, prepared, after, current, next, mutex, done) *
 data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, encode_event_wait_grp(waitList(next), after.TskState))
*/
}

/*@ exists (entry prepared state: UCOS2_Verify_State) (current event: OSEventAbstractState) (mutex: MutexFields) (priorities: list Z),
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 encode_event_wait_grp(waitList(event), state.TskState) == 0 &&
 mutex_del_parent_loop_rest(sg, eid, entry, prepared, state, current, event, mutex, priorities) *
 data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, 0)
 which implies
 mutex_del_parent_drained(sg, eid, entry, prepared, state, current, event, mutex, priorities)
*/
#if OS_EVENT_NAME_EN > 0u
             pevent->OSEventName   = (INT8U *)(void *)"?";
#endif
             
/*@ exists (entry prepared state: UCOS2_Verify_State) (current event: OSEventAbstractState) (mutex: MutexFields) (priorities: list Z),
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 mutex_del_parent_drained(sg, eid, entry, prepared, state, current, event, mutex, priorities)
 which implies
 exists kind pointer count group free,
 mutex_del_parent_event_values(sg, state, eid, event, kind, pointer, count, group, free) &&
 data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, kind) * data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, pointer) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, count) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, group) * data_at(&OSEventFreeList, OS_EVENT *, free) * mutex_del_parent_drained_rest(sg, eid, entry, prepared, state, current, event, mutex, priorities)
*/
pcp                   = (INT8U)(pevent->OSEventCnt >> 8u);
             
/*@ exists (entry prepared state: UCOS2_Verify_State) (current event: OSEventAbstractState) (mutex: MutexFields) (priorities: list Z), exists kind pointer count group free pcp_v,
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 mutex_del_parent_event_values(sg, state, eid, event, kind, pointer, count, group, free) &&
 eq(pcp_v, (count >> 8)) &&
 data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, kind) * data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, pointer) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, count) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, group) * data_at(&OSEventFreeList, OS_EVENT *, free) * mutex_del_parent_drained_rest(sg, eid, entry, prepared, state, current, event, mutex, priorities) * data_at(&pcp, INT8U, pcp_v)
 which implies
 mutex_del_parent_ceiling(mutex, pcp_v) && mutex_del_parent_drained(sg, eid, entry, prepared, state, current, event, mutex, priorities) * data_at(&pcp, INT8U, pcp_v)
*/
if (pcp != OS_PRIO_MUTEX_CEIL_DIS) {
                 
/*@ exists (entry prepared state: UCOS2_Verify_State) (current event: OSEventAbstractState) (mutex: MutexFields) (priorities: list Z), exists pcp_v,
 mutex_del_parent_layout(sg) &&
 mutex_del_parent_ceiling(mutex, pcp_v) && pcp_v != 255 &&
 mutex_del_parent_drained(sg, eid, entry, prepared, state, current, event, mutex, priorities) * data_at(&pcp, INT8U, pcp_v)
 which implies
 0 <= pcp_v && pcp_v < 64 &&
 data_at(pointer_offset(OSTCBPrioTbl, pcp_v, OS_TCB *), OS_TCB *, 0) *
 store_prio_tbl_missing_i(sg, state.TskState.prioTbl, pcp_v) *
 mutex_del_parent_drained_without_priority(sg, eid, entry, prepared, state, current, event, mutex, priorities) * data_at(&pcp, INT8U, pcp_v)
*/
OSTCBPrioTbl[pcp] = (OS_TCB *)0;          /* Free up the PCP                          */
             
/*@ exists (entry prepared state: UCOS2_Verify_State) (current event: OSEventAbstractState) (mutex: MutexFields) (priorities: list Z), exists pcp_v,
 mutex_del_parent_layout(sg) &&
 mutex_del_parent_ceiling(mutex, pcp_v) && pcp_v != 255 &&
 data_at(pointer_offset(OSTCBPrioTbl, pcp_v, OS_TCB *), OS_TCB *, 0) *
 store_prio_tbl_missing_i(sg, state.TskState.prioTbl, pcp_v) *
 mutex_del_parent_drained_without_priority(sg, eid, entry, prepared, state, current, event, mutex, priorities) * data_at(&pcp, INT8U, pcp_v)
 which implies
 mutex_del_parent_drained(sg, eid, entry, prepared, state, current, event, mutex, priorities) * data_at(&pcp, INT8U, pcp_v)
*/
}
             
/*@ exists (entry prepared state: UCOS2_Verify_State) (current event: OSEventAbstractState) (mutex: MutexFields) (priorities: list Z),
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 mutex_del_parent_drained(sg, eid, entry, prepared, state, current, event, mutex, priorities)
 which implies
 exists kind pointer count group free,
 mutex_del_parent_event_values(sg, state, eid, event, kind, pointer, count, group, free) &&
 data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, kind) * data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, pointer) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, count) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, group) * data_at(&OSEventFreeList, OS_EVENT *, free) * mutex_del_parent_drained_rest(sg, eid, entry, prepared, state, current, event, mutex, priorities)
*/
pevent->OSEventType   = OS_EVENT_TYPE_UNUSED;
             pevent->OSEventPtr    = OSEventFreeList;      /* Return Event Control Block to free list  */
             pevent->OSEventCnt    = 0u;
             OSEventFreeList       = pevent;               /* Get next free event control block        */
             
/*@ exists (entry prepared state: UCOS2_Verify_State) (current event: OSEventAbstractState) (mutex: MutexFields) (priorities: list Z), exists group free saved_v waiting_v,
 mutex_del_parent_layout(sg) && valid_event_id(sg, eid) &&
 pe == event_addr(sg, eid) &&
 mutex_del_parent_recycle_values(sg, state, event, group, free) &&
 opt_in == 1 && mutex_del_parent_waiting_flag(entry, current, waiting_v) &&
 mutex_del_runtime_save_facts(sg, mask, saved_v, before, entry) &&
 data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, 0) * data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, free) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, 0) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, group) * data_at(&OSEventFreeList, OS_EVENT *, pe) *
 mutex_del_parent_drained_rest(sg, eid, entry, prepared, state, current, event, mutex, priorities) *
 critical_region_masked(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), saved_v, entry) *
 data_at(&cpu_sr, OS_CPU_SR, saved_v) * data_at(&tasks_waiting, BOOLEAN, waiting_v)
 which implies
 exists (checkpoint: UCOS2_Verify_State),
 mutex_del_parent_critical_observation(sg, eid, opt_in, 0, 0, waiting_v, entry, checkpoint) &&
 mutex_del_runtime_save_facts(sg, mask, saved_v, before, entry) &&
 (waiting_v == 0 || waiting_v == 1) &&
 mutex_del_runtime_program_restore_pre(platform, mutex_program_region(configuration), sg, context, mask, saved_v, before, entry, checkpoint) *
 data_at(&cpu_sr, OS_CPU_SR, saved_v) * data_at(&tasks_waiting, BOOLEAN, waiting_v)
*/

/*@ exists (entry checkpoint : UCOS2_Verify_State) saved_v result_v error_v request_v,
 mutex_del_call_stage(context, entry) && kernel_call_stack_available(context, entry) &&
 mutex_del_parent_critical_observation(sg, eid, opt_in, result_v, error_v, request_v, entry, checkpoint) &&
 mutex_del_runtime_program_restore_pre(platform, mutex_program_region(configuration), sg, context, mask, saved_v, before, entry, checkpoint) *
 mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, context, entry)
 which implies
 mutex_del_call_stage(context, entry) && kernel_call_stack_available(context, entry) &&
 mutex_del_schedule_request(context, request_v) &&
 mutex_del_continuation_source_restore_pre(source_env, external, platform, mutex_program_region(configuration), saved_local, sg, context, mask, saved_v, entry, checkpoint)
*/
OS_EXIT_CRITICAL();
             
/*@ exists (checkpoint: UCOS2_Verify_State),
 mutex_del_api_restore_source_post(source_env, external, platform, mutex_program_region(configuration), saved_local, sg, context, mask, checkpoint)
 which implies
 exists (returned: OsSchedCallContext) (current: UCOS2_Verify_State),
 mutex_api_restore_history(source_env, mutex_program_region(configuration), sg, context, checkpoint, returned, current) &&
 kernel_stack_call_same_call(returned, context) &&
 mutex_del_continuation_source_return_at(source_env, external, platform, saved_local, sg, context, mask, returned, current)
*/
if (tasks_waiting == OS_TRUE) {               /* Reschedule only if task(s) were waiting  */
                 
/*@ exists (current: UCOS2_Verify_State) (returned: OsSchedCallContext),
 mutex_del_schedule_request(context, 1) &&
 mutex_del_continuation_source_return_at(source_env, external, platform, saved_local, sg, context, mask, returned, current)
 which implies
 mutex_del_continuation_source_sched_pre(source_env, external, platform, saved_local, sg, returned, mask, current)
*/
/*@ exists (current: UCOS2_Verify_State) (returned: OsSchedCallContext),
 mutex_del_parent_layout(sg) && mutex_del_scheduler_admission(sg, configuration, pe, before, eid, opt_in) &&
 mutex_del_parent_prefix_ok(pe, before, eid) && opt_in == 1 &&
 mutex_del_continuation_source_sched_pre(source_env, external, platform, saved_local, sg, returned, mask, current)
 which implies
 mutex_del_callsite_environment(source_env, external, platform) &&
 os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
   &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
   &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 kernel_sched_ready_clients(mutex_program_region(configuration)) &&
 os_sched_continuation_call_pre(mutex_del_runtime_sched_environment(source_env), saved_local,
   mutex_del_stack_resources, sg, returned, mask, current)
*/
OS_Sched();
/*@ exists (current checkpoint: UCOS2_Verify_State) (returned: OsSchedCallContext),
 mutex_del_callsite_environment(source_env, external, platform) &&
 mutex_api_restore_history(source_env, mutex_program_region(configuration), sg, context, checkpoint, returned, current) &&
 sched_del_history_return_post(mutex_del_runtime_sched_environment(source_env), mutex_program_region(configuration),
   saved_local, sg, returned, mask, current)
 which implies
 mutex_api_tail_post(source_env, external, platform, mutex_program_region(configuration), saved_local, sg, context, mask, checkpoint, 1)
*/
                               /* Find highest priority task ready to run  */
             

}
             *perr         = OS_ERR_NONE;
             pevent_return = (OS_EVENT *)0;                /* Mutex has been deleted                   */
             break;

        default:
             
/*@ exists (entry: UCOS2_Verify_State) saved_v,
 mutex_del_call_stage(context, entry) && kernel_call_stack_available(context, entry) &&
 mutex_del_parent_layout(sg) &&
 pe == event_addr(sg, eid) &&
 opt_in != 0 && opt_in != 1 &&
 mutex_del_parent_live(sg, eid, entry) &&
 mutex_del_runtime_save_facts(sg, mask, saved_v, before, entry) &&
 UCOS2_inv(sg, entry) * unmap_table_rep(sg) * critical_region_masked(platform, mutex_program_region(configuration), sg, os_sched_call_invocation(context), os_sched_call_origin(context), saved_v, entry) *
 data_at(&cpu_sr, OS_CPU_SR, saved_v)
 which implies
 mutex_del_parent_critical_observation(sg, eid, opt_in, pe, 7, 0, entry, entry) &&
 mutex_del_runtime_save_facts(sg, mask, saved_v, before, entry) &&
 mutex_del_runtime_program_restore_pre(platform, mutex_program_region(configuration), sg, context, mask, saved_v, before, entry, entry) *
 data_at(&cpu_sr, OS_CPU_SR, saved_v)
*/

/*@ exists (entry : UCOS2_Verify_State) saved_v,
 mutex_del_call_stage(context, entry) && kernel_call_stack_available(context, entry) &&
 mutex_del_runtime_program_restore_pre(platform, mutex_program_region(configuration), sg, context, mask, saved_v, before, entry, entry) *
 mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, context, entry)
 which implies
 mutex_del_call_stage(context, entry) && kernel_call_stack_available(context, entry) &&
 mutex_del_continuation_source_restore_pre(source_env, external, platform, mutex_program_region(configuration), saved_local, sg, context, mask, saved_v, entry, entry)
*/
OS_EXIT_CRITICAL();
             
/*@ exists (checkpoint: UCOS2_Verify_State),
 mutex_del_api_restore_source_post(source_env, external, platform, mutex_program_region(configuration), saved_local, sg, context, mask, checkpoint)
 which implies
 exists (returned: OsSchedCallContext) (current: UCOS2_Verify_State),
 mutex_api_restore_history(source_env, mutex_program_region(configuration), sg, context, checkpoint, returned, current) &&
 kernel_stack_call_same_call(returned, context) &&
 mutex_del_continuation_source_return_at(source_env, external, platform, saved_local, sg, context, mask, returned, current)
*/
*perr         = OS_ERR_INVALID_OPT;
             pevent_return = pevent;
             break;
    }

    OS_TRACE_MUTEX_DEL_EXIT(*perr);

    return (pevent_return);
}
