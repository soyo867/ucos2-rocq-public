/* Single-function annotation carrier; compose before canonical QCP.
 * The environment retains the pinned headers, configuration and callees.
 * Formatting and documented frontend form match the checked C input.
 */

void  OSMutexPend (OS_EVENT  *pevent,
                   INT32U     timeout,
                   INT8U     *perr)
/*@ With (external: OsSchedExternalResources) (platform: InterruptPlatformResources)
         (critical: CriticalRegionResources) (sg: StableGlobVars) (context: OsSchedCallContext)
         (environment: option TaskStackCallEnvironment) saved_local
         (idle mask: Z) (before: UCOS2_Verify_State) (eid: EventID)
         (observed: OSEventAbstractState) (pe pd ticks: Z) X
    Require pevent == pe && timeout == ticks && perr == pd &&
      &OSTCBCur == sg.g_OSTCBCur &&
      mutex_pend_fact(sem_pend_profile(sg)) && mutex_pend_fact(kernel_tcb_stack_field_layout(sg)) &&
      mutex_pend_fact(mutex_pend_api_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed)) &&
      mutex_pend_fact(mutex_pend_api_admission(environment, idle, context, pe, before, eid)) &&
      mutex_pend_fact(mutex_pend_api_scope(environment, critical, sg, idle, context, pe, before, eid)) &&
      safeExec(LastSeen(before), bind(atomic_cmd(mutex_pend_api_program(environment, critical, sg, context, pe, eid, ticks)),
                                    sem_query_observe_error), X) &&
      sem_pend_continuation_save_input(external, platform, environment, critical, saved_local, sg, context, mask, before) *
      unmap_table_rep(sg) * sem_pend_error_cell(pd) &&
      (pe == 0 || (pe != 0 && mutex_pend_fact(event_object_layout_prop(sg, eid)) &&
        mutex_pend_fact(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)))) &&
      mutex_pend_fact(os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
        &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl))
    Ensure mutex_pend_api_post(external, platform, environment, critical, saved_local, sg, context,
      mask, pe, eid, ticks, pd, before, X)
*/
{
    INT8U      pcp;                                        /* Priority Ceiling Priority (PCP)          */
    INT8U      mprio;                                      /* Mutex owner priority                     */
    BOOLEAN    rdy;                                        /* Flag indicating task was ready           */
    OS_TCB    *ptcb;
    OS_EVENT  *pevent2;
    INT8U      y;
#if OS_CRITICAL_METHOD == 3u                               /* Allocate storage for CPU status register */
    OS_CPU_SR  cpu_sr = 0u;
#endif



/*@ perr == pd && sem_pend_error_cell(pd)
        which implies perr == pd && undef_data_at(perr, unsigned char) */
#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return;
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {                         /* Validate 'pevent'                        */
        *perr = OS_ERR_PEVENT_NULL;
        return;
    }
#endif

    OS_TRACE_MUTEX_PEND_ENTER(pevent, timeout);

    
/*@ mutex_pend_fact(mutex_pend_api_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed)) &&
        pevent == pe && pe != 0 &&
        mutex_pend_fact(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        sem_pend_continuation_save_input(external, platform, environment, critical, saved_local, sg, context, mask, before)
        which implies
        mutex_pend_fact(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        mutex_pend_fact(mutex_pend_api_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed)) &&
        pevent == pe && pe == event_addr(sg, eid) && mutex_pend_fact(valid_event_id(sg, eid)) &&
        mutex_pend_fact(sem_query_public_slot(before, eid, observed)) && mutex_pend_fact(UCOS2_state_inv(sg, before)) &&
        interrupt_platform_running(platform, os_sched_call_invocation(context), os_sched_call_origin(context), mask) *
        os_sched_context_resources(external, context) *
        sem_pend_optional_continuation_resources(external, platform, environment, saved_local, context, before) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(before.EventState, eid)) *
        sem_query_type_frame(sg, before, eid)
    */

/*@ 0 <= event_slot_type_value(before.EventState, eid) && event_slot_type_value(before.EventState, eid) <= 255 by local */
if (pevent->OSEventType != OS_EVENT_TYPE_MUTEX) {      /* Validate event block type                */
        *perr = OS_ERR_EVENT_TYPE;
        OS_TRACE_MUTEX_PEND_EXIT(*perr);
        return;
    }
    
/*@ mutex_pend_fact(UCOS2_state_inv(sg, before)) &&
        mutex_pend_fact(os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
          &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl)) &&
        mutex_pend_fact(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(before.EventState, eid)) *
        sem_query_type_frame(sg, before, eid)
        which implies
        mutex_pend_fact(os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
          &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl)) &&
        mutex_pend_fact(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) && mutex_pend_fact(UCOS2_state_inv(sg, before)) &&
        data_at(&OSIntNesting, unsigned char, before.IntrState.intNesting) *
        data_at(&OSLockNesting, unsigned char, before.IntrState.lockNesting) * sem_pend_interrupt_frame(sg, before)
    */

/*@ 0 <= before.IntrState.intNesting && before.IntrState.intNesting <= 255 by local */
if (OSIntNesting > 0u) {                               /* See if called from ISR ...               */
        *perr = OS_ERR_PEND_ISR;                           /* ... can't PEND from an ISR               */
        OS_TRACE_MUTEX_PEND_EXIT(*perr);
        return;
    }
    
/*@ 0 <= before.IntrState.lockNesting && before.IntrState.lockNesting <= 255 by local */
if (OSLockNesting > 0u) {                              /* See if called with scheduler locked ...  */
        *perr = OS_ERR_PEND_LOCKED;                        /* ... can't PEND when locked               */
        OS_TRACE_MUTEX_PEND_EXIT(*perr);
        return;
    }

    
/*@ mutex_pend_fact(UCOS2_state_inv(sg, before)) &&
        mutex_pend_fact(mutex_pend_api_admission(environment, idle, context, pe, before, eid)) &&
        pe != 0 && event_slot_type_value(before.EventState, eid) == 4 &&
        before.IntrState.intNesting <= 0 && before.IntrState.lockNesting <= 0 &&
        interrupt_platform_running(platform, os_sched_call_invocation(context), os_sched_call_origin(context), mask) *
        os_sched_context_resources(external, context) *
        sem_pend_optional_continuation_resources(external, platform, environment, saved_local, context, before) *
        data_at(&OSIntNesting, unsigned char, before.IntrState.intNesting) *
        data_at(&OSLockNesting, unsigned char, before.IntrState.lockNesting) * sem_pend_interrupt_frame(sg, before) &&
        mutex_pend_fact(os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
          &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl))
        which implies exists (owned: TaskStackCallEnvironment),
        mutex_pend_fact(mutex_pend_api_admission(environment, idle, context, pe, before, eid)) &&
        environment == Some(owned) && external == task_stack_call_external(owned) &&
        platform == task_stack_call_platform(owned) &&
        mutex_pend_fact(mutex_pend_api_prefix(pe, before, eid)) &&
        mutex_pend_fact(UCOS2_state_inv(sg, before)) &&
        mutex_pend_fact(kernel_call_task_source(context, before)) &&
        task_tcb_init_continuation_save_input(owned, critical, saved_local, sg, context, mask, before) &&
        mutex_pend_fact(os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
          &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl))
    */
OS_ENTER_CRITICAL();
    
/*@ exists (owned: TaskStackCallEnvironment),
        mutex_pend_fact(UCOS2_state_inv(sg, before)) &&
        mutex_pend_api_save_output(owned, critical, saved_local, sg, context, mask, cpu_sr, before) &&
        mutex_pend_fact(mutex_pend_api_scope(environment, critical, sg, idle, context, pe, before, eid)) &&
        mutex_pend_fact(mutex_pend_api_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed)) &&
        mutex_pend_fact(mutex_pend_api_admission(environment, idle, context, pe, before, eid)) &&
        mutex_pend_fact(mutex_pend_api_prefix(pe, before, eid)) && environment == Some(owned) &&
        mutex_pend_fact(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        mutex_pend_fact(os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
          &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl)) &&
        &OSTCBCur == sg.g_OSTCBCur
        which implies exists (entered: OsSchedCallContext) (entry: UCOS2_Verify_State)
          (current: OSEventAbstractState) (m: MutexFields) (tid: TaskID) (caller: TaskAbstractState),
        mutex_pend_fact(UCOS2_state_inv(sg, before)) &&
        mutex_pend_fact(mutex_pend_api_scope(environment, critical, sg, idle, context, pe, before, eid)) &&
        mutex_pend_fact(mutex_pend_api_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed)) &&
        mutex_pend_fact(mutex_pend_api_admission(environment, idle, context, pe, before, eid)) &&
        mutex_pend_fact(mutex_pend_api_prefix(pe, before, eid)) &&
        mutex_pend_fact(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        mutex_pend_fact(os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
          &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl)) &&
        mutex_pend_fact(mutex_pend_first_snapshot(owned, critical, sg, idle, context, entered, mask, cpu_sr,
          before, entry, eid, observed, current, m, tid, caller)) &&
        pe == event_addr(sg, eid) &&
        mutex_pend_masked_frame(owned, critical, saved_local, sg, entered, cpu_sr, entry, entry) *
        data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, encode_event_cnt_value(current)) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, encode_event_ptr_value(sg, current)) *
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBPrio, unsigned char, caller.curPrio) *
        mutex_accept_current_frame(sg, entry, eid, current, tid, caller) &&
        &OSTCBCur == sg.g_OSTCBCur
    */
pcp = (INT8U)(pevent->OSEventCnt >> 8u);               /* Get PCP from mutex                       */
                                                           /* Is Mutex available?                      */
    if ((INT8U)(pevent->OSEventCnt & OS_MUTEX_KEEP_LOWER_8) == OS_MUTEX_AVAILABLE) {
        pevent->OSEventCnt &= OS_MUTEX_KEEP_UPPER_8;       /* Yes, Acquire the resource                */
        pevent->OSEventCnt |= (INT16U)OSTCBCur->OSTCBPrio; /*      Save priority of owning task        */
        pevent->OSEventPtr  = (void *)OSTCBCur;            /*      Point to owning task's OS_TCB       */
        if ((pcp != OS_PRIO_MUTEX_CEIL_DIS) &&
            (OSTCBCur->OSTCBPrio <= pcp)) {                /*      PCP 'must' have a SMALLER prio ...  */
             
/*@ exists (pcp_value: Z) (owned: TaskStackCallEnvironment) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MutexFields) (tid: TaskID) (caller: TaskAbstractState),
        pcp == pcp_value &&
        mutex_pend_fact(mutex_pend_first_snapshot(owned, critical, sg, idle, context, entered, mask, cpu_sr,
                  before, entry, eid, observed, current, m, tid, caller)) &&
                ((INT8U)(encode_event_cnt_value(current) & OS_MUTEX_KEEP_LOWER_8)) == OS_MUTEX_AVAILABLE &&
                pcp == (INT8U)(encode_event_cnt_value(current) >> 8u) &&
                pcp != OS_PRIO_MUTEX_CEIL_DIS && caller.curPrio <= pcp &&
                mutex_pend_masked_frame(owned, critical, saved_local, sg, entered, cpu_sr, entry, entry) *
                data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short,
                  (encode_event_cnt_value(current) & OS_MUTEX_KEEP_UPPER_8) | (INT16U)caller.curPrio) *
                data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, task_slot_addr(sg, tid)) *
                data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
                data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBPrio, unsigned char, caller.curPrio) *
                mutex_accept_current_frame(sg, entry, eid, current, tid, caller) &&
        pe == event_addr(sg, eid) &&
        &OSTCBCur == sg.g_OSTCBCur &&
        mutex_pend_fact(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt))
        which implies
        mutex_pend_fact(mutex_pend_first_snapshot(owned, critical, sg, idle, context, entered, mask, cpu_sr,
                  before, entry, eid, observed, current, m, tid, caller)) &&
        pcp == pcp_value &&
                mutex_pend_fact(sem_pend_modular_call_history(owned, critical, sg, context, before, entered, entry)) &&
                mutex_pend_fact(mutex_pend_first_acquired(sg, eid, ticks, entry, 120,
                  mutex_accept_owned_state(entry, eid, current, m, tid, caller.curPrio))) &&
                mutex_pend_api_restore_input(false, owned, critical, saved_local, sg, entered, cpu_sr, entry,
                  mutex_accept_owned_state(entry, eid, current, m, tid, caller.curPrio)) &&
        pe == event_addr(sg, eid) &&
        &OSTCBCur == sg.g_OSTCBCur &&
        mutex_pend_fact(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt))
    */
OS_EXIT_CRITICAL();                           /*      ... than current task!              */
            *perr = OS_ERR_PCP_LOWER;
        } else {
             
/*@ exists (pcp_value: Z) (owned: TaskStackCallEnvironment) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MutexFields) (tid: TaskID) (caller: TaskAbstractState),
        pcp == pcp_value &&
        mutex_pend_fact(mutex_pend_first_snapshot(owned, critical, sg, idle, context, entered, mask, cpu_sr,
                  before, entry, eid, observed, current, m, tid, caller)) &&
                ((INT8U)(encode_event_cnt_value(current) & OS_MUTEX_KEEP_LOWER_8)) == OS_MUTEX_AVAILABLE &&
                pcp == (INT8U)(encode_event_cnt_value(current) >> 8u) &&
                encode_os_err_code(mutex_pend_acquire_error(sg, pcp, caller.curPrio)) == 0 &&
                mutex_pend_masked_frame(owned, critical, saved_local, sg, entered, cpu_sr, entry, entry) *
                data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short,
                  (encode_event_cnt_value(current) & OS_MUTEX_KEEP_UPPER_8) | (INT16U)caller.curPrio) *
                data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, task_slot_addr(sg, tid)) *
                data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
                data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBPrio, unsigned char, caller.curPrio) *
                mutex_accept_current_frame(sg, entry, eid, current, tid, caller) &&
        pe == event_addr(sg, eid) &&
        &OSTCBCur == sg.g_OSTCBCur &&
        mutex_pend_fact(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt))
        which implies
        mutex_pend_fact(mutex_pend_first_snapshot(owned, critical, sg, idle, context, entered, mask, cpu_sr,
                  before, entry, eid, observed, current, m, tid, caller)) &&
        pcp == pcp_value &&
                mutex_pend_fact(sem_pend_modular_call_history(owned, critical, sg, context, before, entered, entry)) &&
                mutex_pend_fact(mutex_pend_first_acquired(sg, eid, ticks, entry, 0,
                  mutex_accept_owned_state(entry, eid, current, m, tid, caller.curPrio))) &&
                mutex_pend_api_restore_input(false, owned, critical, saved_local, sg, entered, cpu_sr, entry,
                  mutex_accept_owned_state(entry, eid, current, m, tid, caller.curPrio)) &&
        pe == event_addr(sg, eid) &&
        &OSTCBCur == sg.g_OSTCBCur &&
        mutex_pend_fact(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt))
    */
OS_EXIT_CRITICAL();
            *perr = OS_ERR_NONE;
        }
        OS_TRACE_MUTEX_PEND_EXIT(*perr);
        return;
    }
    
/*@ exists (owned: TaskStackCallEnvironment) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MutexFields) (tid: TaskID) (caller: TaskAbstractState),
        mutex_pend_fact(mutex_pend_first_snapshot(owned, critical, sg, idle, context, entered, mask, cpu_sr,
          before, entry, eid, observed, current, m, tid, caller)) &&
        mutex_pend_fact(mutex_pend_api_scope(environment, critical, sg, idle, context, pe, before, eid)) &&
        mutex_pend_fact(mutex_pend_api_prefix(pe, before, eid)) && environment == Some(owned) &&
        ((INT8U)(encode_event_cnt_value(current) & OS_MUTEX_KEEP_LOWER_8)) != OS_MUTEX_AVAILABLE &&
        data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, encode_event_cnt_value(current)) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, encode_event_ptr_value(sg, current)) *
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBPrio, unsigned char, caller.curPrio) *
        mutex_accept_current_frame(sg, entry, eid, current, tid, caller) &&
        pe == event_addr(sg, eid) &&
        &OSTCBCur == sg.g_OSTCBCur &&
        mutex_pend_fact(UCOS2_state_inv(sg, before)) &&
        mutex_pend_fact(event_object_layout_prop(sg, eid)) &&
        mutex_pend_fact(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt))
        which implies
        mutex_pend_fact(mutex_pend_api_scope(environment, critical, sg, idle, context, pe, before, eid)) &&
        mutex_pend_fact(mutex_pend_api_prefix(pe, before, eid)) &&
        mutex_pend_fact(mutex_pend_wait_entry(sg, entry, eid, current, tid, caller)) &&
        mutex_pend_fact(mutex_pend_task_entry(idle, entered, entry)) &&
        mutex_pend_fact(sem_pend_blocking_call_stage(sg, entered, entry)) &&
        mutex_pend_fact(mutex_pend_first_snapshot(owned, critical, sg, idle, context, entered, mask, cpu_sr,
          before, entry, eid, observed, current, m, tid, caller)) &&
        UCOS2_inv(sg, entry) &&
        pe == event_addr(sg, eid) &&
        &OSTCBCur == sg.g_OSTCBCur &&
        mutex_pend_fact(UCOS2_state_inv(sg, before)) &&
        mutex_pend_fact(event_object_layout_prop(sg, eid)) &&
        mutex_pend_fact(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt))
    */
if (pcp != OS_PRIO_MUTEX_CEIL_DIS) {
        
/*@ exists (cpu_sr_value: Z) (owned: TaskStackCallEnvironment) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MutexFields) (tid: TaskID) (caller: TaskAbstractState),
        cpu_sr == cpu_sr_value &&
        mutex_pend_fact(mutex_pend_wait_entry(sg, entry, eid, current, tid, caller)) &&
            mutex_pend_fact(mutex_pend_first_snapshot(owned, critical, sg, idle, context, entered, mask, cpu_sr,
              before, entry, eid, observed, current, m, tid, caller)) &&
            UCOS2_inv(sg, entry) &&
        pe == event_addr(sg, eid)
        which implies exists (owner: TaskID) (node: TaskAbstractState),
        mutex_pend_fact(mutex_pend_wait_entry(sg, entry, eid, current, tid, caller)) &&
        mutex_pend_fact(mutex_pend_first_snapshot(owned, critical, sg, idle, context, entered, mask, cpu_sr,
              before, entry, eid, observed, current, m, tid, caller)) &&
        cpu_sr == cpu_sr_value &&
            mutex_pend_fact(mutex_pend_owner_snapshot(sg, entry, eid, current, m, tid, caller, owner, node)) &&
            encode_event_ptr_value(sg, current) == task_slot_addr(sg, owner) &&
            data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, encode_event_cnt_value(current)) *
            data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, task_slot_addr(sg, owner)) *
            mutex_accept_event_frame(sg, entry, eid, current) &&
        pe == event_addr(sg, eid)
    */
ptcb  = (OS_TCB *)(pevent->OSEventPtr);                   /*     Point to TCB of mutex owner   */
        
/*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MutexFields) (tid: TaskID) (caller: TaskAbstractState) (owner: TaskID) (node: TaskAbstractState),
        mutex_pend_fact(mutex_pend_owner_snapshot(sg, entry, eid, current, m, tid, caller, owner, node)) &&
            pcp == unsigned_last_nbits(encode_event_cnt_value(current) >> 8, 8) &&
            pcp != OS_PRIO_MUTEX_CEIL_DIS &&
            ptcb == task_slot_addr(sg, owner) &&
            data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, encode_event_cnt_value(current)) *
            data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, task_slot_addr(sg, owner)) *
            mutex_accept_event_frame(sg, entry, eid, current) &&
        pe == event_addr(sg, eid) &&
        &OSTCBCur == sg.g_OSTCBCur &&
        mutex_pend_fact(os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
          &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl))
        which implies
            mutex_pend_fact(mutex_pend_owner_snapshot(sg, entry, eid, current, m, tid, caller, owner, node)) &&
            pcp == unsigned_last_nbits(encode_event_cnt_value(current) >> 8, 8) &&
            0 <= pcp && pcp < 64 &&
            0 <= node.curPrio && node.curPrio < 64 &&
            mutex_pend_fact(mutex_priority_fallback(task_tcb64_image(sg, node), node.curPrio)) &&
            Zlength(mutex_del_priority_values(sg, entry.TskState.prioTbl)) == 64 &&
            tcb64_storage_rep(ptcb, task_tcb64_image(sg, node)) *
            PtrArray::full(&OSTCBPrioTbl, 64, mutex_del_priority_values(sg, entry.TskState.prioTbl)) *
            UCharArray::full(&OSRdyTbl, 8, sched_row_values(entry.TskState, entry.SchedState.readyList)) *
            data_at(&OSRdyGrp, OS_PRIO, encode_ready_grp(entry.SchedState.readyList, entry.TskState)) *
            data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
            data_at(&OSPrioCur, INT8U, sched_priority_byte(entry.SchedState.curSchedPrio)) *
            data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBPrio, unsigned char, caller.curPrio) *
            mutex_pend_caller_priority_frame(sg, entry, owner, tid, caller) &&
        pe == event_addr(sg, eid) &&
        &OSTCBCur == sg.g_OSTCBCur &&
        mutex_pend_fact(os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
          &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl))
    */
mprio = OSMutex_BasePrio(ptcb);
        
/*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MutexFields) (tid: TaskID) (caller: TaskAbstractState) (owner: TaskID) (node: TaskAbstractState),
        mutex_pend_fact(mutex_pend_owner_snapshot(sg, entry, eid, current, m, tid, caller, owner, node)) &&
            mutex_base_priority_result(mutex_del_priority_values(sg, entry.TskState.prioTbl),
              ptcb, node.curPrio, mprio) && ptcb == task_slot_addr(sg, owner) &&
            tcb64_storage_rep(ptcb, task_tcb64_image(sg, node)) &&
        mutex_pend_fact(kernel_tcb_stack_field_layout(sg))
        which implies
        mutex_pend_fact(mutex_pend_owner_snapshot(sg, entry, eid, current, m, tid, caller, owner, node)) &&
        mutex_pend_fact(mutex_base_priority_result(mutex_del_priority_values(sg, entry.TskState.prioTbl),
              ptcb, node.curPrio, mprio)) &&
            mutex_pend_fact(task_base_priority(sg, entry.TskState.prioTbl, owner, mprio)) &&
            data_at(&ptcb->OSTCBPrio, unsigned char, node.curPrio) *
            tcb64_storage_without(ptcb, TCBPrio, task_tcb64_image(sg, node)) &&
        mutex_pend_fact(kernel_tcb_stack_field_layout(sg))
    */
if (ptcb->OSTCBPrio > pcp) {                              /*     Need to promote prio of owner?*/
            if (mprio > OSTCBCur->OSTCBPrio) {
                
/*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MutexFields) (tid: TaskID) (caller: TaskAbstractState) (owner: TaskID) (node: TaskAbstractState),
        mutex_pend_fact(mutex_pend_owner_snapshot(sg, entry, eid, current, m, tid, caller, owner, node)) &&
                    pcp == (INT8U)(encode_event_cnt_value(current) >> 8u) && pcp != OS_PRIO_MUTEX_CEIL_DIS &&
                    data_at(&ptcb->OSTCBPrio, unsigned char, node.curPrio) *
                    tcb64_storage_without(ptcb, TCBPrio, task_tcb64_image(sg, node))
                    which implies
        mutex_pend_fact(mutex_pend_owner_snapshot(sg, entry, eid, current, m, tid, caller, owner, node)) &&
                    0 <= pcp && pcp < 64 && 0 <= tcb_y_of_prio(node.curPrio) && tcb_y_of_prio(node.curPrio) < 8 &&
                    mutex_pend_owner_fields_rest(ptcb, task_tcb64_image(sg, node)) *
                    data_at(&ptcb->OSTCBEventPtr, OS_EVENT *, 0) *
                    data_at(&ptcb->OSTCBPrio, unsigned char, node.curPrio) *
                    data_at(&ptcb->OSTCBX, unsigned char, tcb_x_of_prio(node.curPrio)) *
                    data_at(&ptcb->OSTCBY, unsigned char, tcb_y_of_prio(node.curPrio)) *
                    data_at(&ptcb->OSTCBBitX, OS_PRIO, tcb_bit_x_of_prio(node.curPrio)) *
                    data_at(&ptcb->OSTCBBitY, OS_PRIO, tcb_bit_y_of_prio(node.curPrio))
                */
y = ptcb->OSTCBY;
                if ((OSRdyTbl[y] & ptcb->OSTCBBitX) != 0u) {      /*     See if mutex owner is ready   */
                    OSRdyTbl[y] &= (OS_PRIO)~ptcb->OSTCBBitX;     /*     Yes, Remove owner from Rdy ...*/
                    if (OSRdyTbl[y] == 0u) {                      /*          ... list at current prio */
                        OSRdyGrp &= (OS_PRIO)~ptcb->OSTCBBitY;
                    }
                    rdy = OS_TRUE;
                } else {
                    pevent2 = ptcb->OSTCBEventPtr;
                    if (pevent2 != (OS_EVENT *)0) {               /* Remove from event wait list       */
                        y = ptcb->OSTCBY;
                        pevent2->OSEventTbl[y] &= (OS_PRIO)~ptcb->OSTCBBitX;
                        if (pevent2->OSEventTbl[y] == 0u) {
                            pevent2->OSEventGrp &= (OS_PRIO)~ptcb->OSTCBBitY;
                        }
                    }
                    rdy = OS_FALSE;                        /* No                                       */
                }
                ptcb->OSTCBPrio = pcp;                     /* Change owner task prio to PCP            */

                OS_TRACE_MUTEX_TASK_PRIO_INHERIT(ptcb, pcp);

#if OS_LOWEST_PRIO <= 63u
                ptcb->OSTCBY    = (INT8U)( ptcb->OSTCBPrio >> 3u);
                ptcb->OSTCBX    = (INT8U)( ptcb->OSTCBPrio & 0x07u);
#else
                ptcb->OSTCBY    = (INT8U)((INT8U)(ptcb->OSTCBPrio >> 4u) & 0xFFu);
                ptcb->OSTCBX    = (INT8U)( ptcb->OSTCBPrio & 0x0Fu);
#endif
                ptcb->OSTCBBitY = (OS_PRIO)(1uL << ptcb->OSTCBY);
                ptcb->OSTCBBitX = (OS_PRIO)(1uL << ptcb->OSTCBX);

                
/*@ 0 <= pcp && pcp < 64
                    which implies 0 <= pcp && pcp < 64 &&
                      0 <= unsigned_last_nbits(pcp >> 3u, 8) &&
                      unsigned_last_nbits(pcp >> 3u, 8) < 8 */
if (rdy == OS_TRUE) {                      /* If task was ready at owner's priority ...*/
                    OSRdyGrp               |= ptcb->OSTCBBitY; /* ... make it ready at new priority.   */
                    OSRdyTbl[ptcb->OSTCBY] |= ptcb->OSTCBBitX;
                } else {
                    pevent2 = ptcb->OSTCBEventPtr;
                    if (pevent2 != (OS_EVENT *)0) {        /* Add to event wait list                   */
                        pevent2->OSEventGrp               |= ptcb->OSTCBBitY;
                        pevent2->OSEventTbl[ptcb->OSTCBY] |= ptcb->OSTCBBitX;
                    }
                }
                OSTCBPrioTbl[pcp] = ptcb;
            
/*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MutexFields) (tid: TaskID) (caller: TaskAbstractState) (owner: TaskID) (node: TaskAbstractState),
        mutex_pend_owner_fields_rest(ptcb, task_tcb64_image(sg, node)) *
                    data_at(&ptcb->OSTCBEventPtr, OS_EVENT *, 0) *
                    data_at(&ptcb->OSTCBPrio, unsigned char, pcp) *
                    data_at(&ptcb->OSTCBX, unsigned char, tcb_x_of_prio(pcp)) *
                    data_at(&ptcb->OSTCBY, unsigned char, tcb_y_of_prio(pcp)) *
                    data_at(&ptcb->OSTCBBitX, OS_PRIO, tcb_bit_x_of_prio(pcp)) *
                    data_at(&ptcb->OSTCBBitY, OS_PRIO, tcb_bit_y_of_prio(pcp)) &&
                    mutex_pend_fact(mutex_pend_owner_snapshot(sg, entry, eid, current, m, tid, caller, owner, node))
                    which implies
        mutex_pend_fact(mutex_pend_owner_snapshot(sg, entry, eid, current, m, tid, caller, owner, node)) && tcb64_storage_rep(ptcb, mutex_priority_image(task_tcb64_image(sg, node), pcp))
                */
}
        } else if ((mprio > OSTCBCur->OSTCBPrio) && (mprio > pcp)) {
            /* Keep this demand even while another held mutex masks it. */
            OSTCBPrioTbl[pcp] = ptcb;
        }
    }
    
/*@ Assert exists (owned: TaskStackCallEnvironment) (entered: OsSchedCallContext)
        (entry inherited: UCOS2_Verify_State) (current: OSEventAbstractState)
        (m: MutexFields) (tid: TaskID) (caller: TaskAbstractState),
        pevent == pe && timeout == ticks && perr == pd && environment == Some(owned) &&
        external == task_stack_call_external(owned) && platform == task_stack_call_platform(owned) &&
        mutex_pend_fact(sem_pend_profile(sg)) && mutex_pend_fact(kernel_tcb_stack_field_layout(sg)) &&
        mutex_pend_fact(mutex_pend_api_input(critical, sg, os_sched_call_invocation(context), pe, before, eid, observed)) &&
        mutex_pend_fact(mutex_pend_api_admission(environment, idle, context, pe, before, eid)) &&
        mutex_pend_fact(mutex_pend_api_scope(environment, critical, sg, idle, context, pe, before, eid)) &&
        mutex_pend_fact(mutex_pend_api_prefix(pe, before, eid)) && mutex_pend_fact(UCOS2_state_inv(sg, before)) &&
        mutex_pend_fact(mutex_pend_first_snapshot(owned, critical, sg, idle, context, entered, mask, cpu_sr,
          before, entry, eid, observed, current, m, tid, caller)) &&
        mutex_pend_fact(mutex_pend_inherited_snapshot(sg, entry, eid, current, m, tid, caller, inherited)) &&
        mutex_pend_fact(kernel_call_task_source(entered, inherited)) &&
        mutex_pend_fact(sched_current_consistency(inherited.TskState, inherited.SchedState)) &&
        mutex_pend_fact(sem_pend_blocking_call_stage(sg, entered, inherited)) &&
        pe == event_addr(sg, eid) && mutex_pend_fact(event_object_layout_prop(sg, eid)) &&
        mutex_pend_fact(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        mutex_pend_fact(os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
          &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl)) &&
        safeExec(LastSeen(before), bind(atomic_cmd(mutex_pend_api_program(environment, critical, sg, context, pe, eid, ticks)),
          sem_query_observe_error), X) &&
        mutex_pend_masked_frame(owned, critical, saved_local, sg, entered, cpu_sr, entry, inherited) *
        UCOS2_inv(sg, inherited) * undef_data_at(pd, unsigned char) *
        undef_data_at(&pcp, unsigned char) * undef_data_at(&mprio, unsigned char) *
        undef_data_at(&rdy, unsigned char) * undef_data_at(&ptcb, OS_TCB *) *
        undef_data_at(&pevent2, OS_EVENT *) * undef_data_at(&y, unsigned char) &&
        &OSTCBCur == sg.g_OSTCBCur
    */

/*@ exists (entry inherited: UCOS2_Verify_State) (current: OSEventAbstractState)
        (m: MutexFields) (tid: TaskID) (caller: TaskAbstractState),
        mutex_pend_fact(mutex_pend_inherited_snapshot(sg, entry, eid, current, m, tid, caller, inherited)) &&
        UCOS2_inv(sg, inherited) &&
        &OSTCBCur == sg.g_OSTCBCur
        which implies
        mutex_pend_fact(mutex_pend_inherited_snapshot(sg, entry, eid, current, m, tid, caller, inherited)) &&
        mutex_pend_fact(mutex_pend_wait_entry(sg, inherited, eid, current, tid, caller)) &&
        0 <= encode_task_status(caller.stat) && encode_task_status(caller.stat) <= 255 &&
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBStat, unsigned char, encode_task_status(caller.stat)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBStatPend, unsigned char, encode_pend_status(caller.statPend)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBDly, unsigned int, caller.dly) *
        sem_pend_prefix_frame(sg, inherited, tid, caller) &&
        &OSTCBCur == sg.g_OSTCBCur
    */
OSTCBCur->OSTCBStat     |= OS_STAT_MUTEX;         /* Mutex not available, pend current task        */
    OSTCBCur->OSTCBStatPend  = OS_STAT_PEND_OK;
    OSTCBCur->OSTCBDly       = timeout;               /* Store timeout in current task's TCB           */
    
/*@ exists (current: OSEventAbstractState) (tid: TaskID) (caller: TaskAbstractState) (inherited: UCOS2_Verify_State),
        mutex_pend_fact(mutex_pend_wait_entry(sg, inherited, eid, current, tid, caller)) &&
        pe == event_addr(sg, eid) && &OSTCBCur == sg.g_OSTCBCur && &OSRdyGrp == sg.g_OSRdyGrp && &OSRdyTbl == sg.g_OSRdyTbl &&
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBStat, unsigned char, encode_task_status(caller.stat) | 16) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBStatPend, unsigned char, 0) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBDly, unsigned int, ticks) *
        sem_pend_prefix_frame(sg, inherited, tid, caller)
        which implies
        mutex_pend_fact(mutex_pend_wait_entry(sg, inherited, eid, current, tid, caller)) &&
        0 <= caller.curPrio / 8 && caller.curPrio / 8 < 8 &&
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBEventPtr, OS_EVENT *, 0) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBY, unsigned char, caller.curPrio / 8) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBBitX, OS_PRIO, tcb_bit_x_of_prio(caller.curPrio)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBBitY, OS_PRIO, tcb_bit_y_of_prio(caller.curPrio)) *
        data_at(pointer_offset(&((OS_EVENT *)pe)->OSEventTbl, caller.curPrio / 8, unsigned char), OS_PRIO,
          encode_event_wait_tbl_at_or(current.waitList, inherited.TskState, caller.curPrio / 8)) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, OS_PRIO, encode_event_wait_grp(current.waitList, inherited.TskState)) *
        data_at(pointer_offset(&OSRdyTbl, caller.curPrio / 8, unsigned char), OS_PRIO,
          encode_ready_tbl_at_or(inherited.SchedState.readyList, inherited.TskState, caller.curPrio / 8)) *
        data_at(&OSRdyGrp, OS_PRIO, encode_ready_grp(inherited.SchedState.readyList, inherited.TskState)) *
        mutex_pend_wait_call_frame(sg, inherited, eid, current, tid, caller, ticks)
    */
OS_EventTaskWait(pevent);                         /* Suspend task until event or timeout occurs    */
    
/*@ exists (pevent_value: Z) (owned: TaskStackCallEnvironment) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MutexFields) (tid: TaskID) (caller: TaskAbstractState) (inherited: UCOS2_Verify_State),
        pevent == pevent_value &&
        mutex_pend_fact(mutex_pend_first_snapshot(owned, critical, sg, idle, context, entered, mask, cpu_sr,
          before, entry, eid, observed, current, m, tid, caller)) &&
        mutex_pend_fact(mutex_pend_inherited_snapshot(sg, entry, eid, current, m, tid, caller, inherited)) &&
        mutex_pend_fact(kernel_call_task_source(entered, inherited)) &&
        mutex_pend_fact(sched_current_consistency(inherited.TskState, inherited.SchedState)) &&
        mutex_pend_fact(sem_pend_blocking_call_stage(sg, entered, inherited)) &&
        mutex_pend_fact(kernel_tcb_stack_field_layout(sg)) &&
        pevent == pe && pe == event_addr(sg, eid) &&
        &OSTCBCur == sg.g_OSTCBCur && &OSRdyGrp == sg.g_OSRdyGrp && &OSRdyTbl == sg.g_OSRdyTbl &&
        mutex_pend_masked_frame(owned, critical, saved_local, sg, entered, cpu_sr, entry, inherited) *
        event_task_wait_post(&OSTCBCur, task_slot_addr(sg, tid), pevent, &OSRdyGrp, &OSRdyTbl,
          caller.curPrio / 8, tcb_bit_x_of_prio(caller.curPrio), tcb_bit_y_of_prio(caller.curPrio),
          encode_event_wait_tbl_at_or(current.waitList, inherited.TskState, caller.curPrio / 8),
          encode_event_wait_grp(current.waitList, inherited.TskState),
          encode_ready_tbl_at_or(inherited.SchedState.readyList, inherited.TskState, caller.curPrio / 8),
          encode_ready_grp(inherited.SchedState.readyList, inherited.TskState)) *
        mutex_pend_wait_call_frame(sg, inherited, eid, current, tid, caller, ticks)
        which implies exists (waiting: UCOS2_Verify_State),
        mutex_pend_fact(mutex_pend_first_snapshot(owned, critical, sg, idle, context, entered, mask, cpu_sr,
          before, entry, eid, observed, current, m, tid, caller)) &&
        mutex_pend_fact(mutex_pend_inherited_snapshot(sg, entry, eid, current, m, tid, caller, inherited)) &&
        mutex_pend_fact(kernel_call_task_source(entered, inherited)) &&
        mutex_pend_fact(sched_current_consistency(inherited.TskState, inherited.SchedState)) &&
        mutex_pend_fact(sem_pend_blocking_call_stage(sg, entered, inherited)) &&
        mutex_pend_fact(kernel_tcb_stack_field_layout(sg)) &&
        pevent == pevent_value &&
        waiting == event_pend_state(sg, inherited, eid, current, tid, caller, PendMutex, ticks) &&
        mutex_pend_fact(sem_pend_modular_call_history(owned, critical, sg, context, before, entered, entry)) &&
        mutex_pend_fact(interrupt_saved_value(mask, cpu_sr)) &&
        mutex_pend_fact(mutex_pend_wait_at(sg, context, entry, current, eid, ticks, waiting, entered, waiting)) &&
        mutex_pend_fact(sem_pend_wait_sched_entry(sg, entered, waiting)) &&
        mutex_pend_fact(UCOS2_state_inv(sg, waiting)) &&
        mutex_pend_api_restore_input(true, owned, critical, saved_local, sg, entered, cpu_sr, entry, waiting)
    */
OS_EXIT_CRITICAL();
    
/*@ exists (cpu_sr_value: Z) (owned: TaskStackCallEnvironment) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (waiting: UCOS2_Verify_State),
        cpu_sr == cpu_sr_value &&
        mutex_pend_fact(interrupt_saved_value(mask, cpu_sr)) &&
        mutex_pend_fact(mutex_pend_wait_at(sg, context, entry, current, eid, ticks, waiting, entered, waiting)) &&
        mutex_pend_fact(sem_pend_wait_sched_entry(sg, entered, waiting)) &&
        mutex_pend_fact(UCOS2_state_inv(sg, waiting)) &&
        mutex_pend_fact(kernel_tcb_stack_field_layout(sg)) &&
        mutex_pend_fact(mutex_pend_api_scope(environment, critical, sg, idle, context, pe, before, eid)) &&
        mutex_pend_fact(mutex_pend_api_prefix(pe, before, eid)) && environment == Some(owned) &&
        external == task_stack_call_external(owned) && platform == task_stack_call_platform(owned) &&
        mutex_pend_api_restore_output(true, owned, critical, saved_local, sg, entered, cpu_sr, waiting)
        which implies exists (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State),
        mutex_pend_fact(interrupt_saved_value(mask, cpu_sr)) &&
        mutex_pend_fact(mutex_pend_wait_at(sg, context, entry, current, eid, ticks, waiting, entered, waiting)) &&
        mutex_pend_fact(sem_pend_wait_sched_entry(sg, entered, waiting)) &&
        mutex_pend_fact(UCOS2_state_inv(sg, waiting)) &&
        mutex_pend_fact(kernel_tcb_stack_field_layout(sg)) &&
        mutex_pend_fact(mutex_pend_api_scope(environment, critical, sg, idle, context, pe, before, eid)) &&
        mutex_pend_fact(mutex_pend_api_prefix(pe, before, eid)) &&
        cpu_sr == cpu_sr_value &&
        mutex_pend_fact(sem_pend_modular_call_history(owned, critical, sg, entered, waiting, released, unmasked)) &&
        mutex_pend_fact(mutex_pend_wait_at(sg, context, entry, current, eid, ticks, waiting, released, unmasked)) &&
        mutex_pend_fact(sem_pend_wait_sched_entry(sg, released, unmasked)) &&
        mutex_pend_continuation_phase_sched_input(
          MutexPendWaitPhase(context, mask, entry, current, eid, ticks, waiting), external, platform,
          environment, critical, saved_local, sg, released, mask, unmasked)
    */
OS_Sched();                                       /* Find next highest priority task ready         */
    
/*@ exists (owned: TaskStackCallEnvironment) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State),
        mutex_pend_fact(sem_pend_modular_call_history(owned, critical, sg, entered, waiting, released, unmasked)) &&
        mutex_pend_continuation_phase_sched_output(
          MutexPendWaitPhase(context, mask, entry, current, eid, ticks, waiting), external, platform,
          environment, critical, saved_local, sg, released, mask, unmasked) &&
        environment == Some(owned) && external == task_stack_call_external(owned) &&
        platform == task_stack_call_platform(owned)
        which implies exists (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State),
        mutex_pend_fact(sem_pend_modular_call_history(owned, critical, sg, entered, waiting, released, unmasked)) &&
        mutex_pend_fact(mutex_pend_sched_return(environment, critical, sg, released, unmasked, scheduled, selected)) &&
        mutex_pend_fact(mutex_pend_wait_selected_at(sg, context, entry, current, eid, ticks, waiting, scheduled, selected)) &&
        task_tcb_init_continuation_save_input(owned, critical, saved_local, sg, scheduled, mask, selected) *
        unmap_table_rep(sg)
    */
OS_ENTER_CRITICAL();
    
/*@ exists (owned: TaskStackCallEnvironment) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (waiting: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State),
        mutex_pend_api_save_output(owned, critical, saved_local, sg, scheduled, mask, cpu_sr, selected) &&
        mutex_pend_fact(mutex_pend_wait_selected_at(sg, context, entry, current, eid, ticks, waiting, scheduled, selected)) &&
        mutex_pend_fact(mutex_pend_api_scope(environment, critical, sg, idle, context, pe, before, eid)) &&
        mutex_pend_fact(mutex_pend_api_prefix(pe, before, eid)) && environment == Some(owned) &&
        &OSTCBCur == sg.g_OSTCBCur
        which implies exists (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State)
          (resume_tid: TaskID) (node: TaskAbstractState),
        mutex_pend_fact(mutex_pend_wait_selected_at(sg, context, entry, current, eid, ticks, waiting, scheduled, selected)) &&
        mutex_pend_fact(mutex_pend_api_scope(environment, critical, sg, idle, context, pe, before, eid)) &&
        mutex_pend_fact(mutex_pend_api_prefix(pe, before, eid)) &&
        mutex_pend_fact(sem_pend_modular_call_history(owned, critical, sg, scheduled, selected, resumed, resume_entry)) &&
        mutex_pend_fact(interrupt_saved_value(mask, cpu_sr)) &&
        mutex_pend_fact(mutex_pend_wait_selected_at(sg, context, entry, current, eid, ticks, waiting, resumed, resume_entry)) &&
        mutex_pend_fact(sem_pend_resume_entry(sg, resume_entry, eid, resume_tid, node)) &&
        mutex_pend_masked_frame(owned, critical, saved_local, sg, resumed, cpu_sr, resume_entry, resume_entry) *
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStat, unsigned char, encode_task_status(node.stat)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStatPend, unsigned char, encode_pend_status(node.statPend)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBEventPtr, OS_EVENT *, encode_event_link(sg, node.eventPtr)) *
        sem_pend_cleanup_frame(sg, resume_entry, resume_tid, node)
    */
switch (OSTCBCur->OSTCBStatPend) {                /* See if we timed-out or aborted                */
        case OS_STAT_PEND_OK:
             *perr = OS_ERR_NONE;
             
/*@ exists (owned: TaskStackCallEnvironment) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (resume_tid: TaskID),
        mutex_pend_fact(sem_pend_resume_entry(sg, resume_entry, eid, resume_tid, node)) &&
                 encode_pend_status(node.statPend) == 0 &&
                 mutex_pend_masked_frame(owned, critical, saved_local, sg, resumed, cpu_sr, resume_entry, resume_entry) *
                 data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStat, unsigned char, encode_task_status(node.stat)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStatPend, unsigned char, encode_pend_status(node.statPend)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBEventPtr, OS_EVENT *, encode_event_link(sg, node.eventPtr)) *
                 sem_pend_cleanup_frame(sg, resume_entry, resume_tid, node)
                 which implies exists (cleaning: UCOS2_Verify_State) (clean_node: TaskAbstractState),
        mutex_pend_fact(sem_pend_resume_entry(sg, resume_entry, eid, resume_tid, node)) &&
                 mutex_pend_fact(mutex_pend_cleanup_observation(sg, resume_entry, eid, 0, cleaning, resume_tid, clean_node)) &&
                 mutex_pend_masked_frame(owned, critical, saved_local, sg, resumed, cpu_sr, resume_entry, cleaning) *
                 data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStat, unsigned char, encode_task_status(clean_node.stat)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStatPend, unsigned char, encode_pend_status(clean_node.statPend)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBEventPtr, OS_EVENT *, encode_event_link(sg, clean_node.eventPtr)) *
                 sem_pend_cleanup_frame(sg, cleaning, resume_tid, clean_node)
             */
break;

        case OS_STAT_PEND_ABORT:
             *perr = OS_ERR_PEND_ABORT;               /* Indicate that we aborted getting mutex        */
             
/*@ exists (owned: TaskStackCallEnvironment) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (resume_tid: TaskID),
        mutex_pend_fact(sem_pend_resume_entry(sg, resume_entry, eid, resume_tid, node)) &&
                 encode_pend_status(node.statPend) == 2 &&
                 mutex_pend_masked_frame(owned, critical, saved_local, sg, resumed, cpu_sr, resume_entry, resume_entry) *
                 data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStat, unsigned char, encode_task_status(node.stat)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStatPend, unsigned char, encode_pend_status(node.statPend)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBEventPtr, OS_EVENT *, encode_event_link(sg, node.eventPtr)) *
                 sem_pend_cleanup_frame(sg, resume_entry, resume_tid, node)
                 which implies exists (cleaning: UCOS2_Verify_State) (clean_node: TaskAbstractState),
        mutex_pend_fact(sem_pend_resume_entry(sg, resume_entry, eid, resume_tid, node)) &&
                 mutex_pend_fact(mutex_pend_cleanup_observation(sg, resume_entry, eid, 14, cleaning, resume_tid, clean_node)) &&
                 mutex_pend_masked_frame(owned, critical, saved_local, sg, resumed, cpu_sr, resume_entry, cleaning) *
                 data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStat, unsigned char, encode_task_status(clean_node.stat)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStatPend, unsigned char, encode_pend_status(clean_node.statPend)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBEventPtr, OS_EVENT *, encode_event_link(sg, clean_node.eventPtr)) *
                 sem_pend_cleanup_frame(sg, cleaning, resume_tid, clean_node)
             */
break;

        case OS_STAT_PEND_TO:
        default:
             
/*@ exists (node: TaskAbstractState) (resume_entry: UCOS2_Verify_State) (resume_tid: TaskID),
        mutex_pend_fact(sem_pend_resume_entry(sg, resume_entry, eid, resume_tid, node)) &&
                 encode_pend_status(node.statPend) != 0 && encode_pend_status(node.statPend) != 2 &&
                 pe == event_addr(sg, eid) && mutex_pend_fact(event_object_layout_prop(sg, eid)) &&
                 data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStat, unsigned char, encode_task_status(node.stat)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStatPend, unsigned char, encode_pend_status(node.statPend)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBEventPtr, OS_EVENT *, encode_event_link(sg, node.eventPtr)) *
                 sem_pend_cleanup_frame(sg, resume_entry, resume_tid, node)
                 which implies exists (linked: OSEventAbstractState),
        mutex_pend_fact(event_object_layout_prop(sg, eid)) &&
                 mutex_pend_fact(sem_pend_resume_entry(sg, resume_entry, eid, resume_tid, node)) &&
                 node.statPend == PendTimeout && mutex_pend_fact(mutex_query_lookup(resume_entry, eid, linked)) &&
                 data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
                 event_task_remove_pre(task_slot_addr(sg, resume_tid),
                   &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0],
                   node.curPrio / 8, tcb_bit_x_of_prio(node.curPrio), tcb_bit_y_of_prio(node.curPrio),
                   encode_event_wait_tbl_at_or(linked.waitList, resume_entry.TskState, node.curPrio / 8),
                   encode_event_wait_grp(linked.waitList, resume_entry.TskState)) *
                 sem_pend_remove_call_frame(sg, resume_entry, eid, linked, resume_tid, node)
             */
OS_EventTaskRemove(OSTCBCur, pevent);
             
/*@ exists (owned: TaskStackCallEnvironment) (node: TaskAbstractState) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (resume_tid: TaskID) (linked: OSEventAbstractState),
        mutex_pend_fact(sem_pend_resume_entry(sg, resume_entry, eid, resume_tid, node)) &&
                 node.statPend == PendTimeout && mutex_pend_fact(mutex_query_lookup(resume_entry, eid, linked)) &&
                 pe == event_addr(sg, eid) && mutex_pend_fact(event_object_layout_prop(sg, eid)) && &OSTCBCur == sg.g_OSTCBCur &&
                 mutex_pend_masked_frame(owned, critical, saved_local, sg, resumed, cpu_sr, resume_entry, resume_entry) *
                 data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
                 event_task_remove_post(task_slot_addr(sg, resume_tid),
                   &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0],
                   node.curPrio / 8, tcb_bit_x_of_prio(node.curPrio), tcb_bit_y_of_prio(node.curPrio),
                   encode_event_wait_tbl_at_or(linked.waitList, resume_entry.TskState, node.curPrio / 8),
                   encode_event_wait_grp(linked.waitList, resume_entry.TskState)) *
                 sem_pend_remove_call_frame(sg, resume_entry, eid, linked, resume_tid, node)
                 which implies exists (cleaning: UCOS2_Verify_State) (clean_node: TaskAbstractState),
        mutex_pend_fact(sem_pend_resume_entry(sg, resume_entry, eid, resume_tid, node)) &&
        mutex_pend_fact(mutex_query_lookup(resume_entry, eid, linked)) &&
        mutex_pend_fact(event_object_layout_prop(sg, eid)) &&
                 mutex_pend_fact(mutex_pend_cleanup_observation(sg, resume_entry, eid, 10, cleaning, resume_tid, clean_node)) &&
                 mutex_pend_masked_frame(owned, critical, saved_local, sg, resumed, cpu_sr, resume_entry, cleaning) *
                 data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStat, unsigned char, encode_task_status(clean_node.stat)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStatPend, unsigned char, encode_pend_status(clean_node.statPend)) *
                 data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBEventPtr, OS_EVENT *, encode_event_link(sg, clean_node.eventPtr)) *
                 sem_pend_cleanup_frame(sg, cleaning, resume_tid, clean_node)
             */
*perr = OS_ERR_TIMEOUT;                  /* Indicate that we didn't get mutex within TO   */
             break;
    }
    OSTCBCur->OSTCBStat          =  OS_STAT_RDY;      /* Set   task  status to ready                   */
    OSTCBCur->OSTCBStatPend      =  OS_STAT_PEND_OK;  /* Clear pend  status                            */
    OSTCBCur->OSTCBEventPtr      = (OS_EVENT  *)0;    /* Clear event pointers                          */
#if (OS_EVENT_MULTI_EN > 0u)
    OSTCBCur->OSTCBEventMultiPtr = (OS_EVENT **)0;
    OSTCBCur->OSTCBEventMultiRdy = (OS_EVENT  *)0;
#endif
    
/*@ exists (perr_value: Z) (owned: TaskStackCallEnvironment) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (resume_tid: TaskID) (cleaning: UCOS2_Verify_State) (clean_node: TaskAbstractState) (code: Z),
        perr == perr_value &&
        mutex_pend_fact(mutex_pend_cleanup_observation(sg, resume_entry, eid, code, cleaning, resume_tid, clean_node)) &&
        perr == pd && &OSTCBCur == sg.g_OSTCBCur &&
        data_at(pd, unsigned char, code) *
        mutex_pend_masked_frame(owned, critical, saved_local, sg, resumed, cpu_sr, resume_entry, cleaning) *
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, resume_tid)) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStat, unsigned char, 0) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBStatPend, unsigned char, 0) *
        data_at(&((OS_TCB *)task_slot_addr(sg, resume_tid))->OSTCBEventPtr, OS_EVENT *, 0) *
        sem_pend_cleanup_frame(sg, cleaning, resume_tid, clean_node)
        which implies exists (cleaned: UCOS2_Verify_State) (code: Z),
        mutex_pend_fact(mutex_pend_cleanup_observation(sg, resume_entry, eid, code, cleaning, resume_tid, clean_node)) &&
        perr == perr_value &&
        mutex_pend_fact(mutex_pend_resume_result(sg, eid, resume_entry, code, cleaned)) &&
        data_at(pd, unsigned char, code) *
        mutex_pend_api_restore_input(false, owned, critical, saved_local, sg, resumed, cpu_sr, resume_entry, cleaned)
    */
OS_EXIT_CRITICAL();

    
/*@ exists (cpu_sr_value: Z) (owned: TaskStackCallEnvironment) (entered: OsSchedCallContext) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (waiting: UCOS2_Verify_State) (released: OsSchedCallContext) (unmasked: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (selected: UCOS2_Verify_State) (resumed: OsSchedCallContext) (resume_entry: UCOS2_Verify_State) (cleaned: UCOS2_Verify_State) (code: Z),
        cpu_sr == cpu_sr_value &&
        mutex_pend_fact(mutex_pend_api_prefix(pe, before, eid)) &&
        mutex_pend_fact(sem_pend_modular_call_history(owned, critical, sg, context, before, entered, entry)) &&
        mutex_pend_fact(mutex_pend_wait_at(sg, context, entry, current, eid, ticks, waiting, entered, waiting)) &&
        mutex_pend_fact(sem_pend_modular_call_history(owned, critical, sg, entered, waiting, released, unmasked)) &&
        mutex_pend_fact(mutex_pend_sched_return(environment, critical, sg, released, unmasked, scheduled, selected)) &&
        mutex_pend_fact(sem_pend_modular_call_history(owned, critical, sg, scheduled, selected, resumed, resume_entry)) &&
        mutex_pend_fact(mutex_pend_resume_result(sg, eid, resume_entry, code, cleaned)) &&
        mutex_pend_fact(interrupt_saved_value(mask, cpu_sr)) &&
        environment == Some(owned) && external == task_stack_call_external(owned) &&
        platform == task_stack_call_platform(owned) &&
        safeExec(LastSeen(before), bind(atomic_cmd(mutex_pend_api_program(environment, critical, sg, context, pe, eid, ticks)),
          sem_query_observe_error), X) &&
        data_at(pd, unsigned char, code) *
        mutex_pend_api_restore_output(false, owned, critical, saved_local, sg, resumed, cpu_sr, cleaned)
        which implies
        mutex_pend_fact(mutex_pend_api_prefix(pe, before, eid)) &&
        mutex_pend_fact(sem_pend_modular_call_history(owned, critical, sg, context, before, entered, entry)) &&
        mutex_pend_fact(mutex_pend_wait_at(sg, context, entry, current, eid, ticks, waiting, entered, waiting)) &&
        mutex_pend_fact(sem_pend_modular_call_history(owned, critical, sg, entered, waiting, released, unmasked)) &&
        mutex_pend_fact(mutex_pend_sched_return(environment, critical, sg, released, unmasked, scheduled, selected)) &&
        mutex_pend_fact(sem_pend_modular_call_history(owned, critical, sg, scheduled, selected, resumed, resume_entry)) &&
        mutex_pend_fact(mutex_pend_resume_result(sg, eid, resume_entry, code, cleaned)) &&
        mutex_pend_fact(interrupt_saved_value(mask, cpu_sr)) &&
        cpu_sr == cpu_sr_value && mutex_pend_api_post(external, platform, environment, critical, saved_local,
          sg, context, mask, pe, eid, ticks, pd, before, X)
    */
OS_TRACE_MUTEX_PEND_EXIT(*perr);
}
