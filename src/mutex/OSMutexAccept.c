/* Single-function annotation carrier; compose before canonical QCP.
 * The environment retains the pinned headers, configuration and callees.
 * Formatting and documented frontend form match the checked C input.
 */

BOOLEAN  OSMutexAccept (OS_EVENT  *pevent,
                        INT8U     *perr)
/*@ With (environment: TaskStackCallEnvironment) (saved_local: Armv7aContinuation -> Assertion)
         (context: OsSchedCallContext) (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
         (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
         (mask: Z) (before: UCOS2_Verify_State) (eid: EventID)
         (observed: OSEventAbstractState) (pe pd: addr) (isr: Z) X
    Require pevent == pe && perr == pd && perr != 0 &&
      coq_prop(mutex_accept_call_binding(environment, platform, context, invocation, origin)) &&
      coq_prop(mutex_accept_call_admission(context, pe, before, eid)) &&
      isr == intNesting(IntrState(before)) && isr >= 0 &&
      coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
      coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) &&
      coq_prop(valid_stable_glob_vars(sg)) &&
      coq_prop(mutex_accept_public_input(critical, sg, invocation, pe, before, eid, observed)) &&
      (pe == 0 || coq_prop(event_core_fields_layout_prop(sg, eid,
        &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt))) &&
      safeExec(LastSeen(before), bind(atomic_cmd(mutex_accept_return_program(critical, sg, invocation, pe)),
                                    mutex_accept_observe_result), X) &&
      mutex_accept_closed(platform, critical, sg, invocation, origin, mask, before) *
      mutex_accept_call_support(environment, saved_local, sg, context, before) *
      undef_data_at(perr, unsigned char)
    Ensure exists (after: UCOS2_Verify_State) (code: Z),
      pevent == pe && perr == pd &&
      coq_prop(mutex_accept_return_post_prop(critical, sg, invocation, pe, before, code, __return, after)) &&
      safeExec(LastSeen(after), return(__return), X) &&
      mutex_accept_closed(platform, critical, sg, invocation, origin, mask, after) *
      mutex_accept_call_support(environment, saved_local, sg, context, after) *
      data_at(pd, unsigned char, code)
*/
{
    INT8U      pcp;                                    /* Priority Ceiling Priority (PCP)              */
#if OS_CRITICAL_METHOD == 3u                           /* Allocate storage for CPU status register     */
    OS_CPU_SR  cpu_sr = 0u;
#endif



#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return (OS_FALSE);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {                     /* Validate 'pevent'                            */
        *perr = OS_ERR_PEVENT_NULL;
        return (OS_FALSE);
    }
#endif
    /*@ pevent == pe && pevent != 0 &&
        coq_prop(mutex_accept_public_input(critical, sg, invocation, pe, before, eid, observed)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        mutex_accept_closed(platform, critical, sg, invocation, origin, mask, before)
        which implies
        pevent == pe && pe == event_addr(sg, eid) &&
        coq_prop(valid_event_id(sg, eid)) && coq_prop(UCOS2_state_inv(sg, before)) &&
        coq_prop(sem_query_public_slot(before, eid, observed)) &&
        coq_prop(mutex_accept_public_input(critical, sg, invocation, pe, before, eid, observed)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        sem_query_type_frame(sg, before, eid)
    */
    /*@ 0 <= event_slot_type_value(EventState(before), eid) && event_slot_type_value(EventState(before), eid) <= 255 by local */
    if (pevent->OSEventType != OS_EVENT_TYPE_MUTEX) {  /* Validate event block type                    */
        /*@ coq_prop(UCOS2_state_inv(sg, before)) &&
            coq_prop(event_core_fields_layout_prop(sg, eid,
              &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
            interrupt_platform_running(platform, invocation, origin, mask) *
            data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
            sem_query_type_frame(sg, before, eid)
            which implies coq_prop(UCOS2_state_inv(sg, before)) &&
              mutex_accept_closed(platform, critical, sg, invocation, origin, mask, before)
        */
        *perr = OS_ERR_EVENT_TYPE;
        return (OS_FALSE);
    }
    /*@ coq_prop(UCOS2_state_inv(sg, before)) && coq_prop(sem_query_public_slot(before, eid, observed)) &&
        event_slot_type_value(EventState(before), eid) == 4 &&
        isr == intNesting(IntrState(before)) && coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        sem_query_type_frame(sg, before, eid)
        which implies
        coq_prop(UCOS2_state_inv(sg, before)) && coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
        coq_prop(mutex_accept_lookup(before, eid, observed)) &&
        encode_event_type(eventType(observed)) == 4 &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        isr == intNesting(IntrState(before)) &&
        data_at(&OSIntNesting, unsigned char, isr) *
        interrupt_inv_no_int_nesting(sg, IntrState(before)) * mutex_accept_interrupt_frame(sg, before)
    */
    /*@ 0 <= isr && isr <= 255 by local */
    if (OSIntNesting > 0u) {                           /* Make sure it's not called from an ISR        */
        /*@ coq_prop(UCOS2_state_inv(sg, before)) &&
            isr == intNesting(IntrState(before)) && coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
            interrupt_platform_running(platform, invocation, origin, mask) *
            data_at(&OSIntNesting, unsigned char, isr) *
            interrupt_inv_no_int_nesting(sg, IntrState(before)) * mutex_accept_interrupt_frame(sg, before)
            which implies coq_prop(UCOS2_state_inv(sg, before)) &&
              mutex_accept_closed(platform, critical, sg, invocation, origin, mask, before)
        */
        *perr = OS_ERR_PEND_ISR;
        return (OS_FALSE);
    }
    /*@ coq_prop(UCOS2_state_inv(sg, before)) &&
        coq_prop(mutex_accept_call_admission(context, pe, before, eid)) &&
        coq_prop(mutex_accept_public_input(critical, sg, invocation, pe, before, eid, observed)) &&
        coq_prop(mutex_accept_lookup(before, eid, observed)) && pe != 0 &&
        encode_event_type(eventType(observed)) == 4 &&
        isr == intNesting(IntrState(before)) && isr <= 0 &&
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
        data_at(&OSIntNesting, unsigned char, isr) *
        interrupt_inv_no_int_nesting(sg, IntrState(before)) * mutex_accept_interrupt_frame(sg, before)
        which implies
        coq_prop(kernel_call_task_source(context, before)) &&
        coq_prop(mutex_accept_handle_protocol(critical, sg, invocation, eid)) &&
        coq_prop(mutex_accept_lookup(before, eid, observed)) &&
        isr == intNesting(IntrState(before)) && isr <= 0 &&
        encode_event_type(eventType(observed)) == 4 && UCOS2_inv(sg, before)
    */
    OS_ENTER_CRITICAL();                               /* Get value (0 or 1) of Mutex                  */
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(mutex_accept_call_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) && pevent == pe && pe == event_addr(sg, eid) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        mutex_accept_call_support(environment, saved_local, sg, context, entry) * UCOS2_inv(sg, entry)
        which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
                             (m: MutexFields) (cnt ptr: Z),
        coq_prop(mutex_accept_call_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) && pevent == pe && pe == event_addr(sg, eid) &&
        coq_prop(mutex_accept_event_snapshot(sg, entry, eid, current, m, cnt, ptr)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        mutex_accept_call_support(environment, saved_local, sg, context, entry) *
        data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, ptr) * mutex_accept_event_frame(sg, entry, eid, current)
    */
    pcp = (INT8U)(pevent->OSEventCnt >> 8u);           /* Get PCP from mutex                           */
    if ((pevent->OSEventCnt & OS_MUTEX_KEEP_LOWER_8) == OS_MUTEX_AVAILABLE) {
        /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MutexFields) (cnt ptr: Z),
            coq_prop(mutex_accept_call_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
              before, entry, observed, current)) &&
            coq_prop(mutex_accept_event_snapshot(sg, entry, eid, current, m, cnt, ptr)) &&
            (cnt & OS_MUTEX_KEEP_LOWER_8) == OS_MUTEX_AVAILABLE &&
            pcp == (INT8U)(cnt >> 8u) &&
            coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        mutex_accept_call_support(environment, saved_local, sg, context, entry) *
            data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) *
            data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, ptr) *
            mutex_accept_event_frame(sg, entry, eid, current)
            which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
                                 (m: MutexFields) (tid: TaskID) (task: TaskAbstractState) (cnt ptr: Z),
            coq_prop(mutex_accept_call_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
              before, entry, observed, current)) &&
            coq_prop(mutex_accept_event_snapshot(sg, entry, eid, current, m, cnt, ptr)) &&
            (cnt & OS_MUTEX_KEEP_LOWER_8) == OS_MUTEX_AVAILABLE &&
            pcp == (INT8U)(cnt >> 8u) &&
            coq_prop(mutex_accept_current_task(sg, entry, tid, task)) &&
            coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        mutex_accept_call_support(environment, saved_local, sg, context, entry) *
            data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) *
            data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, ptr) *
            data_at(&OSTCBCur, struct os_tcb *, task_slot_addr(sg, tid)) *
            data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBPrio, unsigned char, curPrio(task)) *
            mutex_accept_current_frame(sg, entry, eid, current, tid, task)
        */
        pevent->OSEventCnt &= OS_MUTEX_KEEP_UPPER_8;   /*      Mask off LSByte (Acquire Mutex)         */
        pevent->OSEventCnt |= (INT16U)OSTCBCur->OSTCBPrio;  /* Save current task priority in LSByte    */
        pevent->OSEventPtr  = (void *)OSTCBCur;        /*      Link TCB of task owning Mutex           */
        if ((pcp != OS_PRIO_MUTEX_CEIL_DIS) &&
            (OSTCBCur->OSTCBPrio <= pcp)) {            /*      PCP 'must' have a SMALLER prio ...      */
            /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MutexFields)
                       (cnt ptr: Z) (tid: TaskID) (task: TaskAbstractState),
                coq_prop(mutex_accept_call_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
                  before, entry, observed, current)) &&
                coq_prop(mutex_accept_event_snapshot(sg, entry, eid, current, m, cnt, ptr)) &&
                coq_prop(mutex_accept_current_task(sg, entry, tid, task)) &&
                pe == event_addr(sg, eid) && (cnt & OS_MUTEX_KEEP_LOWER_8) == OS_MUTEX_AVAILABLE &&
                pcp == (INT8U)(cnt >> 8u) && pcp != OS_PRIO_MUTEX_CEIL_DIS && curPrio(task) <= pcp &&
                coq_prop(event_core_fields_layout_prop(sg, eid,
                  &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
                coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) &&
                critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        mutex_accept_call_support(environment, saved_local, sg, context, entry) *
                data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, (cnt & OS_MUTEX_KEEP_UPPER_8) | (INT16U)curPrio(task)) *
                data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, task_slot_addr(sg, tid)) *
                data_at(&OSTCBCur, struct os_tcb *, task_slot_addr(sg, tid)) *
                data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBPrio, unsigned char, curPrio(task)) *
                mutex_accept_current_frame(sg, entry, eid, current, tid, task)
                which implies
                pcp == (INT8U)(cnt >> 8u) &&
                coq_prop(mutex_accept_call_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
                  before, entry, observed, current)) &&
                coq_prop(mutex_accept_protected_result(sg, eid, entry, current, 120, 1,
                  mutex_accept_owned_state(entry, eid, current, m, tid, curPrio(task)))) &&
                critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        mutex_accept_call_support(environment, saved_local, sg, context,
                  mutex_accept_owned_state(entry, eid, current, m, tid, curPrio(task))) *
                UCOS2_inv(sg, mutex_accept_owned_state(entry, eid, current, m, tid, curPrio(task)))
            */
             OS_EXIT_CRITICAL();                       /*      ... than current task!                  */
            *perr = OS_ERR_PCP_LOWER;
        } else {
            /*@ mutex_accept_pcp_code(pcp, OSTCBCur->OSTCBPrio) == 0 by local */
            /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MutexFields)
                       (cnt ptr: Z) (tid: TaskID) (task: TaskAbstractState),
                coq_prop(mutex_accept_call_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
                  before, entry, observed, current)) &&
                coq_prop(mutex_accept_event_snapshot(sg, entry, eid, current, m, cnt, ptr)) &&
                coq_prop(mutex_accept_current_task(sg, entry, tid, task)) &&
                pe == event_addr(sg, eid) && (cnt & OS_MUTEX_KEEP_LOWER_8) == OS_MUTEX_AVAILABLE &&
                pcp == (INT8U)(cnt >> 8u) && mutex_accept_pcp_code(pcp, curPrio(task)) == 0 &&
                coq_prop(event_core_fields_layout_prop(sg, eid,
                  &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
                coq_prop(os_tcb_cur_addr(sg, &OSTCBCur)) &&
                critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        mutex_accept_call_support(environment, saved_local, sg, context, entry) *
                data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, (cnt & OS_MUTEX_KEEP_UPPER_8) | (INT16U)curPrio(task)) *
                data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, task_slot_addr(sg, tid)) *
                data_at(&OSTCBCur, struct os_tcb *, task_slot_addr(sg, tid)) *
                data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBPrio, unsigned char, curPrio(task)) *
                mutex_accept_current_frame(sg, entry, eid, current, tid, task)
                which implies
                pcp == (INT8U)(cnt >> 8u) &&
                coq_prop(mutex_accept_call_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
                  before, entry, observed, current)) &&
                coq_prop(mutex_accept_protected_result(sg, eid, entry, current, 0, 1,
                  mutex_accept_owned_state(entry, eid, current, m, tid, curPrio(task)))) &&
                critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        mutex_accept_call_support(environment, saved_local, sg, context,
                  mutex_accept_owned_state(entry, eid, current, m, tid, curPrio(task))) *
                UCOS2_inv(sg, mutex_accept_owned_state(entry, eid, current, m, tid, curPrio(task)))
            */
             OS_EXIT_CRITICAL();
            *perr = OS_ERR_NONE;
        }
        return (OS_TRUE);
    }
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MutexFields) (cnt ptr: Z),
        coq_prop(mutex_accept_call_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) &&
        coq_prop(mutex_accept_event_snapshot(sg, entry, eid, current, m, cnt, ptr)) &&
        pe == event_addr(sg, eid) && (cnt & OS_MUTEX_KEEP_LOWER_8) != OS_MUTEX_AVAILABLE &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        mutex_accept_call_support(environment, saved_local, sg, context, entry) *
        data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, ptr) * mutex_accept_event_frame(sg, entry, eid, current)
        which implies
        coq_prop(mutex_accept_call_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) &&
        coq_prop(mutex_accept_protected_result(sg, eid, entry, current, 0, 0, entry)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        mutex_accept_call_support(environment, saved_local, sg, context, entry) * UCOS2_inv(sg, entry)
    */
    OS_EXIT_CRITICAL();
    *perr = OS_ERR_NONE;
    return (OS_FALSE);
}
