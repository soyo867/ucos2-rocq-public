/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSTaskNameSet (INT8U   prio,
                     INT8U  *pname,
                     INT8U  *perr)
/*@ With (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
         (saved_local : Armv7aContinuation -> Assertion) (platform : InterruptPlatformResources)
         (sg : StableGlobVars) (before : UCOS2_Verify_State) (call : OsSchedCallContext)
         (invocation : nat) (origin : TaskInvocationOrigin) (mask request name error_addr : Z)
         (X : OsSchedCallContext -> Z -> UCOS2_Verify_State -> Prop)
    Require prio == request && pname == name && perr == error_addr &&
      0 <= request && request <= 255 &&
      coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
      coq_prop(UCOS2_state_inv(sg, before)) &&
      coq_prop(task_name_set_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
      coq_prop(task_name_set_layout(sg)) &&
      coq_prop(task_name_set_continuation_admission(sg, call, request, name, before)) &&
      coq_prop(task_name_set_continuation_call_safe(environment, critical, sg, call, mask, request, name, before, X)) &&
      task_name_set_continuation_closed(environment, critical, saved_local, sg, call, mask, before) *
      undef_data_at(perr, unsigned char)
    Ensure exists (returned : OsSchedCallContext) (current : UCOS2_Verify_State) (err : Z),
      coq_prop(task_name_set_continuation_call_post(environment, critical, sg, call, mask, request, name,
        before, returned, err, current, X)) &&
      task_name_set_continuation_closed(environment, critical, saved_local, sg, returned, mask, current) *
      data_at(error_addr, unsigned char, err)
*/
{
    OS_TCB    *ptcb;
#if OS_CRITICAL_METHOD == 3u                         /* Allocate storage for CPU status register       */
    OS_CPU_SR  cpu_sr = 0u;
#endif



#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return;
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (prio > OS_LOWEST_PRIO) {                     /* Task priority valid ?                          */
        if (prio != OS_PRIO_SELF) {
            *perr = OS_ERR_PRIO_INVALID;             /* No                                             */
            return;
        }
    }
    if (pname == (INT8U *)0) {                       /* Is 'pname' a NULL pointer?                     */
        *perr = OS_ERR_PNAME_NULL;                   /* Yes                                            */
        return;
    }
#endif
    /*@ coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
        task_name_set_continuation_closed(environment, critical, saved_local, sg, call, mask, before)
        which implies
        coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        critical_region_outside(critical, sg, invocation, before) *
        task_name_set_continuation_resources(environment, saved_local, sg, call, before)
    */
    /*@ coq_prop(task_name_set_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
        critical_region_outside(critical, sg, invocation, before)
        which implies
        coq_prop(task_name_set_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
        0 <= task_name_set_nesting(before) && task_name_set_nesting(before) <= 255 &&
        data_at(&OSIntNesting, unsigned char, task_name_set_nesting(before)) *
        task_name_set_observation_frame(sg, before)
    */
    if (OSIntNesting > 0u) {                         /* See if trying to call from an ISR              */
        /*@ coq_prop(task_name_set_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
            data_at(&OSIntNesting, unsigned char, task_name_set_nesting(before)) *
            task_name_set_observation_frame(sg, before)
            which implies
            coq_prop(task_name_set_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
            critical_region_outside(critical, sg, invocation, before)
        */
        *perr = OS_ERR_NAME_SET_ISR;
        return;
    }
    /*@ coq_prop(task_name_set_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
        data_at(&OSIntNesting, unsigned char, task_name_set_nesting(before)) *
        task_name_set_observation_frame(sg, before)
        which implies
        coq_prop(task_name_set_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
        critical_region_outside(critical, sg, invocation, before)
    */
    /*@ coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
        coq_prop(UCOS2_state_inv(sg, before)) &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        critical_region_outside(critical, sg, invocation, before) *
        task_name_set_continuation_resources(environment, saved_local, sg, call, before)
        which implies
        coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
        coq_prop(UCOS2_state_inv(sg, before)) &&
        task_name_set_continuation_closed(environment, critical, saved_local, sg, call, mask, before)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (active : OsSchedCallContext) (acquired : UCOS2_Verify_State),
        pname == name && perr == error_addr && prio == request &&
        coq_prop(task_name_set_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
        coq_prop(task_name_set_layout(sg)) &&
        coq_prop(task_name_set_continuation_call_safe(environment, critical, sg, call, mask, request, name, before, X)) &&
        coq_prop(task_name_set_continuation_call_context(environment, critical, sg, call, mask, request, name, cpu_sr, before, active, acquired)) &&
            coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            task_name_set_continuation_resources(environment, saved_local, sg, active, acquired) *
        UCOS2_inv(sg, acquired) * undef_data_at(&ptcb, OS_TCB *) *
        undef_data_at(perr, unsigned char)
    */
    /*@ Given active acquired */
    if (prio == OS_PRIO_SELF) {                      /* See if caller desires to set it's own name     */
        /*@ Assert exists (tid : Z) (task : TaskAbstractState),
            pname == name && perr == error_addr && prio == request && request == 255 &&
            coq_prop(task_name_set_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
            coq_prop(task_name_set_layout(sg)) &&
            coq_prop(task_name_set_continuation_call_safe(environment, critical, sg, call, mask, request, name, before, X)) &&
            coq_prop(task_name_set_continuation_call_context(environment, critical, sg, call, mask, request, name, cpu_sr, before, active, acquired)) &&
            coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
            coq_prop(task_name_set_current(acquired, tid, task)) &&
            0 <= curPrio(task) && curPrio(task) <= 63 &&
            data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
            data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBPrio, unsigned char, curPrio(task)) *
            task_name_set_self_frame(sg, acquired, tid, task) *
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            task_name_set_continuation_resources(environment, saved_local, sg, active, acquired) *
            undef_data_at(&ptcb, OS_TCB *) * undef_data_at(perr, unsigned char)
        */
        /*@ Given tid task */
        prio = OSTCBCur->OSTCBPrio;
        /*@ Assert coq_prop(task_name_set_resolved(request, acquired, prio)) &&
            pname == name && perr == error_addr &&
            coq_prop(task_name_set_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
            coq_prop(task_name_set_layout(sg)) &&
            coq_prop(task_name_set_continuation_call_safe(environment, critical, sg, call, mask, request, name, before, X)) &&
            coq_prop(task_name_set_continuation_call_context(environment, critical, sg, call, mask, request, name, cpu_sr, before, active, acquired)) &&
            coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
            0 <= prio && prio <= 63 &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            task_name_set_continuation_resources(environment, saved_local, sg, active, acquired) *
            UCOS2_inv(sg, acquired) * undef_data_at(&ptcb, OS_TCB *) * undef_data_at(perr, unsigned char)
        */
    }
    /*@ Assert coq_prop(task_name_set_resolved(request, acquired, prio)) &&
        pname == name && perr == error_addr &&
        coq_prop(task_name_set_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
        coq_prop(task_name_set_layout(sg)) &&
        coq_prop(task_name_set_continuation_call_safe(environment, critical, sg, call, mask, request, name, before, X)) &&
        coq_prop(task_name_set_continuation_call_context(environment, critical, sg, call, mask, request, name, cpu_sr, before, active, acquired)) &&
            coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
        0 <= prio && prio <= 63 &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            task_name_set_continuation_resources(environment, saved_local, sg, active, acquired) *
        UCOS2_inv(sg, acquired) * undef_data_at(&ptcb, OS_TCB *) * undef_data_at(perr, unsigned char)
    */
    /*@ UCOS2_inv(sg, acquired) && 0 <= prio && prio <= 63 &&
        coq_prop(task_name_set_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSIntNesting))
        which implies
        0 <= prio && prio <= 63 &&
        coq_prop(task_name_set_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
        data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), OS_TCB *,
          task_name_set_table_entry(sg, acquired, prio)) *
        task_name_set_table_frame(sg, acquired, prio)
    */
    ptcb = OSTCBPrioTbl[prio];
    /*@ Assert coq_prop(task_name_set_resolved(request, acquired, prio)) &&
        pname == name && perr == error_addr &&
        0 <= prio && prio <= 63 &&
        ptcb == task_name_set_table_entry(sg, acquired, prio) &&
        coq_prop(task_name_set_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
        coq_prop(task_name_set_layout(sg)) &&
        coq_prop(task_name_set_continuation_call_safe(environment, critical, sg, call, mask, request, name, before, X)) &&
        coq_prop(task_name_set_continuation_call_context(environment, critical, sg, call, mask, request, name, cpu_sr, before, active, acquired)) &&
            coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            task_name_set_continuation_resources(environment, saved_local, sg, active, acquired) *
        UCOS2_inv(sg, acquired) * undef_data_at(perr, unsigned char)
    */
    if (ptcb == (OS_TCB *)0) {                       /* Does task exist?                               */
        /*@ Assert coq_prop(task_name_set_step(prio, name, acquired, 67, acquired)) &&
            pname == name && perr == error_addr &&
            coq_prop(task_name_set_resolved(request, acquired, prio)) &&
            coq_prop(task_name_set_continuation_call_safe(environment, critical, sg, call, mask, request, name, before, X)) &&
            coq_prop(task_name_set_continuation_call_context(environment, critical, sg, call, mask, request, name, cpu_sr, before, active, acquired)) &&
            coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            task_name_set_continuation_resources(environment, saved_local, sg, active, acquired) *
            UCOS2_inv(sg, acquired) * undef_data_at(&ptcb, OS_TCB *) * undef_data_at(perr, unsigned char)
        */
        /*@ coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
            coq_prop(task_name_set_continuation_call_context(environment, critical, sg, call, mask, request, name, cpu_sr, before, active, acquired)) &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            UCOS2_inv(sg, acquired) *
            task_name_set_continuation_resources(environment, saved_local, sg, active, acquired)
            which implies
            coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
            coq_prop(task_name_set_continuation_call_context(environment, critical, sg, call, mask, request, name, cpu_sr, before, active, acquired)) &&
            task_name_set_continuation_masked(environment, critical, saved_local, sg, active, cpu_sr, acquired, acquired)
        */
        OS_EXIT_CRITICAL();                          /* No                                             */
        *perr = OS_ERR_TASK_NOT_EXIST;
        return;
    }
    /* QCP adapter: exact expansion of OS_TCB_RESERVED, with no side effects. */
    if (ptcb == ((OS_TCB *)1)) {                     /* Task assigned to a Mutex?                      */
        /*@ Assert coq_prop(task_name_set_step(prio, name, acquired, 67, acquired)) &&
            pname == name && perr == error_addr &&
            coq_prop(task_name_set_resolved(request, acquired, prio)) &&
            coq_prop(task_name_set_continuation_call_safe(environment, critical, sg, call, mask, request, name, before, X)) &&
            coq_prop(task_name_set_continuation_call_context(environment, critical, sg, call, mask, request, name, cpu_sr, before, active, acquired)) &&
            coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            task_name_set_continuation_resources(environment, saved_local, sg, active, acquired) *
            UCOS2_inv(sg, acquired) * undef_data_at(&ptcb, OS_TCB *) * undef_data_at(perr, unsigned char)
        */
        /*@ coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
            coq_prop(task_name_set_continuation_call_context(environment, critical, sg, call, mask, request, name, cpu_sr, before, active, acquired)) &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            UCOS2_inv(sg, acquired) *
            task_name_set_continuation_resources(environment, saved_local, sg, active, acquired)
            which implies
            coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
            coq_prop(task_name_set_continuation_call_context(environment, critical, sg, call, mask, request, name, cpu_sr, before, active, acquired)) &&
            task_name_set_continuation_masked(environment, critical, saved_local, sg, active, cpu_sr, acquired, acquired)
        */
        OS_EXIT_CRITICAL();                          /* Yes                                            */
        *perr = OS_ERR_TASK_NOT_EXIST;
        return;
    }
    /*@ Assert exists (tid : Z) (task : TaskAbstractState),
        pname == name && perr == error_addr &&
        coq_prop(task_name_set_resolved(request, acquired, prio)) &&
        coq_prop(task_name_set_layout(sg)) &&
        coq_prop(task_name_set_continuation_call_safe(environment, critical, sg, call, mask, request, name, before, X)) &&
        coq_prop(task_name_set_continuation_call_context(environment, critical, sg, call, mask, request, name, cpu_sr, before, active, acquired)) &&
            coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
        ptcb == task_slot_addr(sg, tid) &&
        coq_prop(task_name_set_target(acquired, prio, tid, task)) &&
        data_at(&ptcb->OSTCBTaskName, INT8U *, tcbTaskName(task)) *
        task_name_set_field_frame(sg, acquired, tid, task) *
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            task_name_set_continuation_resources(environment, saved_local, sg, active, acquired) *
        undef_data_at(perr, unsigned char)
    */
    /*@ Given tid task */
    ptcb->OSTCBTaskName = pname;
    /*@ Assert exists (released : UCOS2_Verify_State),
        pname == name && perr == error_addr &&
        coq_prop(task_name_set_resolved(request, acquired, prio)) &&
        coq_prop(task_name_set_continuation_call_safe(environment, critical, sg, call, mask, request, name, before, X)) &&
        coq_prop(task_name_set_continuation_call_context(environment, critical, sg, call, mask, request, name, cpu_sr, before, active, acquired)) &&
            coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
        coq_prop(task_name_set_step(prio, name, acquired, 0, released)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            task_name_set_continuation_resources(environment, saved_local, sg, active, released) *
        UCOS2_inv(sg, released) * undef_data_at(&ptcb, OS_TCB *) * undef_data_at(perr, unsigned char)
    */
    /*@ Given released */
    OS_TRACE_TASK_NAME_SET(ptcb);
    /*@ coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
            coq_prop(task_name_set_continuation_call_context(environment, critical, sg, call, mask, request, name, cpu_sr, before, active, acquired)) &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            UCOS2_inv(sg, released) *
            task_name_set_continuation_resources(environment, saved_local, sg, active, released)
            which implies
            coq_prop(task_name_set_continuation_call_binding(environment, call, platform, invocation, origin)) &&
            coq_prop(task_name_set_continuation_call_context(environment, critical, sg, call, mask, request, name, cpu_sr, before, active, acquired)) &&
            task_name_set_continuation_masked(environment, critical, saved_local, sg, active, cpu_sr, acquired, released)
        */
        OS_EXIT_CRITICAL();
    *perr               = OS_ERR_NONE;
}
