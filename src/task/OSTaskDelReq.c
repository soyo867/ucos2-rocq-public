/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSTaskDelReq (INT8U prio)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
         (sg : StableGlobVars) (before : UCOS2_Verify_State)
         (invocation : nat) (origin : TaskInvocationOrigin) (mask request : Z)
         (X : Z -> UCOS2_Verify_State -> Prop)
    Require prio == request && 0 <= request && request <= 255 &&
      coq_prop(UCOS2_state_inv(sg, before)) &&
      coq_prop(task_del_req_addresses(sg, OSTCBPrioTbl, &OSTCBCur)) &&
      coq_prop(task_del_req_admission(critical, sg, invocation, request, before)) &&
      coq_prop(task_del_req_safe(critical, sg, invocation, request, before, X)) &&
      task_del_req_closed(platform, critical, sg, invocation, origin, mask, before)
    Ensure exists (current : UCOS2_Verify_State),
      coq_prop(task_del_req_post(critical, sg, invocation, request, before, __return, current, X)) &&
      task_del_req_closed(platform, critical, sg, invocation, origin, mask, current)
*/
{
    INT8U      stat;
    OS_TCB    *ptcb;
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif



#ifdef OS_SAFETY_CRITICAL_IEC61508
    if (OSSafetyCriticalStartFlag == OS_TRUE) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return (OS_ERR_ILLEGAL_DEL_RUN_TIME);
    }
#endif

    if (prio == OS_TASK_IDLE_PRIO) {                            /* Not allowed to delete idle task     */
        return (OS_ERR_TASK_DEL_IDLE);
    }
#if OS_ARG_CHK_EN > 0u
    if (prio >= OS_LOWEST_PRIO) {                               /* Task priority valid ?               */
        if (prio != OS_PRIO_SELF) {
            return (OS_ERR_PRIO_INVALID);
        }
    }
#endif
    if (prio == OS_PRIO_SELF) {                                 /* See if a task is requesting to ...  */
        /*@ task_del_req_closed(platform, critical, sg, invocation, origin, mask, before)
            which implies
            interrupt_platform_running(platform, invocation, origin, mask) *
            critical_region_outside(critical, sg, invocation, before)
        */
        OS_ENTER_CRITICAL();                                    /* ... this task to delete itself      */
        /*@ Assert exists (acquired : UCOS2_Verify_State) (tid : Z) (task : TaskAbstractState),
            prio == request && request == 255 &&
            coq_prop(task_del_req_safe(critical, sg, invocation, request, before, X)) &&
            coq_prop(task_del_req_addresses(sg, OSTCBPrioTbl, &OSTCBCur)) &&
            coq_prop(critical_region_interval(critical, sg, invocation, before, acquired)) &&
            coq_prop(interrupt_saved_value(mask, cpu_sr)) &&
            coq_prop(UCOS2_state_inv(sg, acquired)) && coq_prop(task_del_req_current(acquired, tid, task)) &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, tid)) *
            data_at(&((OS_TCB *)task_slot_addr(sg, tid))->OSTCBDelReq, unsigned char,
              encode_task_delete_request(delReq(task))) * task_del_req_self_frame(sg, acquired, tid, task) *
            undef_data_at(&stat, INT8U) * undef_data_at(&ptcb, OS_TCB *)
        */
        stat = OSTCBCur->OSTCBDelReq;                           /* Return request status to caller     */
        /*@ Assert exists (acquired : UCOS2_Verify_State),
            prio == request && request == 255 &&
            coq_prop(task_del_req_safe(critical, sg, invocation, request, before, X)) &&
            coq_prop(critical_region_interval(critical, sg, invocation, before, acquired)) &&
            coq_prop(interrupt_saved_value(mask, cpu_sr)) &&
            coq_prop(task_del_req_step(request, acquired, stat, acquired)) &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            UCOS2_inv(sg, acquired) * undef_data_at(&ptcb, OS_TCB *)
        */
        OS_EXIT_CRITICAL();
        return (stat);
    }
    /*@ task_del_req_closed(platform, critical, sg, invocation, origin, mask, before)
        which implies
        interrupt_platform_running(platform, invocation, origin, mask) *
        critical_region_outside(critical, sg, invocation, before)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (acquired : UCOS2_Verify_State),
        prio == request && 0 <= request && request < 63 &&
        coq_prop(task_del_req_safe(critical, sg, invocation, request, before, X)) &&
        coq_prop(task_del_req_addresses(sg, OSTCBPrioTbl, &OSTCBCur)) &&
        coq_prop(critical_region_interval(critical, sg, invocation, before, acquired)) &&
        coq_prop(interrupt_saved_value(mask, cpu_sr)) && coq_prop(UCOS2_state_inv(sg, acquired)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
        data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), OS_TCB *, task_del_req_table_entry(sg, acquired, request)) *
        task_del_req_table_frame(sg, acquired, request) * undef_data_at(&ptcb, OS_TCB *) *
        undef_data_at(&stat, INT8U)
    */
    ptcb = OSTCBPrioTbl[prio];
    /*@ Assert exists (acquired : UCOS2_Verify_State),
        prio == request && 0 <= request && request < 63 &&
        coq_prop(task_del_req_safe(critical, sg, invocation, request, before, X)) &&
        ptcb == task_del_req_table_entry(sg, acquired, request) &&
        coq_prop(task_del_req_addresses(sg, OSTCBPrioTbl, &OSTCBCur)) &&
        coq_prop(critical_region_interval(critical, sg, invocation, before, acquired)) &&
        coq_prop(interrupt_saved_value(mask, cpu_sr)) && coq_prop(UCOS2_state_inv(sg, acquired)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
        UCOS2_inv(sg, acquired) * undef_data_at(&stat, INT8U)
    */
    if (ptcb == (OS_TCB *)0) {                                  /* Task to delete must exist           */
        /*@ Assert exists (acquired : UCOS2_Verify_State),
            prio == request && 0 <= request && request < 63 &&
            coq_prop(task_del_req_safe(critical, sg, invocation, request, before, X)) &&
            coq_prop(critical_region_interval(critical, sg, invocation, before, acquired)) &&
            coq_prop(interrupt_saved_value(mask, cpu_sr)) &&
            coq_prop(task_del_req_step(request, acquired, 67, acquired)) &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            UCOS2_inv(sg, acquired) * undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&stat, INT8U)
        */
        OS_EXIT_CRITICAL();
        return (OS_ERR_TASK_NOT_EXIST);                         /* Task must already be deleted        */
    }
    if (ptcb == ((OS_TCB *)1)) {                                /* Must NOT be assigned to a Mutex     */
        /*@ Assert exists (acquired : UCOS2_Verify_State),
            prio == request && 0 <= request && request < 63 &&
            coq_prop(task_del_req_safe(critical, sg, invocation, request, before, X)) &&
            coq_prop(critical_region_interval(critical, sg, invocation, before, acquired)) &&
            coq_prop(interrupt_saved_value(mask, cpu_sr)) &&
            coq_prop(task_del_req_step(request, acquired, 61, acquired)) &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            UCOS2_inv(sg, acquired) * undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&stat, INT8U)
        */
        OS_EXIT_CRITICAL();
        return (OS_ERR_TASK_DEL);
    }
    /*@ Assert exists (acquired : UCOS2_Verify_State) (tid : Z) (task : TaskAbstractState),
        prio == request && 0 <= request && request < 63 && ptcb == task_slot_addr(sg, tid) &&
        coq_prop(task_del_req_safe(critical, sg, invocation, request, before, X)) &&
        coq_prop(critical_region_interval(critical, sg, invocation, before, acquired)) &&
        coq_prop(interrupt_saved_value(mask, cpu_sr)) && coq_prop(UCOS2_state_inv(sg, acquired)) &&
        coq_prop(task_del_req_target(acquired, request, tid, task)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
        data_at(&ptcb->OSTCBDelReq, unsigned char, encode_task_delete_request(delReq(task))) *
        task_del_req_field_frame(sg, acquired, tid, task) * undef_data_at(&stat, INT8U)
    */
    ptcb->OSTCBDelReq = OS_ERR_TASK_DEL_REQ;                    /* Set flag indicating task to be DEL. */
    /*@ Assert exists (acquired released : UCOS2_Verify_State),
        prio == request && 0 <= request && request < 63 &&
        coq_prop(task_del_req_safe(critical, sg, invocation, request, before, X)) &&
        coq_prop(critical_region_interval(critical, sg, invocation, before, acquired)) &&
        coq_prop(interrupt_saved_value(mask, cpu_sr)) &&
        coq_prop(task_del_req_step(request, acquired, 0, released)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
        UCOS2_inv(sg, released) * undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&stat, INT8U)
    */
    OS_EXIT_CRITICAL();
    return (OS_ERR_NONE);
}
