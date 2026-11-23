/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSTaskNameGet (INT8U    prio,
                      INT8U  **pname,
                      INT8U   *perr)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
    (sg : StableGlobVars) (before : UCOS2_Verify_State)
    (invocation : nat) (origin : TaskInvocationOrigin) (mask request : Z) (old : option Z)
    (X : TaskNameGetObservation -> UCOS2_Verify_State -> Prop)
    Require prio == request && task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
      task_name_get_pre(platform, critical, sg, invocation, origin, mask, before, request, pname, perr, old) &&
      task_name_get_safe(critical, sg, invocation, request, pname, before, X)
    Ensure task_name_get_post(platform, critical, sg, invocation, origin, mask, before, request, pname, perr, old, __return, X)
*/
{
    OS_TCB    *ptcb;
    INT8U      len;
#if OS_CRITICAL_METHOD == 3u                             /* Allocate storage for CPU status register   */
    OS_CPU_SR  cpu_sr = 0u;
#endif

    /*@ task_name_get_pre(platform, critical, sg, invocation, origin, mask, before, request, pname, perr, old)
      which implies
      UCOS2_state_inv(sg, before) && 0 <= request && request < 256 &&
      task_name_get_access(critical, sg, invocation, before, request, pname, old) &&
      task_name_get_closed(platform, critical, sg, invocation, origin, mask, before) *
      undef_data_at(perr, unsigned char) * task_name_get_output_cell(pname, old) *
      task_name_get_guarded_private(sg, invocation, request, pname, before)
    */
#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return (0u);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (prio > OS_LOWEST_PRIO) {                         /* Task priority valid ?                      */
        if (prio != OS_PRIO_SELF) {
            *perr = OS_ERR_PRIO_INVALID;                 /* No                                         */
            return (0u);
        }
    }
    if (pname == (INT8U **)0) {                          /* Is 'pname' a NULL pointer?                 */
        *perr = OS_ERR_PNAME_NULL;                       /* Yes                                        */
        return (0u);
    }
#endif
    /*@ task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
      task_name_get_closed(platform, critical, sg, invocation, origin, mask, before)
      which implies
      task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      data_at(&OSIntNesting, unsigned char, task_name_get_nesting(before)) *
      task_name_get_nesting_frame(sg, before)
    */
    if (OSIntNesting > 0u) {                              /* See if trying to call from an ISR          */
        /*@ task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
          interrupt_platform_running(platform, invocation, origin, mask) *
          data_at(&OSIntNesting, unsigned char, task_name_get_nesting(before)) *
          task_name_get_nesting_frame(sg, before)
          which implies
          task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
          task_name_get_closed(platform, critical, sg, invocation, origin, mask, before)
        */
        *perr = OS_ERR_NAME_GET_ISR;
        return (0u);
    }
    /*@ task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      data_at(&OSIntNesting, unsigned char, task_name_get_nesting(before)) *
      task_name_get_nesting_frame(sg, before)
      which implies
      task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
      0 <= task_name_get_nesting(before) && task_name_get_nesting(before) < 256 &&
      task_name_get_closed(platform, critical, sg, invocation, origin, mask, before)
    */
    /*@ task_name_get_closed(platform, critical, sg, invocation, origin, mask, before)
      which implies
      interrupt_platform_running(platform, invocation, origin, mask) *
      critical_region_outside(critical, sg, invocation, before)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists acquired,
      prio == request && pname == pname@pre && perr == perr@pre &&
      UCOS2_state_inv(sg, before) && UCOS2_state_inv(sg, acquired) &&
      task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
      task_name_get_early_error(request, pname, task_name_get_nesting(before)) == None &&
      task_name_get_access(critical, sg, invocation, before, request, pname, old) &&
      critical_region_interval(critical, sg, invocation, before, acquired) &&
      interrupt_saved_value(mask, cpu_sr) &&
      task_name_get_safe(critical, sg, invocation, request, pname, before, X) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
      UCOS2_inv(sg, acquired) * task_name_get_private(sg, invocation, request, acquired) *
      task_name_get_output_cell(pname, old) * undef_data_at(perr, unsigned char) *
      undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&len, unsigned char)
    */
    /*@ Given acquired */
    if (prio == OS_PRIO_SELF) {                          /* See if caller desires it's own name        */
        /*@ UCOS2_state_inv(sg, acquired) &&
          critical_region_interval(critical, sg, invocation, before, acquired) &&
          task_name_get_access(critical, sg, invocation, before, request, pname, old) &&
          task_name_get_early_error(request, pname, task_name_get_nesting(before)) == None && request == 255 &&
          task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
          UCOS2_inv(sg, acquired) * task_name_get_private(sg, invocation, request, acquired)
          which implies exists view priority,
          UCOS2_state_inv(sg, acquired) &&
          critical_region_interval(critical, sg, invocation, before, acquired) &&
          task_name_get_access(critical, sg, invocation, before, request, pname, old) &&
          task_name_get_early_error(request, pname, task_name_get_nesting(before)) == None && request == 255 &&
          task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
          task_name_get_current_view(sg, invocation, acquired, view, priority) &&
          data_at(&OSTCBCur, OS_TCB *, task_name_get_current_pointer(sg, view)) *
          data_at(&(((OS_TCB *)task_name_get_current_pointer(sg, view))->OSTCBPrio), unsigned char, priority) *
          task_name_get_current_residual(sg, invocation, acquired, view)
        */
        /*@ Given view priority */
        prio = OSTCBCur->OSTCBPrio;
        /*@ UCOS2_state_inv(sg, acquired) && request == 255 &&
          task_name_get_current_view(sg, invocation, acquired, view, prio) &&
          task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
          data_at(&OSTCBCur, OS_TCB *, task_name_get_current_pointer(sg, view)) *
          data_at(&(((OS_TCB *)task_name_get_current_pointer(sg, view))->OSTCBPrio), unsigned char, prio) *
          task_name_get_current_residual(sg, invocation, acquired, view)
          which implies
          UCOS2_state_inv(sg, acquired) &&
          task_name_get_resolved(sg, invocation, acquired, request, prio) &&
          task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
          UCOS2_inv(sg, acquired) * task_name_get_private(sg, invocation, request, acquired)
        */
    }
    /*@ Assert
      pname == pname@pre && perr == perr@pre &&
      UCOS2_state_inv(sg, before) && UCOS2_state_inv(sg, acquired) &&
      task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
      task_name_get_early_error(request, pname, task_name_get_nesting(before)) == None &&
      task_name_get_access(critical, sg, invocation, before, request, pname, old) &&
      critical_region_interval(critical, sg, invocation, before, acquired) &&
      interrupt_saved_value(mask, cpu_sr) && task_name_get_resolved(sg, invocation, acquired, request, prio) &&
      task_name_get_safe(critical, sg, invocation, request, pname, before, X) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
      UCOS2_inv(sg, acquired) * task_name_get_private(sg, invocation, request, acquired) *
      task_name_get_output_cell(pname, old) * undef_data_at(perr, unsigned char) *
      undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&len, unsigned char)
    */
    /*@ task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
      task_name_get_resolved(sg, invocation, acquired, request, prio) && UCOS2_inv(sg, acquired)
      which implies
      task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
      task_name_get_resolved(sg, invocation, acquired, request, prio) && UCOS2_state_inv(sg, acquired) &&
      data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), OS_TCB *, task_name_get_table_value(sg, acquired, prio)) *
      task_name_get_table_residual(sg, acquired, prio)
    */
    ptcb = OSTCBPrioTbl[prio];
    /*@ task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
      task_name_get_resolved(sg, invocation, acquired, request, prio) &&
      ptcb == task_name_get_table_value(sg, acquired, prio) && UCOS2_state_inv(sg, acquired) &&
      data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), OS_TCB *, task_name_get_table_value(sg, acquired, prio)) *
      task_name_get_table_residual(sg, acquired, prio)
      which implies
      task_name_get_addresses(sg, &OSIntNesting, &OSTCBCur, OSTCBPrioTbl) &&
      task_name_get_lookup(sg, invocation, acquired, request, prio, ptcb) &&
      UCOS2_state_inv(sg, acquired) && UCOS2_inv(sg, acquired)
    */
    /*@ UCOS2_state_inv(sg, before) &&
      critical_region_interval(critical, sg, invocation, before, acquired) &&
      task_name_get_private(sg, invocation, request, acquired)
      which implies
      UCOS2_state_inv(sg, before) &&
      critical_region_interval(critical, sg, invocation, before, acquired) &&
      task_name_get_private(sg, invocation, request, before)
    */
    if (ptcb == (OS_TCB *)0) {                           /* Does task exist?                           */
        OS_EXIT_CRITICAL();                              /* No                                         */
        *perr = OS_ERR_TASK_NOT_EXIST;
        return (0u);
    }
    if (ptcb == ((OS_TCB *)1)) {                         /* Exact OS_TCB_RESERVED expansion for QCP.    */
        OS_EXIT_CRITICAL();                              /* Yes                                        */
        *perr = OS_ERR_TASK_NOT_EXIST;
        return (0u);
    }
    /*@ UCOS2_state_inv(sg, acquired) &&
      task_name_get_lookup(sg, invocation, acquired, request, prio, ptcb) && ptcb != 0 && ptcb != 1 &&
      task_name_get_access(critical, sg, invocation, before, request, pname, old) &&
      task_name_get_early_error(request, pname, task_name_get_nesting(before)) == None &&
      critical_region_interval(critical, sg, invocation, before, acquired) &&
      UCOS2_inv(sg, acquired) * task_name_get_output_cell(pname, old)
      which implies exists tid node chars previous,
      UCOS2_state_inv(sg, acquired) &&
      task_name_get_lookup(sg, invocation, acquired, request, prio, ptcb) &&
      task_name_get_target(acquired, prio, tid, node) && ptcb != 0 && ptcb != 1 &&
      task_name_get_success(sg, invocation, acquired, request, prio, ptcb, task_name_get_name(node), chars) &&
      old == Some(previous) &&
      data_at(&(ptcb->OSTCBTaskName), INT8U *, task_name_get_name(node)) *
      task_name_get_name_field_residual(sg, acquired, tid, node) *
      data_at(pname, INT8U *, previous)
    */
    /*@ Given tid node chars previous */
    *pname = ptcb->OSTCBTaskName;
    /*@ UCOS2_state_inv(sg, acquired) && task_name_get_target(acquired, prio, tid, node) &&
      task_name_get_success(sg, invocation, acquired, request, prio, ptcb, task_name_get_name(node), chars) &&
      data_at(&(ptcb->OSTCBTaskName), INT8U *, task_name_get_name(node)) *
      task_name_get_name_field_residual(sg, acquired, tid, node)
      which implies
      UCOS2_state_inv(sg, acquired) &&
      task_name_get_success(sg, invocation, acquired, request, prio, ptcb, task_name_get_name(node), chars) &&
      UCOS2_inv(sg, acquired)
    */
    /*@ UCOS2_state_inv(sg, acquired) &&
      task_name_get_success(sg, invocation, acquired, request, prio, ptcb, task_name_get_name(node), chars) &&
      UCOS2_inv(sg, acquired)
      which implies
      UCOS2_state_inv(sg, acquired) &&
      task_name_get_success(sg, invocation, acquired, request, prio, ptcb, task_name_get_name(node), chars) &&
      task_name_get_readable(task_name_get_names(acquired), task_name_get_name(node), chars) &&
      task_name_get_name_bytes(task_name_get_name(node), chars) *
      task_name_get_name_frame(sg, acquired, task_name_get_name(node), chars)
    */
    /*@ task_name_get_name_frame(sg, acquired, task_name_get_name(node), chars) *
      task_name_get_private(sg, invocation, request, before) *
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
      undef_data_at(perr, unsigned char)
      which implies
      task_name_get_call_frame(platform, critical, sg, invocation, origin, cpu_sr,
        before, acquired, request, perr, task_name_get_name(node), chars)
    */
    len    = OS_StrLen(*pname) /*@ where (task_name_get_spec) entry=task_name_get_name(node),
      names=task_name_get_names(acquired), chars=chars,
      frame=task_name_get_call_frame(platform, critical, sg, invocation, origin, cpu_sr,
        before, acquired, request, perr, task_name_get_name(node), chars) */;
    /*@ task_name_get_call_frame(platform, critical, sg, invocation, origin, cpu_sr,
        before, acquired, request, perr, task_name_get_name(node), chars)
      which implies
      task_name_get_name_frame(sg, acquired, task_name_get_name(node), chars) *
      task_name_get_private(sg, invocation, request, before) *
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
      undef_data_at(perr, unsigned char)
    */
    /*@ UCOS2_state_inv(sg, acquired) &&
      task_name_get_success(sg, invocation, acquired, request, prio, ptcb, task_name_get_name(node), chars) &&
      task_name_get_name_bytes(task_name_get_name(node), chars) *
      task_name_get_name_frame(sg, acquired, task_name_get_name(node), chars)
      which implies UCOS2_state_inv(sg, acquired) &&
      task_name_get_success(sg, invocation, acquired, request, prio, ptcb, task_name_get_name(node), chars) &&
      UCOS2_inv(sg, acquired)
    */
    OS_EXIT_CRITICAL();
    *perr  = OS_ERR_NONE;
    return (len);
}
