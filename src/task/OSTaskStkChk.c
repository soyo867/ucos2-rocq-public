/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSTaskStkChk (INT8U         prio,
                     OS_STK_DATA  *p_stk_data)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
    (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
    (mask : Z) (before : UCOS2_Verify_State) (caller : Assertion)
    (X : Z -> option TaskStackCheckData -> UCOS2_Verify_State -> Prop)
    Require 0 <= prio && prio <= 255 && UCOS2_state_inv(sg, before) &&
      task_stk_chk_configuration(sg) &&
      task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
      task_stk_chk_admission(critical, sg, invocation, before, caller, prio, p_stk_data) &&
      task_stk_chk_safe(critical, sg, invocation, before, caller, prio, p_stk_data, X) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      critical_region_outside(critical, sg, invocation, before) * caller *
      task_stk_chk_output_pre(sg, prio, p_stk_data)
    Ensure exists after error data,
      task_stk_chk_post(critical, sg, invocation, mask, before, caller,
        prio, p_stk_data, error, data, after, X) && __return == error &&
      UCOS2_state_inv(sg, after) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      critical_region_outside(critical, sg, invocation, after) * caller *
      task_stk_chk_output_post(p_stk_data, data)
*/
{
    OS_TCB    *ptcb;
    OS_STK    *pchk;
    INT32U     nfree;
    INT32U     size;
#if OS_CRITICAL_METHOD == 3u                           /* Allocate storage for CPU status register     */
    OS_CPU_SR  cpu_sr = 0u;
#endif



#if OS_ARG_CHK_EN > 0u
    if (prio > OS_LOWEST_PRIO) {                       /* Make sure task priority is valid             */
        if (prio != OS_PRIO_SELF) {
            return (OS_ERR_PRIO_INVALID);
        }
    }
    if (p_stk_data == (OS_STK_DATA *)0) {              /* Validate 'p_stk_data'                        */
        return (OS_ERR_PDATA_NULL);
    }
#endif
    /*@ task_stk_chk_configuration(sg) && task_stk_chk_valid_arguments(prio, p_stk_data) &&
      task_stk_chk_output_pre(sg, prio, p_stk_data)
      which implies task_stk_chk_configuration(sg) &&
        task_stk_chk_valid_arguments(prio, p_stk_data) &&
        undef_data_at(&(p_stk_data->OSFree), unsigned int) *
        undef_data_at(&(p_stk_data->OSUsed), unsigned int)
    */
    p_stk_data->OSFree = 0u;                           /* Assume failure, set to 0 size                */
    p_stk_data->OSUsed = 0u;
    /*@ data_at(&(p_stk_data->OSFree), unsigned int, 0) *
      data_at(&(p_stk_data->OSUsed), unsigned int, 0)
      which implies task_stack_check_data_rep(p_stk_data, task_stack_check_zero_data)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists entry,
      prio == prio@pre && p_stk_data == p_stk_data@pre &&
      task_stk_chk_configuration(sg) &&
      task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
      task_stk_chk_admission(critical, sg, invocation, before, caller, prio@pre, p_stk_data) &&
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      0 <= prio && prio <= 255 && (prio <= 63 || prio == 255) && p_stk_data != 0 &&
      task_stk_chk_safe(critical, sg, invocation, before, caller, prio@pre, p_stk_data@pre, X) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
      UCOS2_inv(sg, entry) * caller *
      task_stack_check_data_rep(p_stk_data, task_stack_check_zero_data) *
      undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&pchk, OS_STK *) *
      undef_data_at(&nfree, unsigned int) * undef_data_at(&size, unsigned int)
    */
    /*@ Given entry */
    if (prio == OS_PRIO_SELF) {                        /* See if check for SELF                        */
        /*@
          task_stk_chk_admission(critical, sg, invocation, before, caller, prio@pre, p_stk_data) &&
          task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          task_stk_chk_configuration(sg) && prio@pre == 255 && p_stk_data != 0 &&
          task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          UCOS2_inv(sg, entry) * caller *
          task_stack_check_data_rep(p_stk_data, task_stack_check_zero_data)
          which implies exists selected residual,
          task_stk_chk_admission(critical, sg, invocation, before, caller, prio@pre, p_stk_data) &&
          task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          task_stk_chk_configuration(sg) && prio@pre == 255 && p_stk_data != 0 &&
          task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          task_stk_chk_self_view(sg, entry, caller, p_stk_data, selected, residual) &&
          data_at(&OSTCBCur, void *, task_stk_chk_current_pointer(sg, entry)) *
          data_at(field_addr(task_stk_chk_current_pointer(sg, entry), os_tcb, OSTCBPrio),
            unsigned char, selected) * task_stk_chk_residual(residual)
        */
        /*@ Given selected residual */
        prio = OSTCBCur->OSTCBPrio;
        /*@
          task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          task_stk_chk_self_view(sg, entry, caller, p_stk_data, selected, residual) &&
          task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          prio == selected && prio@pre == 255 &&
          data_at(&OSTCBCur, void *, task_stk_chk_current_pointer(sg, entry)) *
          data_at(field_addr(task_stk_chk_current_pointer(sg, entry), os_tcb, OSTCBPrio),
            unsigned char, selected) * task_stk_chk_residual(residual)
          which implies
          task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          task_stk_chk_selected(sg, entry, caller, prio@pre, p_stk_data, prio) &&
          0 <= prio && prio <= 63 && UCOS2_inv(sg, entry) * caller *
          task_stack_check_data_rep(p_stk_data, task_stack_check_zero_data)
        */
    }
    /*@ Assert
      p_stk_data == p_stk_data@pre && task_stk_chk_configuration(sg) &&
      task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
      task_stk_chk_admission(critical, sg, invocation, before, caller, prio@pre, p_stk_data) &&
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_stk_chk_selected(sg, entry, caller, prio@pre, p_stk_data, prio) &&
      0 <= prio && prio <= 63 && p_stk_data != 0 &&
      task_stk_chk_safe(critical, sg, invocation, before, caller, prio@pre, p_stk_data@pre, X) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
      UCOS2_inv(sg, entry) * caller *
      task_stack_check_data_rep(p_stk_data, task_stack_check_zero_data) *
      undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&pchk, OS_STK *) *
      undef_data_at(&nfree, unsigned int) * undef_data_at(&size, unsigned int)
    */
    /*@
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
      0 <= prio && prio <= 63 && UCOS2_inv(sg, entry)
      which implies
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
      0 <= prio && prio <= 63 &&
      data_at(pointer_offset(&OSTCBPrioTbl, prio, void *), void *,
        task_stk_chk_table_pointer(sg, entry, prio)) * task_stk_chk_table_frame(sg, entry, prio)
    */
    ptcb = OSTCBPrioTbl[prio];
    /*@
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
      0 <= prio && prio <= 63 && ptcb == task_stk_chk_table_pointer(sg, entry, prio) &&
      data_at(pointer_offset(&OSTCBPrioTbl, prio, void *), void *,
        task_stk_chk_table_pointer(sg, entry, prio)) * task_stk_chk_table_frame(sg, entry, prio)
      which implies
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      0 <= prio && prio <= 63 && ptcb == task_stk_chk_table_pointer(sg, entry, prio) &&
      UCOS2_inv(sg, entry)
    */
    if (ptcb == (OS_TCB *)0) {                         /* Make sure task exist                         */
        /*@ Assert p_stk_data == p_stk_data@pre &&
          task_stk_chk_error_facts(critical, sg, invocation, mask, before, caller,
            prio@pre, p_stk_data, cpu_sr, entry, prio, 67) &&
          task_stk_chk_safe(critical, sg, invocation, before, caller, prio@pre, p_stk_data@pre, X) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          UCOS2_inv(sg, entry) * caller *
          task_stack_check_data_rep(p_stk_data, task_stack_check_zero_data) *
          undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&pchk, OS_STK *) *
          undef_data_at(&nfree, unsigned int) * undef_data_at(&size, unsigned int)
        */
        OS_EXIT_CRITICAL();
        return (OS_ERR_TASK_NOT_EXIST);
    }
    if (ptcb == ((OS_TCB *)1)) {
        /*@ Assert p_stk_data == p_stk_data@pre &&
          task_stk_chk_error_facts(critical, sg, invocation, mask, before, caller,
            prio@pre, p_stk_data, cpu_sr, entry, prio, 67) &&
          task_stk_chk_safe(critical, sg, invocation, before, caller, prio@pre, p_stk_data@pre, X) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          UCOS2_inv(sg, entry) * caller *
          task_stack_check_data_rep(p_stk_data, task_stack_check_zero_data) *
          undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&pchk, OS_STK *) *
          undef_data_at(&nfree, unsigned int) * undef_data_at(&size, unsigned int)
        */
        OS_EXIT_CRITICAL();
        return (OS_ERR_TASK_NOT_EXIST);
    }
    /*@
      task_stk_chk_configuration(sg) &&
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_stk_chk_selected(sg, entry, caller, prio@pre, p_stk_data, prio) &&
      0 <= prio && prio <= 63 && ptcb == task_stk_chk_table_pointer(sg, entry, prio) &&
      ptcb != 0 && ptcb != 1 && UCOS2_inv(sg, entry)
      which implies exists slot node,
      task_stk_chk_configuration(sg) &&
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_stk_chk_selected(sg, entry, caller, prio@pre, p_stk_data, prio) &&
      0 <= prio && prio <= 63 &&
      task_stk_chk_node(sg, entry, prio, ptcb, slot, node) &&
      data_at(&(ptcb->OSTCBOpt), unsigned short, task_stk_chk_node_option(node)) *
      task_stk_chk_field_frame(sg, entry, slot, node, TCBOpt)
    */
    /*@ Given slot node */
    if ((ptcb->OSTCBOpt & OS_TASK_OPT_STK_CHK) == 0u) { /* Make sure stack checking option is set      */
        /*@
          task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          task_stk_chk_node(sg, entry, prio, ptcb, slot, node) &&
          data_at(&(ptcb->OSTCBOpt), unsigned short, task_stk_chk_node_option(node)) *
          task_stk_chk_field_frame(sg, entry, slot, node, TCBOpt)
          which implies
          task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          task_stk_chk_node(sg, entry, prio, ptcb, slot, node) && UCOS2_inv(sg, entry)
        */
        /*@ Assert p_stk_data == p_stk_data@pre &&
          task_stk_chk_error_facts(critical, sg, invocation, mask, before, caller,
            prio@pre, p_stk_data, cpu_sr, entry, prio, 69) &&
          task_stk_chk_safe(critical, sg, invocation, before, caller, prio@pre, p_stk_data@pre, X) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          UCOS2_inv(sg, entry) * caller *
          task_stack_check_data_rep(p_stk_data, task_stack_check_zero_data) *
          undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&pchk, OS_STK *) *
          undef_data_at(&nfree, unsigned int) * undef_data_at(&size, unsigned int)
        */
        OS_EXIT_CRITICAL();
        return (OS_ERR_TASK_OPT);
    }
    /*@
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_stk_chk_node(sg, entry, prio, ptcb, slot, node) &&
      data_at(&(ptcb->OSTCBOpt), unsigned short, task_stk_chk_node_option(node)) *
      task_stk_chk_field_frame(sg, entry, slot, node, TCBOpt)
      which implies
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_stk_chk_node(sg, entry, prio, ptcb, slot, node) && UCOS2_inv(sg, entry)
    */
    nfree = 0u;
    /*@
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_stk_chk_node(sg, entry, prio, ptcb, slot, node) && UCOS2_inv(sg, entry)
      which implies
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_stk_chk_node(sg, entry, prio, ptcb, slot, node) &&
      data_at(&(ptcb->OSTCBStkSize), unsigned int, task_stk_chk_node_size(node)) *
      task_stk_chk_field_frame(sg, entry, slot, node, TCBStkSize)
    */
    size  = ptcb->OSTCBStkSize;
    /*@ 0 <= size && size <= 4294967295 by local */
    /*@
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_stk_chk_node(sg, entry, prio, ptcb, slot, node) &&
      size == task_stk_chk_node_size(node) && 0 <= size && size <= 4294967295 &&
      data_at(&(ptcb->OSTCBStkSize), unsigned int, task_stk_chk_node_size(node)) *
      task_stk_chk_field_frame(sg, entry, slot, node, TCBStkSize)
      which implies
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_stk_chk_node(sg, entry, prio, ptcb, slot, node) &&
      size == task_stk_chk_node_size(node) && 0 <= size && size <= 4294967295 &&
      UCOS2_inv(sg, entry)
    */
    /*@
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_stk_chk_node(sg, entry, prio, ptcb, slot, node) &&
      size == task_stk_chk_node_size(node) && 0 <= size && size <= 4294967295 &&
      UCOS2_inv(sg, entry)
      which implies
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_stk_chk_node(sg, entry, prio, ptcb, slot, node) &&
      size == task_stk_chk_node_size(node) && 0 <= size && size <= 4294967295 &&
      data_at(&(ptcb->OSTCBStkBottom), void *, task_stk_chk_node_bottom(node)) *
      task_stk_chk_field_frame(sg, entry, slot, node, TCBStkBottom)
    */
    pchk  = ptcb->OSTCBStkBottom;
    /*@
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_stk_chk_node(sg, entry, prio, ptcb, slot, node) &&
      size == task_stk_chk_node_size(node) && 0 <= size && size <= 4294967295 &&
      pchk == task_stk_chk_node_bottom(node) &&
      data_at(&(ptcb->OSTCBStkBottom), void *, task_stk_chk_node_bottom(node)) *
      task_stk_chk_field_frame(sg, entry, slot, node, TCBStkBottom)
      which implies
      task_stk_chk_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_stk_chk_node(sg, entry, prio, ptcb, slot, node) &&
      size == task_stk_chk_node_size(node) && 0 <= size && size <= 4294967295 &&
      pchk == task_stk_chk_node_bottom(node) && UCOS2_inv(sg, entry)
    */
    OS_EXIT_CRITICAL();
    /*@ Assert exists after snapshot region words count stop residual,
      p_stk_data == p_stk_data@pre &&
      task_stk_chk_scan_facts(critical, sg, invocation, mask, before, caller, prio@pre,
        p_stk_data, cpu_sr, entry, after, prio, snapshot,
        region, words, count, stop, residual) &&
      snapshot == task_stk_chk_node_snapshot(slot, node) &&
      task_stk_chk_node(sg, entry, prio, ptcb, slot, node) &&
      size == task_stk_chk_size(snapshot) && pchk == task_stk_chk_bottom(snapshot) &&
      0 <= size && size <= 4294967295 && nfree == 0 &&
      task_stk_chk_safe(critical, sg, invocation, before, caller, prio@pre, p_stk_data@pre, X) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      critical_region_outside(critical, sg, invocation, after) * caller *
      task_stack_check_data_rep(p_stk_data, task_stack_check_zero_data)
    */
    /*@ Given after snapshot region words count stop residual */
    /*@
      task_stk_chk_scan_facts(critical, sg, invocation, mask, before, caller, prio@pre,
        p_stk_data, cpu_sr, entry, after, prio, snapshot, region, words, count, stop, residual) &&
      pchk == task_stk_chk_bottom(snapshot) && size == task_stk_chk_size(snapshot) &&
      nfree == 0 && critical_region_outside(critical, sg, invocation, after) * caller *
      task_stack_check_data_rep(p_stk_data, task_stack_check_zero_data)
      which implies
      task_stk_chk_scan_facts(critical, sg, invocation, mask, before, caller, prio@pre,
        p_stk_data, cpu_sr, entry, after, prio, snapshot, region, words, count, stop, residual) &&
      pchk == task_stk_chk_cursor(snapshot, 0) && size == task_stk_chk_size(snapshot) &&
      nfree == 0 &&
      data_at(task_stk_chk_cursor(snapshot, 0), unsigned int, task_stk_chk_word(count, stop, 0)) *
      task_stk_chk_scan_read_frame(region, words, 0, residual)
    */
#if OS_STK_GROWTH == 1u
    /*@ Assert
      p_stk_data == p_stk_data@pre &&
      task_stk_chk_scan_facts(critical, sg, invocation, mask, before, caller, prio@pre,
        p_stk_data, cpu_sr, entry, after, prio, snapshot, region, words, count, stop, residual) &&
      pchk == task_stk_chk_cursor(snapshot, 0) && nfree == 0 &&
      size == task_stk_chk_size(snapshot) && 0 <= size && size <= 4294967295 &&
      task_stk_chk_safe(critical, sg, invocation, before, caller, prio@pre, p_stk_data@pre, X) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      data_at(task_stk_chk_cursor(snapshot, 0), unsigned int, task_stk_chk_word(count, stop, 0)) *
      task_stk_chk_scan_read_frame(region, words, 0, residual) *
      undef_data_at(&ptcb, OS_TCB *)
    */
    /*@ Inv exists index,
      p_stk_data == p_stk_data@pre &&
      task_stk_chk_scan_facts(critical, sg, invocation, mask, before, caller, prio@pre,
        p_stk_data, cpu_sr, entry, after, prio, snapshot, region, words, count, stop, residual) &&
      0 <= index && index <= task_stk_chk_count(count) &&
      pchk == task_stk_chk_cursor(snapshot, index) && nfree == index &&
      size == task_stk_chk_size(snapshot) && 0 <= size && size <= 4294967295 &&
      task_stk_chk_safe(critical, sg, invocation, before, caller, prio@pre, p_stk_data@pre, X) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      data_at(task_stk_chk_cursor(snapshot, index), unsigned int, task_stk_chk_word(count, stop, index)) *
      task_stk_chk_scan_read_frame(region, words, index, residual)
    */
    while (*pchk == (OS_STK)0) {                      /* Frontend exposure of the original postfix increment */
        pchk++;
        nfree++;
        /*@ Assert exists previous,
          p_stk_data == p_stk_data@pre &&
          task_stk_chk_scan_facts(critical, sg, invocation, mask, before, caller, prio@pre,
            p_stk_data, cpu_sr, entry, after, prio, snapshot, region, words, count, stop, residual) &&
          0 <= previous && previous < task_stk_chk_count(count) &&
          pchk == task_stk_chk_cursor(snapshot, previous) + 4 && nfree == previous + 1 &&
          size == task_stk_chk_size(snapshot) && 0 <= size && size <= 4294967295 &&
          task_stk_chk_safe(critical, sg, invocation, before, caller, prio@pre, p_stk_data@pre, X) &&
          interrupt_platform_running(platform, invocation, origin, mask) *
          data_at(task_stk_chk_cursor(snapshot, previous), unsigned int,
            task_stk_chk_word(count, stop, previous)) *
          task_stk_chk_scan_read_frame(region, words, previous, residual) *
          undef_data_at(&ptcb, OS_TCB *)
        */
        /*@ Given previous */
        /*@
          task_stk_chk_scan_facts(critical, sg, invocation, mask, before, caller, prio@pre,
            p_stk_data, cpu_sr, entry, after, prio, snapshot, region, words, count, stop, residual) &&
          0 <= previous && previous < task_stk_chk_count(count) &&
          pchk == task_stk_chk_cursor(snapshot, previous) + 4 && nfree == previous + 1 &&
          data_at(task_stk_chk_cursor(snapshot, previous), unsigned int,
            task_stk_chk_word(count, stop, previous)) *
          task_stk_chk_scan_read_frame(region, words, previous, residual)
          which implies exists index,
          task_stk_chk_scan_facts(critical, sg, invocation, mask, before, caller, prio@pre,
            p_stk_data, cpu_sr, entry, after, prio, snapshot, region, words, count, stop, residual) &&
          0 <= index && index <= task_stk_chk_count(count) &&
          pchk == task_stk_chk_cursor(snapshot, index) && nfree == index &&
          data_at(task_stk_chk_cursor(snapshot, index), unsigned int, task_stk_chk_word(count, stop, index)) *
          task_stk_chk_scan_read_frame(region, words, index, residual)
        */
    }
    pchk++;
    /*@ Assert
      p_stk_data == p_stk_data@pre &&
      task_stk_chk_scan_facts(critical, sg, invocation, mask, before, caller, prio@pre,
        p_stk_data, cpu_sr, entry, after, prio, snapshot, region, words, count, stop, residual) &&
      nfree == task_stk_chk_count(count) &&
      pchk == task_stk_chk_cursor(snapshot, task_stk_chk_count(count)) + 4 &&
      size == task_stk_chk_size(snapshot) && 0 <= size && size <= 4294967295 &&
      task_stk_chk_safe(critical, sg, invocation, before, caller, prio@pre, p_stk_data@pre, X) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      data_at(task_stk_chk_cursor(snapshot, task_stk_chk_count(count)), unsigned int, stop) *
      task_stk_chk_scan_read_frame(region, words, task_stk_chk_count(count), residual) *
      undef_data_at(&ptcb, OS_TCB *)
    */
    /*@
      task_stk_chk_scan_facts(critical, sg, invocation, mask, before, caller, prio@pre,
        p_stk_data, cpu_sr, entry, after, prio, snapshot, region, words, count, stop, residual) &&
      nfree == task_stk_chk_count(count) &&
      pchk == task_stk_chk_cursor(snapshot, task_stk_chk_count(count)) + 4 &&
      data_at(task_stk_chk_cursor(snapshot, task_stk_chk_count(count)),
        unsigned int, stop) *
      task_stk_chk_scan_read_frame(region, words, task_stk_chk_count(count), residual)
      which implies
      task_stk_chk_scan_facts(critical, sg, invocation, mask, before, caller, prio@pre,
        p_stk_data, cpu_sr, entry, after, prio, snapshot, region, words, count, stop, residual) &&
      nfree == task_stk_chk_count(count) &&
      pchk == task_stk_chk_cursor(snapshot, task_stk_chk_count(count)) + 4 &&
      critical_region_outside(critical, sg, invocation, after) * caller *
      task_stack_check_data_rep(p_stk_data, task_stack_check_zero_data)
    */
#else
    while (*pchk == (OS_STK)0) {
        pchk--;
        nfree++;
    }
    pchk--;
#endif
    /*@ task_stack_check_data_rep(p_stk_data, task_stack_check_zero_data)
      which implies data_at(&(p_stk_data->OSFree), unsigned int, 0) *
        data_at(&(p_stk_data->OSUsed), unsigned int, 0)
    */
    p_stk_data->OSFree = nfree;                       /* Store   number of free entries on the stk     */
    p_stk_data->OSUsed = size - nfree;                /* Compute number of entries used on the stk     */
    return (OS_ERR_NONE);
}
