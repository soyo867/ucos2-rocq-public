/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSTaskQuery (INT8U    prio,
                    OS_TCB  *p_task_data)
/*@ With platform critical sg invocation origin mask before caller
         (old_output : list (option Z)) request output
         (X : Z -> list (option Z) -> UCOS2_Verify_State -> Prop)
    Require prio == request && p_task_data == output &&
            task_query_safe(critical, sg, invocation, before, caller, request, output, old_output, X) &&
            task_query_addresses(sg, &OSTCBCur, OSTCBPrioTbl) &&
            task_query_pre(platform, critical, sg, invocation, origin, mask,
                           before, caller, request, output, old_output)
    Ensure task_query_post(platform, critical, sg, invocation, origin, mask,
                          before, caller, request, output, old_output, __return, X)
 */
{
    OS_TCB    *ptcb;
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif



#if OS_ARG_CHK_EN > 0u
    /*@ 0 <= request && request <= 255 by local */
    if (prio > OS_LOWEST_PRIO) {                 /* Task priority valid ?                              */
        if (prio != OS_PRIO_SELF) {
            return (OS_ERR_PRIO_INVALID);
        }
    }
    if (p_task_data == (OS_TCB *)0) {            /* Validate 'p_task_data'                             */
        return (OS_ERR_PDATA_NULL);
    }
#endif
    /*@ task_query_valid_arguments(request, output) &&
        task_query_pre(platform, critical, sg, invocation, origin, mask,
                       before, caller, request, output, old_output)
        which implies
        task_query_closed(platform, critical, sg, invocation, origin, mask, before) *
        task_query_entry_frame(critical, sg, invocation, before, caller, request,
                               output, old_output)
     */
    OS_ENTER_CRITICAL();
    /*@ task_query_save_post(platform, critical, sg, invocation, origin, mask,
                             before, cpu_sr)
        which implies exists acquired,
        interrupt_saved_value(mask, cpu_sr) &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        task_query_restore_pre(platform, critical, sg, invocation, origin, cpu_sr, acquired)
     */
    /*@ Given acquired */
    if (prio == OS_PRIO_SELF) {                  /* See if suspend SELF                                */
        /*@ request == 255 by local */
        /*@ request == 255 &&
            critical_region_interval(critical, sg, invocation, before, acquired) &&
            task_query_addresses(sg, &OSTCBCur, OSTCBPrioTbl) &&
            task_query_restore_pre(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            task_query_entry_frame(critical, sg, invocation, before, caller, request, output, old_output)
            which implies exists (current : Z) (resolved : Z) (residual : Assertion),
            request == 255 &&
            task_query_current_cut(sg, acquired, caller, current, resolved, residual) &&
            data_at(&OSTCBCur, OS_TCB *, current) *
            data_at(&((OS_TCB *)current)->OSTCBPrio, INT8U, resolved) * residual *
            task_query_current_tail(platform, critical, sg, invocation, origin, cpu_sr,
                                    before, acquired, caller, request, output, old_output)
         */
        /*@ Given current resolved residual */
        prio = OSTCBCur->OSTCBPrio;
        /*@ request == 255 &&
            task_query_current_cut(sg, acquired, caller, current, resolved, residual) &&
            task_query_addresses(sg, &OSTCBCur, OSTCBPrioTbl) &&
            prio == resolved && data_at(&OSTCBCur, OS_TCB *, current) *
            data_at(&((OS_TCB *)current)->OSTCBPrio, INT8U, resolved) * residual *
            task_query_current_tail(platform, critical, sg, invocation, origin, cpu_sr,
                                    before, acquired, caller, request, output, old_output)
            which implies
            request == 255 &&
            task_query_priority_resolution(sg, acquired, caller, request, resolved) &&
            data_at(&prio, INT8U, resolved) *
            task_query_restore_pre(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
            task_query_entry_frame(critical, sg, invocation, before, caller, request, output, old_output)
         */
    }
    /*@ exists (local_priority : Z), data_at(&prio, INT8U, local_priority)
        which implies exists (key : Z), key == local_priority && data_at(&prio, INT8U, key)
     */
    /*@ Given key */
    /*@ task_query_priority_resolution(sg, acquired, caller, request, key) &&
        0 <= key && key <= 63 &&
        task_query_addresses(sg, &OSTCBCur, OSTCBPrioTbl) &&
        task_query_restore_pre(platform, critical, sg, invocation, origin, cpu_sr, acquired)
        which implies
        0 <= key && key <= 63 &&
        task_query_priority_resolution(sg, acquired, caller, request, key) &&
        data_at(pointer_offset(OSTCBPrioTbl, key, sizeof(OS_TCB *), OS_TCB *), OS_TCB *, task_query_table_value(sg, acquired, key)) *
        task_query_table_tail(platform, critical, sg, invocation, origin, cpu_sr, acquired, key)
     */
    ptcb = OSTCBPrioTbl[prio];
    /*@ task_query_addresses(sg, &OSTCBCur, OSTCBPrioTbl) &&
        data_at(&ptcb, OS_TCB *, task_query_table_value(sg, acquired, key)) *
        data_at(pointer_offset(OSTCBPrioTbl, key, sizeof(OS_TCB *), OS_TCB *), OS_TCB *, task_query_table_value(sg, acquired, key)) *
        task_query_table_tail(platform, critical, sg, invocation, origin, cpu_sr, acquired, key)
        which implies
        data_at(&ptcb, OS_TCB *, task_query_table_value(sg, acquired, key)) *
        task_query_restore_pre(platform, critical, sg, invocation, origin, cpu_sr, acquired)
     */
    if (ptcb == (OS_TCB *)0) {                   /* Task to query must exist                           */
        /*@ UCOS2_state_inv(sg, acquired) by local */
        OS_EXIT_CRITICAL();
        return (OS_ERR_PRIO);
    }
    if (ptcb == ((OS_TCB *)1)) {               /* Task to query must not be assigned to a Mutex      */
        /*@ UCOS2_state_inv(sg, acquired) by local */
        /*@ task_query_reserved_entry(acquired, key) by local */
        OS_EXIT_CRITICAL();
        return (OS_ERR_TASK_NOT_EXIST);
    }
                                                 /* Copy TCB into user storage area                    */
    /*@ task_query_priority_resolution(sg, acquired, caller, request, key) &&
        0 <= key && key <= 63 &&
        task_query_table_value(sg, acquired, key) != 0 &&
        task_query_table_value(sg, acquired, key) != 1 &&
        task_query_restore_pre(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
        task_query_entry_frame(critical, sg, invocation, before, caller, request, output, old_output) *
        data_at(&ptcb, OS_TCB *, task_query_table_value(sg, acquired, key))
        which implies exists (tid : Z) (t : TaskAbstractState) (bytes : list Z),
        0 <= key && key <= 63 &&
        task_query_task_entry(acquired, key, tid) &&
        task_query_table_value(sg, acquired, key) == task_slot_addr(sg, tid) &&
        task_query_source_byte_view(sg, acquired, tid, t, bytes) &&
        Zlength(bytes) == 64 && sizeof(struct os_tcb) == 64 &&
        0 <= task_slot_addr(sg, tid) &&
        task_slot_addr(sg, tid) + 64 <= 4294967295 &&
        pointer_offset(task_slot_addr(sg, tid), sizeof(struct os_tcb), sizeof(unsigned char), unsigned char) <= 4294967295 &&
        0 <= output && output + 64 <= 4294967295 &&
        pointer_offset(output, sizeof(struct os_tcb), sizeof(unsigned char), unsigned char) <= 4294967295 &&
        data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
        mem_copy_pre(output, task_slot_addr(sg, tid), sizeof(struct os_tcb), bytes) *
        task_query_copy_frame(platform, critical, sg, invocation, origin, cpu_sr, acquired, caller, tid)
     */
    /*@ Given tid t bytes */
    OS_MemCopy((INT8U *)p_task_data, (INT8U *)ptcb, sizeof(OS_TCB)) /*@ where bytes = bytes */;
    /*@ task_query_priority_resolution(sg, acquired, caller, request, key) &&
        task_query_task_entry(acquired, key, tid) &&
        task_query_source_byte_view(sg, acquired, tid, t, bytes) &&
        p_task_data@pre == output && sizeof(struct os_tcb) == 64 &&
        mem_copy_post(p_task_data@pre, task_slot_addr(sg, tid), sizeof(struct os_tcb), bytes) *
        task_query_copy_frame(platform, critical, sg, invocation, origin, cpu_sr, acquired, caller, tid)
        which implies
        task_query_restore_pre(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
        task_query_success_frame(sg, acquired, caller, request, output, bytes)
     */
    /*@ UCOS2_state_inv(sg, acquired) by local */
    OS_EXIT_CRITICAL();
    return (OS_ERR_NONE);
}
