/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT32U  OSTaskRegGet (INT8U   prio,
                      INT8U   id,
                      INT8U  *perr)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
    (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
    (mask : Z) (before : UCOS2_Verify_State) (caller : Assertion)
    (X : Z -> Z -> UCOS2_Verify_State -> Prop)
    Require 0 <= prio && prio <= 255 && 0 <= id && id <= 255 &&
      UCOS2_state_inv(sg, before) &&
      task_reg_get_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
      task_reg_get_admission(critical, sg, invocation, before, caller, prio, id) &&
      task_reg_get_safe(critical, sg, invocation, before, caller, prio, id, X) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      critical_region_outside(critical, sg, invocation, before) * caller *
      undef_data_at(perr, unsigned char)
    Ensure exists after error,
      task_reg_get_post(critical, sg, invocation, mask, before, caller,
        prio, id, error, __return, after, X) && UCOS2_state_inv(sg, after) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      critical_region_outside(critical, sg, invocation, after) * caller *
      data_at(perr, unsigned char, error)
*/
{
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif
    INT32U     value;
    OS_TCB    *ptcb;



#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return (0u);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (prio >= OS_LOWEST_PRIO) {
        if (prio != OS_PRIO_SELF) {
            *perr = OS_ERR_PRIO_INVALID;
            return (0u);
        }
    }
    if (id >= OS_TASK_REG_TBL_SIZE) {
        *perr = OS_ERR_ID_INVALID;
        return (0u);
    }
#endif
    OS_ENTER_CRITICAL();
    /*@ Assert exists entry,
      prio == prio@pre && id == id@pre && perr == perr@pre &&
      task_reg_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_reg_get_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
      task_reg_get_admission(critical, sg, invocation, before, caller, prio, id) &&
      0 <= prio && prio <= 255 && (prio < 63 || prio == 255) && id == 0 &&
      task_reg_get_scalar_valid(prio, id) &&
      task_reg_get_safe(critical, sg, invocation, before, caller, prio, id, X) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
      UCOS2_inv(sg, entry) * caller * undef_data_at(perr, unsigned char) *
      undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&value, unsigned int)
    */
    if (prio == OS_PRIO_SELF) {                  /* See if need to get register from current task      */
        /*@ exists entry,
          task_reg_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          task_reg_get_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          prio == 255 &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          UCOS2_inv(sg, entry)
          which implies exists entry,
          task_reg_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          task_reg_get_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          prio == 255 &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          data_at(&OSTCBCur, void *, task_reg_get_current_pointer(sg, entry)) *
          task_reg_get_current_frame(sg, entry)
        */
        ptcb = OSTCBCur;
        /*@ exists entry,
          task_reg_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          task_reg_get_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          prio == 255 && ptcb == task_reg_get_current_pointer(sg, entry) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          data_at(&OSTCBCur, void *, task_reg_get_current_pointer(sg, entry)) *
          task_reg_get_current_frame(sg, entry)
          which implies exists entry,
          task_reg_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          task_reg_get_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          task_reg_get_selection(sg, entry, prio, ptcb) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          UCOS2_inv(sg, entry)
        */
    } else {
        /*@ exists entry,
          task_reg_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          task_reg_get_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          0 <= prio && prio < 63 &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          UCOS2_inv(sg, entry)
          which implies exists entry,
          task_reg_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          task_reg_get_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          0 <= prio && prio < 63 &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          data_at(pointer_offset(&OSTCBPrioTbl, prio, void *), void *, task_reg_get_table_pointer(sg, entry, prio)) *
          task_reg_get_table_frame(sg, entry, prio)
        */
        ptcb = OSTCBPrioTbl[prio];
        /*@ exists entry,
          task_reg_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          task_reg_get_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          0 <= prio && prio < 63 && ptcb == task_reg_get_table_pointer(sg, entry, prio) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          data_at(pointer_offset(&OSTCBPrioTbl, prio, void *), void *, task_reg_get_table_pointer(sg, entry, prio)) *
          task_reg_get_table_frame(sg, entry, prio)
          which implies exists entry,
          task_reg_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          task_reg_get_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          task_reg_get_selection(sg, entry, prio, ptcb) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          UCOS2_inv(sg, entry)
        */
    }
    /*@ Assert exists entry,
      prio == prio@pre && id == id@pre && perr == perr@pre &&
      task_reg_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_reg_get_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
      task_reg_get_admission(critical, sg, invocation, before, caller, prio, id) &&
      0 <= prio && prio <= 255 && (prio < 63 || prio == 255) && id == 0 &&
      task_reg_get_scalar_valid(prio, id) &&
      task_reg_get_selection(sg, entry, prio, ptcb) &&
      task_reg_get_safe(critical, sg, invocation, before, caller, prio, id, X) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
      UCOS2_inv(sg, entry) * caller * undef_data_at(perr, unsigned char) *
      undef_data_at(&value, unsigned int)
    */
    if ((ptcb == (OS_TCB *)0) || (ptcb == ((OS_TCB *)1))) {
        OS_EXIT_CRITICAL();
        *perr = OS_ERR_TASK_NOT_EXIST;
        return (0u);
    }
    /*@ exists entry,
      task_reg_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_reg_get_admission(critical, sg, invocation, before, caller, prio, id) &&
      task_reg_get_scalar_valid(prio, id) &&
      task_reg_get_selection(sg, entry, prio, ptcb) && ptcb != 0 && ptcb != 1 &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
      UCOS2_inv(sg, entry) * caller
      which implies exists entry observed (residual : Assertion),
      task_reg_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_reg_get_selection(sg, entry, prio, ptcb) && id == 0 &&
      ptcb != 0 && ptcb != 1 &&
      task_reg_get_word_view(sg, entry, caller, ptcb, observed, residual) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
      data_at(pointer_offset(&(ptcb->OSTCBRegTbl), id, unsigned int), unsigned int, observed) *
      task_reg_get_read_frame(ptcb, observed, residual)
    */
    value = ptcb->OSTCBRegTbl[id];
    /*@ exists entry observed (residual : Assertion),
      task_reg_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_reg_get_selection(sg, entry, prio, ptcb) && id == 0 &&
      ptcb != 0 && ptcb != 1 && value == observed &&
      task_reg_get_word_view(sg, entry, caller, ptcb, observed, residual) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
      data_at(pointer_offset(&(ptcb->OSTCBRegTbl), id, unsigned int), unsigned int, observed) *
      task_reg_get_read_frame(ptcb, observed, residual)
      which implies exists entry (residual : Assertion),
      task_reg_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      task_reg_get_selection(sg, entry, prio, ptcb) && id == 0 &&
      ptcb != 0 && ptcb != 1 &&
      task_reg_get_word_view(sg, entry, caller, ptcb, value, residual) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
      UCOS2_inv(sg, entry) * caller
    */
    OS_EXIT_CRITICAL();
    *perr = OS_ERR_NONE;
    return (value);
}
