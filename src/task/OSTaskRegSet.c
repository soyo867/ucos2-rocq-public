/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSTaskRegSet (INT8U    prio,
                    INT8U    id,
                    INT32U   value,
                    INT8U   *perr)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
         (sg : StableGlobVars) (before : UCOS2_Verify_State)
         (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
         (caller : Assertion) (X : Z -> UCOS2_Verify_State -> Prop)
    Require task_reg_set_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
      task_reg_set_safe(critical, sg, invocation, before, caller, prio, id, value, X) &&
      task_reg_set_pre(platform, critical, sg, invocation, origin, mask, before,
        prio, id, value, perr, caller)
    Ensure task_reg_set_post(platform, critical, sg, invocation, origin, mask, before,
      prio, id, value, perr, caller, X)
*/
{
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif
    OS_TCB    *ptcb;

    /*@ 0 <= prio && prio < 256 by local */
    /*@ 0 <= id && id < 256 by local */
    /*@ 0 <= value && value < 4294967296 by local */
    /*@ task_reg_set_pre(platform, critical, sg, invocation, origin, mask, before,
          prio, id, value, perr, caller)
      which implies
      UCOS2_state_inv(sg, before) &&
      task_reg_set_self_admission(critical, sg, invocation, before, prio, id, value, caller) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      critical_region_outside(critical, sg, invocation, before) *
      caller * undef_data_at(perr, unsigned char)
    */

#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return;
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (prio >= OS_LOWEST_PRIO) {
        if (prio != OS_PRIO_SELF) {
            *perr = OS_ERR_PRIO_INVALID;
            return;
        }
    }
    if (id >= OS_TASK_REG_TBL_SIZE) {
        *perr = OS_ERR_ID_INVALID;
        return;
    }
#endif
    OS_ENTER_CRITICAL();
    /*@ Assert exists entry,
      prio == prio@pre && id == id@pre && value == value@pre && perr == perr@pre &&
      0 <= prio && task_reg_set_priority_valid(prio) && id == 0 &&
      0 <= value && value < 4294967296 &&
      task_reg_set_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
      task_reg_set_self_admission(critical, sg, invocation, before, prio, id, value, caller) &&
      UCOS2_state_inv(sg, entry) &&
      critical_region_interval(critical, sg, invocation, before, entry) &&
      interrupt_saved_value(mask, cpu_sr) &&
      task_reg_set_safe(critical, sg, invocation, before, caller, prio, id, value, X) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
      UCOS2_inv(sg, entry) * caller * undef_data_at(perr, unsigned char) *
      undef_data_at(&ptcb, struct os_tcb *)
    */
    if (prio == OS_PRIO_SELF) {                  /* See if need to get register from current task      */
        /*@ Assert exists entry,
          prio == prio@pre && id == id@pre && value == value@pre && perr == perr@pre &&
          prio == 255 && id == 0 && 0 <= value && value < 4294967296 &&
          task_reg_set_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          task_reg_set_self_admission(critical, sg, invocation, before, prio, id, value, caller) &&
          UCOS2_state_inv(sg, entry) &&
          critical_region_interval(critical, sg, invocation, before, entry) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_reg_set_safe(critical, sg, invocation, before, caller, prio, id, value, X) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          data_at(&OSTCBCur, struct os_tcb *, task_reg_set_current_pointer(sg, entry)) *
          task_reg_set_current_frame(sg, entry) * caller *
          undef_data_at(perr, unsigned char) * undef_data_at(&ptcb, struct os_tcb *)
        */
        ptcb = OSTCBCur;
    } else {
        /*@ Assert exists entry,
          prio == prio@pre && id == id@pre && value == value@pre && perr == perr@pre &&
          0 <= prio && prio < 63 && id == 0 && 0 <= value && value < 4294967296 &&
          task_reg_set_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          task_reg_set_self_admission(critical, sg, invocation, before, prio, id, value, caller) &&
          UCOS2_state_inv(sg, entry) &&
          critical_region_interval(critical, sg, invocation, before, entry) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_reg_set_safe(critical, sg, invocation, before, caller, prio, id, value, X) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          data_at(pointer_offset(&OSTCBPrioTbl, prio, struct os_tcb *), struct os_tcb *,
            task_reg_set_table_pointer(sg, entry, prio)) *
          task_reg_set_table_frame(sg, entry, prio) * caller *
          undef_data_at(perr, unsigned char) * undef_data_at(&ptcb, struct os_tcb *)
        */
        ptcb = OSTCBPrioTbl[prio];
    }
    /*@ Assert exists entry,
      prio == prio@pre && id == id@pre && value == value@pre && perr == perr@pre &&
      0 <= prio && task_reg_set_priority_valid(prio) && id == 0 &&
      0 <= value && value < 4294967296 &&
      ptcb == task_reg_set_pointer(sg, entry, prio) &&
      task_reg_set_self_admission(critical, sg, invocation, before, prio, id, value, caller) &&
      UCOS2_state_inv(sg, entry) &&
      critical_region_interval(critical, sg, invocation, before, entry) &&
      interrupt_saved_value(mask, cpu_sr) &&
      task_reg_set_safe(critical, sg, invocation, before, caller, prio, id, value, X) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
      UCOS2_inv(sg, entry) * caller * undef_data_at(perr, unsigned char)
    */
    if ((ptcb == (OS_TCB *)0) || (ptcb == ((OS_TCB *)1))) {
        /*@ Assert exists entry,
          prio == prio@pre && id == id@pre && value == value@pre && perr == perr@pre &&
          critical_region_interval(critical, sg, invocation, before, entry) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_reg_set_effect(sg, entry, caller, prio, id, value, ptcb, 67, entry, caller) &&
          task_reg_set_safe(critical, sg, invocation, before, caller, prio, id, value, X) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          UCOS2_inv(sg, entry) * caller * undef_data_at(perr, unsigned char)
        */
        OS_EXIT_CRITICAL();
        *perr = OS_ERR_TASK_NOT_EXIST;
        return;
    }
    /*@ Assert exists entry released (after_caller : Assertion) (residual : Assertion),
      prio == prio@pre && id == id@pre && value == value@pre && perr == perr@pre &&
      0 <= prio && task_reg_set_priority_valid(prio) && id == 0 &&
      0 <= value && value < 4294967296 &&
      ptcb == task_reg_set_pointer(sg, entry, prio) && ptcb != 0 && ptcb != 1 &&
      critical_region_interval(critical, sg, invocation, before, entry) &&
      interrupt_saved_value(mask, cpu_sr) &&
      task_reg_set_store_closure(sg, entry, caller, ptcb, value, released, after_caller, residual) &&
      task_reg_set_safe(critical, sg, invocation, before, caller, prio, id, value, X) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
      UIntArray::undef_full(&(ptcb->OSTCBRegTbl), 1) * residual *
      undef_data_at(perr, unsigned char)
    */
    ptcb->OSTCBRegTbl[id] = value;
    /*@ Assert exists entry released (after_caller : Assertion),
      prio == prio@pre && id == id@pre && value == value@pre && perr == perr@pre &&
      critical_region_interval(critical, sg, invocation, before, entry) &&
      interrupt_saved_value(mask, cpu_sr) &&
      task_reg_set_effect(sg, entry, caller, prio, id, value, ptcb, 0, released, after_caller) &&
      task_reg_set_safe(critical, sg, invocation, before, caller, prio, id, value, X) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
      UCOS2_inv(sg, released) * after_caller * undef_data_at(perr, unsigned char)
    */
    OS_EXIT_CRITICAL();
    *perr                 = OS_ERR_NONE;
}
