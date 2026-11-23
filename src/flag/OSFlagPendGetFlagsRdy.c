/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

OS_FLAGS  OSFlagPendGetFlagsRdy (void)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
    (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
    (mask: Z) (before: UCOS2_Verify_State) (caller: Assertion)
    (X: Z -> UCOS2_Verify_State -> Prop)
    Require &OSTCBCur == g_OSTCBCur(sg) &&
      flag_pend_get_flags_rdy_admission(critical, sg, invocation, before, caller) &&
      flag_pend_get_flags_rdy_safe(critical, sg, invocation, before, caller, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) * caller
    Ensure flag_pend_get_flags_rdy_api_post(platform, critical, sg, invocation, origin,
      mask, before, caller, __return, X)
*/
{
    OS_FLAGS      flags;
#if OS_CRITICAL_METHOD == 3u                               /* Allocate storage for CPU status register */
    OS_CPU_SR     cpu_sr = 0u;
#endif



    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State),
      &OSTCBCur == g_OSTCBCur(sg) &&
      flag_pend_get_flags_rdy_admission(critical, sg, invocation, before, caller) &&
      time_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
      UCOS2_inv(sg, entry) * caller
      which implies exists (entry: UCOS2_Verify_State) (snapshot: Z) (residual: Assertion),
      &OSTCBCur == g_OSTCBCur(sg) &&
      time_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      flag_pend_get_flags_rdy_observation(sg, caller, entry, snapshot) &&
      flag_pend_get_flags_rdy_word_view(sg, entry, caller,
        task_reg_get_current_pointer(sg, entry), snapshot, residual) &&
      task_reg_get_current_pointer(sg, entry) != 0 && 0 <= snapshot && snapshot <= 65535 &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
      data_at(&OSTCBCur, void *, task_reg_get_current_pointer(sg, entry)) *
      data_at(field_addr(task_reg_get_current_pointer(sg, entry), OS_TCB, OSTCBFlagsRdy), unsigned short, snapshot) *
      flag_pend_get_flags_rdy_read_frame(sg, entry, residual)
    */
    /*@ Given entry */
    /*@ Given snapshot */
    /*@ Given residual */
    flags = OSTCBCur->OSTCBFlagsRdy;
    /*@ &OSTCBCur == g_OSTCBCur(sg) && flags == snapshot &&
      time_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      flag_pend_get_flags_rdy_word_view(sg, entry, caller,
        task_reg_get_current_pointer(sg, entry), snapshot, residual) &&
      data_at(&OSTCBCur, void *, task_reg_get_current_pointer(sg, entry)) *
      data_at(field_addr(task_reg_get_current_pointer(sg, entry), OS_TCB, OSTCBFlagsRdy), unsigned short, snapshot) *
      flag_pend_get_flags_rdy_read_frame(sg, entry, residual)
      which implies flags == snapshot &&
      time_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
      UCOS2_inv(sg, entry) * caller
    */
    OS_EXIT_CRITICAL();
    return (flags);
}
