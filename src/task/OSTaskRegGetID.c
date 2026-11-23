/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSTaskRegGetID (INT8U  *perr)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
         (sg : StableGlobVars) (before : UCOS2_Verify_State)
         (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
         (X : Z -> Z -> UCOS2_Verify_State -> Prop)
    Require task_reg_get_id_safe(critical, sg, invocation, before, X) &&
      task_reg_get_id_addresses(sg, &OSTaskRegNextAvailID) &&
      task_reg_get_id_pre(platform, critical, sg, invocation, origin, mask, before, perr)
    Ensure task_reg_get_id_post(platform, critical, sg, invocation, origin, mask, before, perr, __return, X)
*/
{
#if OS_CRITICAL_METHOD == 3u                                    /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif
    INT8U      id;


#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return ((INT8U)OS_TASK_REG_TBL_SIZE);
    }
#endif

    /*@ task_reg_get_id_pre(platform, critical, sg, invocation, origin, mask, before, perr)
      which implies
      UCOS2_state_inv(sg, before) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      critical_region_outside(critical, sg, invocation, before) *
      undef_data_at(perr, unsigned char)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists entry,
      task_reg_get_id_safe(critical, sg, invocation, before, X) &&
      perr == perr@pre &&
      UCOS2_state_inv(sg, entry) &&
      task_reg_get_id_addresses(sg, &OSTaskRegNextAvailID) &&
      critical_region_interval(critical, sg, invocation, before, entry) &&
      interrupt_saved_value(mask, cpu_sr) &&
      0 <= task_reg_get_id_next(entry) && task_reg_get_id_next(entry) <= 1 &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
      data_at(&OSTaskRegNextAvailID, unsigned char, task_reg_get_id_next(entry)) *
      task_reg_get_id_frame(sg, entry) * undef_data_at(perr, unsigned char) *
      undef_data_at(&id, unsigned char)
    */
    if (OSTaskRegNextAvailID >= OS_TASK_REG_TBL_SIZE) {         /* See if we exceeded the number of IDs available     */
       *perr = OS_ERR_NO_MORE_ID_AVAIL;                         /* Yes, cannot allocate more task register IDs        */
        /*@ Assert exists entry,
          task_reg_get_id_safe(critical, sg, invocation, before, X) &&
          perr == perr@pre &&
          critical_region_interval(critical, sg, invocation, before, entry) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_reg_get_id_effect(sg, entry, 1, 150, entry) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          UCOS2_inv(sg, entry) * data_at(perr, unsigned char, 150) *
          undef_data_at(&id, unsigned char)
        */
        OS_EXIT_CRITICAL();
        return ((INT8U)OS_TASK_REG_TBL_SIZE);
    }

    id   = OSTaskRegNextAvailID;                                /* Assign the next available ID                       */
    OSTaskRegNextAvailID++;                                     /* Increment available ID for next request            */
    /*@ Assert exists entry,
      task_reg_get_id_safe(critical, sg, invocation, before, X) &&
      perr == perr@pre &&
      critical_region_interval(critical, sg, invocation, before, entry) &&
      interrupt_saved_value(mask, cpu_sr) &&
      id == task_reg_get_id_next(entry) &&
      task_reg_get_id_effect(sg, entry, id, 0,
        task_reg_get_id_update(entry, task_reg_get_id_next(entry) + 1)) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
      UCOS2_inv(sg, task_reg_get_id_update(entry, task_reg_get_id_next(entry) + 1)) *
      undef_data_at(perr, unsigned char)
    */
    OS_EXIT_CRITICAL();
   *perr = OS_ERR_NONE;
    return (id);
}
