/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void OS_Sched (void)

/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
         (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
         (region_entry before : UCOS2_Verify_State)
    Require &OSIntNesting == g_OSIntNesting(sg) && os_sched_ints(before) > 0 &&
      time_tick_sched_owned(platform, critical, sg, invocation, origin, region_entry, before)
    Ensure time_tick_sched_owned(platform, critical, sg, invocation, origin, region_entry, before)
*/
{
#if OS_CRITICAL_METHOD == 3u
    OS_CPU_SR cpu_sr = 0u;
#endif

    
    /*@ time_tick_sched_owned(platform, critical, sg, invocation, origin, region_entry, before)
      which implies
      interrupt_platform_running(platform, invocation, origin, 192) *
      critical_region_inside(critical, sg, invocation, region_entry) *
      UCOS2_inv(sg, before) * unmap_table_rep(sg) */
    OS_ENTER_CRITICAL();
    
    /*@ &OSIntNesting == g_OSIntNesting(sg) && os_sched_ints(before) > 0 &&
      UCOS2_inv(sg, before)
      which implies
      &OSIntNesting == g_OSIntNesting(sg) && os_sched_ints(before) > 0 &&
      UCOS2_state_inv(sg, before) && 0 <= os_sched_ints(before) && os_sched_ints(before) <= 255 &&
      data_at(&OSIntNesting, INT8U, os_sched_ints(before)) * time_tick_sched_interrupt_frame(sg, before)
    */
    if (OSIntNesting == 0u) {
        /*@ Assert 0 == 1 */
        if (OSLockNesting == 0u) {
            OS_SchedNew() ;
            
            OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy];
            if (OSPrioHighRdy != OSPrioCur) {
#if OS_TASK_PROFILE_EN > 0u
                OSTCBHighRdy->OSTCBCtxSwCtr++;
#endif
                OSCtxSwCtr++;

#if OS_TASK_CREATE_EXT_EN > 0u
#if defined(OS_TLS_TBL_SIZE) && (OS_TLS_TBL_SIZE > 0u)
                OS_TLS_TaskSw();
#endif
#endif

                
                OS_TASK_SW();
            }
        }
    }
    
    /*@ &OSIntNesting == g_OSIntNesting(sg) && UCOS2_state_inv(sg, before) &&
      data_at(&OSIntNesting, INT8U, os_sched_ints(before)) * time_tick_sched_interrupt_frame(sg, before)
      which implies UCOS2_inv(sg, before) */
    OS_EXIT_CRITICAL();
}
