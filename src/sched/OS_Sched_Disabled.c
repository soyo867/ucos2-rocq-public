/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OS_Sched (void)
/*@ With (external : OsSchedExternalResources)
         (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
         (sg : StableGlobVars) (view : OsExecutionView) (mask : Z)
         (before : UCOS2_Verify_State)
    Require sched_disabled_addresses(sg, &OSIntNesting, &OSLockNesting) &&
            sched_disabled_completed_clients(critical, view) &&
            UCOS2_state_inv(sg, before) && sched_disabled_entry_source(view, before) &&
            sched_disabled_closed(external, platform, critical, sg, view, mask, before)
    Ensure sched_disabled_addresses(sg, &OSIntNesting, &OSLockNesting) &&
           sched_disabled_contextual_post(external, platform, critical, sg, view, mask, before)
*/
{
#if OS_CRITICAL_METHOD == 3u                           /* Allocate storage for CPU status register     */
    OS_CPU_SR  cpu_sr = 0u;
#endif



    /*@ sched_disabled_closed(external, platform, critical, sg, view, mask, before)
        which implies
        interrupt_platform_running(platform, os_execution_invocation(view), os_execution_origin(view), mask) *
        critical_region_outside(critical, sg, os_execution_invocation(view), before) *
        os_execution_view_resources(external, view)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (acquired : UCOS2_Verify_State),
        sched_disabled_addresses(sg, &OSIntNesting, &OSLockNesting) &&
        sched_disabled_completed_clients(critical, view) &&
        critical_region_interval(critical, sg, os_execution_invocation(view), before, acquired) &&
        interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, acquired) &&
        sched_disabled_context_rely(view, sg, before, acquired) &&
        sched_disabled_entry_source(view, acquired) && sched_disabled_protected_identity(acquired) &&
        critical_region_masked(platform, critical, sg, os_execution_invocation(view),
          os_execution_origin(view), cpu_sr, acquired) * UCOS2_inv(sg, acquired) *
        os_execution_view_resources(external, view)
    */
    /*@ Given acquired */
    /*@ sched_disabled_addresses(sg, &OSIntNesting, &OSLockNesting) &&
        sched_disabled_entry_source(view, acquired) && UCOS2_inv(sg, acquired)
        which implies
        sched_disabled_addresses(sg, &OSIntNesting, &OSLockNesting) &&
        sched_disabled_entry_source(view, acquired) &&
        0 < os_sched_ints(acquired) + os_sched_locks(acquired) &&
        0 <= os_sched_ints(acquired) && os_sched_ints(acquired) <= 255 &&
        0 <= os_sched_locks(acquired) && os_sched_locks(acquired) <= 255 &&
        data_at(&OSIntNesting, INT8U, os_sched_ints(acquired)) *
        data_at(&OSLockNesting, INT8U, os_sched_locks(acquired)) *
        sched_disabled_counter_frame(sg, acquired)
    */
    if (OSIntNesting == 0u) {                          /* Schedule only if all ISRs done and ...       */
        if (OSLockNesting == 0u) {                     /* ... scheduler is not locked                  */
            /*@ Assert 0 == 1 */
            OS_SchedNew();
            OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy];
            if (OSPrioHighRdy != OSPrioCur) {          /* No Ctx Sw if current task is highest rdy     */
#if OS_TASK_PROFILE_EN > 0u
                OSTCBHighRdy->OSTCBCtxSwCtr++;         /* Inc. # of context switches to this task      */
#endif
                OSCtxSwCtr++;                          /* Increment context switch counter             */

#if OS_TASK_CREATE_EXT_EN > 0u
#if defined(OS_TLS_TBL_SIZE) && (OS_TLS_TBL_SIZE > 0u)
                OS_TLS_TaskSw();
#endif
#endif

                OS_TASK_SW();                          /* Perform a context switch                     */
            }
        }
    }
    /*@ sched_disabled_addresses(sg, &OSIntNesting, &OSLockNesting) &&
        data_at(&OSIntNesting, INT8U, os_sched_ints(acquired)) *
        data_at(&OSLockNesting, INT8U, os_sched_locks(acquired)) *
        sched_disabled_counter_frame(sg, acquired)
        which implies
        sched_disabled_addresses(sg, &OSIntNesting, &OSLockNesting) && UCOS2_inv(sg, acquired)
    */
    /*@ Assert sched_disabled_addresses(sg, &OSIntNesting, &OSLockNesting) &&
        sched_disabled_completed_clients(critical, view) &&
        critical_region_interval(critical, sg, os_execution_invocation(view), before, acquired) &&
        interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, acquired) &&
        sched_disabled_context_rely(view, sg, before, acquired) &&
        sched_disabled_entry_source(view, acquired) && sched_disabled_protected_identity(acquired) &&
        critical_region_masked(platform, critical, sg, os_execution_invocation(view),
          os_execution_origin(view), cpu_sr, acquired) * UCOS2_inv(sg, acquired) *
        os_execution_view_resources(external, view)
    */
    OS_EXIT_CRITICAL();
}
