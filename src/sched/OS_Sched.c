/* Single-function OS_Sched carrier for the OSSchedUnlock callee.
 * Rebuild with the pinned profile and sched_generic environment fragments.
 */

void OS_Sched (void)
/*@ With (external : OsSchedExternalResources)
         (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
         (sg : StableGlobVars) (before : UCOS2_Verify_State)
         (context : OsSchedCallContext) (mask : Z)
    Require os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            os_sched_pre(external, platform, critical, sg, context, mask, before)
    Ensure os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
           os_sched_post(external, platform, critical, sg, context, mask, before)
*/
{
#if OS_CRITICAL_METHOD == 3u
    OS_CPU_SR cpu_sr = 0u;
#endif

    /*@ os_sched_pre(external, platform, critical, sg, context, mask, before)
        which implies
        UCOS2_state_inv(sg, before) &&
        os_sched_acquire_safety(external, critical, sg, context, before) &&
        interrupt_platform_running(platform, os_sched_call_invocation(context),
          os_sched_call_origin(context), mask) *
        critical_region_outside(critical, sg, os_sched_call_invocation(context), before) *
        os_sched_context_resources(external, context) * unmap_table_rep(sg)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (entry : UCOS2_Verify_State),
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        critical_region_interval(critical, sg, os_sched_call_invocation(context), before, entry) &&
        interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, entry) &&
        os_sched_entry_safety(external, sg, context, entry) &&
        critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry) *
        os_sched_context_resources(external, context) *
        data_at(&OSIntNesting, INT8U, os_sched_ints(entry)) *
        data_at(&OSLockNesting, INT8U, os_sched_locks(entry)) *
        sched_new_rep(sg, os_sched_group(entry), os_sched_rows(entry), os_sched_old_high(entry)) *
        PtrArray::full(OSTCBPrioTbl, 64, os_sched_table(sg, entry)) *
        data_at(&OSPrioCur, OS_PRIO, os_sched_current(entry)) *
        data_at(&OSTCBHighRdy, OS_TCB *, os_sched_old_pointer(sg, entry)) *
        data_at(&OSCtxSwCtr, INT32U, os_sched_counter(entry)) * os_sched_work_frame(sg, entry)
    */
    if (OSIntNesting == 0u) {
        if (OSLockNesting == 0u) {
            OS_SchedNew() /*@ where frame = os_sched_context_resources(external, context) */;
            /*@ Assert exists (entry : UCOS2_Verify_State),
                os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                  &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                  &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                critical_region_interval(critical, sg, os_sched_call_invocation(context), before, entry) &&
                interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, entry) &&
                os_sched_entry_safety(external, sg, context, entry) &&
                os_sched_ints(entry) == 0 && os_sched_locks(entry) == 0 &&
                0 <= os_sched_selected(entry) && os_sched_selected(entry) < 64 &&
                Znth(os_sched_selected(entry), os_sched_table(sg, entry), 0) ==
                  os_sched_selected_tcb(sg, entry) &&
                critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry) *
                os_sched_context_resources(external, context) *
                data_at(&OSIntNesting, INT8U, os_sched_ints(entry)) *
                data_at(&OSLockNesting, INT8U, os_sched_locks(entry)) *
                data_at(&OSRdyGrp, OS_PRIO, os_sched_group(entry)) *
                UCharArray::full(OSRdyTbl, 8, os_sched_rows(entry)) * unmap_table_rep(sg) *
                data_at(&OSPrioHighRdy, OS_PRIO, os_sched_selected(entry)) *
                PtrArray::full(OSTCBPrioTbl, 64, os_sched_table(sg, entry)) *
                data_at(&OSPrioCur, OS_PRIO, os_sched_current(entry)) *
                data_at(&OSTCBHighRdy, OS_TCB *, os_sched_old_pointer(sg, entry)) *
                data_at(&OSCtxSwCtr, INT32U, os_sched_counter(entry)) * os_sched_work_frame(sg, entry)
            */
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

                /*@ Assert exists (entry : UCOS2_Verify_State),
                    os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                      &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                      &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                    critical_region_interval(critical, sg, os_sched_call_invocation(context), before, entry) &&
                    interrupt_saved_value(mask, cpu_sr) &&
                    os_sched_switch_requested(entry) &&
                    os_sched_switch_input(external, sg, context, entry) &&
                    critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry) *
                    UCOS2_inv(sg, os_sched_prefix_state(entry)) *
                    os_sched_context_resources(external, context) * unmap_table_rep(sg)
                */
                OS_TASK_SW();
            }
        }
    }
    /*@ Assert exists (entry final : UCOS2_Verify_State) (returned : OsSchedCallContext),
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        critical_region_interval(critical, sg, os_sched_call_invocation(context), before, entry) &&
        interrupt_saved_value(mask, cpu_sr) &&
        os_sched_c_return(external, critical, sg, entry, context, returned, final) &&
        critical_region_masked(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), cpu_sr, entry) *
        UCOS2_inv(sg, final) * os_sched_context_resources(external, returned) * unmap_table_rep(sg)
    */
    OS_EXIT_CRITICAL();
}
