/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void OSIntExit (void)
/*@ With (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
         (port : OsIntExitPlatformResources) (critical : CriticalRegionResources)
         (sg : StableGlobVars) (context : OsIntExitCallContext) (mask : Z)
         (before : UCOS2_Verify_State)
         (X : OsIntExitOutcome -> UCOS2_Verify_State -> Prop)
    Require os_int_exit_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
      &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr,
      OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
      os_int_exit_program_pre(external, platform, port, critical, sg, context, mask, before, X)
    Ensure os_int_exit_program_post(platform, port, critical, sg, context, mask, before, X)
*/
{
#if OS_CRITICAL_METHOD == 3u
    OS_CPU_SR cpu_sr = 0u;
#endif

    /*@ os_int_exit_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr,
          OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        os_int_exit_program_pre(external, platform, port, critical, sg, context, mask, before, X)
        which implies
        os_int_exit_continuation(external, port, critical, sg, context, before, X) &&
        UCOS2_state_inv(sg, before) &&
        os_int_exit_acquire_safety(external, port, critical, sg, context, before) &&
        sched_new_global_addresses(sg, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy) &&
        os_int_exit_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr,
          OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        data_at(&OSRunning, unsigned char, os_int_exit_running(before)) *
        os_int_exit_outside_frame(platform, port, critical, sg, context, mask, before)
    */
    if (OSRunning == OS_TRUE) {
        OS_ENTER_CRITICAL();
        /*@ exists entry,
          os_int_exit_continuation(external, port, critical, sg, context, before, X) &&
          os_int_exit_body_facts(external, port, critical, sg, context, mask, cpu_sr, before, entry) &&
          sched_new_global_addresses(sg, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy) &&
          os_int_exit_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
            &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr,
            OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
          os_int_exit_inside_frame(platform, port, critical, sg, context, cpu_sr, entry) *
          os_sched_work_cells(sg, entry, os_sched_old_high(entry), os_sched_old_pointer(sg, entry), os_sched_counter(entry))
          which implies
          exists entry,
          os_int_exit_continuation(external, port, critical, sg, context, before, X) &&
          os_int_exit_body_facts(external, port, critical, sg, context, mask, cpu_sr, before, entry) &&
          0 <= os_sched_ints(entry) && os_sched_ints(entry) <= 255 &&
          sched_new_global_addresses(sg, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy) &&
          os_int_exit_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
            &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr,
            OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
          os_int_exit_inside_frame(platform, port, critical, sg, context, cpu_sr, entry) *
          data_at(&OSIntNesting, unsigned char, os_sched_ints(entry)) *
          data_at(&OSLockNesting, unsigned char, os_sched_locks(entry)) *
          sched_new_rep(sg, os_sched_group(entry), os_sched_rows(entry), os_sched_old_high(entry)) *
          PtrArray::full(OSTCBPrioTbl, 64, os_sched_table(sg, entry)) *
          data_at(&OSPrioCur, unsigned char, os_sched_current(entry)) *
          data_at(&OSTCBHighRdy, struct os_tcb *, os_sched_old_pointer(sg, entry)) *
          data_at(&OSCtxSwCtr, unsigned int, os_sched_counter(entry)) * os_sched_work_frame(sg, entry)
        */
        if (OSIntNesting > 0u) {
            OSIntNesting--;
        }
        /*@ Assert exists entry,
          os_int_exit_continuation(external, port, critical, sg, context, before, X) &&
          os_int_exit_body_facts(external, port, critical, sg, context, mask, cpu_sr, before, entry) &&
          sched_new_global_addresses(sg, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSPrioHighRdy) &&
          os_int_exit_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
            &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr,
            OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
          os_int_exit_inside_frame(platform, port, critical, sg, context, cpu_sr, entry) *
          data_at(&OSIntNesting, unsigned char, os_int_exit_counted_ints(entry)) *
          data_at(&OSLockNesting, unsigned char, os_sched_locks(entry)) *
          sched_new_rep(sg, os_sched_group(entry), os_sched_rows(entry), os_sched_old_high(entry)) *
          PtrArray::full(OSTCBPrioTbl, 64, os_sched_table(sg, entry)) *
          data_at(&OSPrioCur, unsigned char, os_sched_current(entry)) *
          data_at(&OSTCBHighRdy, struct os_tcb *, os_sched_old_pointer(sg, entry)) *
          data_at(&OSCtxSwCtr, unsigned int, os_sched_counter(entry)) *
          os_sched_work_frame(sg, entry)
        */
        if (OSIntNesting == 0u) {
            if (OSLockNesting == 0u) {
                OS_SchedNew();
                /*@ Assert exists entry,
                  os_int_exit_continuation(external, port, critical, sg, context, before, X) &&
          os_int_exit_body_facts(external, port, critical, sg, context, mask, cpu_sr, before, entry) &&
                  os_int_exit_counted_ints(entry) == 0 && os_sched_locks(entry) == 0 &&
                  os_int_exit_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
                    &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr,
                    OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                  0 <= os_sched_selected(entry) && os_sched_selected(entry) < 64 &&
                  os_int_exit_inside_frame(platform, port, critical, sg, context, cpu_sr, entry) *
                  data_at(&OSIntNesting, unsigned char, os_int_exit_counted_ints(entry)) *
                  data_at(&OSLockNesting, unsigned char, os_sched_locks(entry)) *
                  data_at(&OSPrioHighRdy, unsigned char, os_sched_selected(entry)) *
                  os_int_exit_ready_tables(sg, os_sched_group(entry), os_sched_rows(entry)) *
                  PtrArray::full(OSTCBPrioTbl, 64, os_sched_table(sg, entry)) *
                  data_at(&OSPrioCur, unsigned char, os_sched_current(entry)) *
                  data_at(&OSTCBHighRdy, struct os_tcb *, os_sched_old_pointer(sg, entry)) *
                  data_at(&OSCtxSwCtr, unsigned int, os_sched_counter(entry)) * os_sched_work_frame(sg, entry)
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
                    OS_TRACE_ISR_EXIT_TO_SCHEDULER();
                    /*@ Assert exists entry,
                      os_int_exit_transfer_program_pre(external, platform, port, critical, sg, context, cpu_sr, before, entry, X)
                    */
                    OSIntCtxSw();
                } else {
                    OS_TRACE_ISR_EXIT();
                }
            } else {
                OS_TRACE_ISR_EXIT();
            }
        } else {
            OS_TRACE_ISR_EXIT();
        }
        /*@ Assert exists entry,
          os_int_exit_continuation(external, port, critical, sg, context, before, X) &&
          os_int_exit_body_facts(external, port, critical, sg, context, mask, cpu_sr, before, entry) &&
          os_int_exit_requests_switch(true, entry) == false &&
          os_int_exit_inside_frame(platform, port, critical, sg, context, cpu_sr, entry) *
          UCOS2_inv(sg, os_int_exit_ready_checkpoint(true, entry)) * unmap_table_rep(sg)
        */
        OS_EXIT_CRITICAL();
    }
}
