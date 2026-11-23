/* Annotation carrier for OS_Sched, pinned uC/OS-II V2.93.01.
 * Original headers, configuration and callee declarations: ../../overlays/sched/sched_del_history_environment.patch.
 * Reproduce the canonical translation unit using the module README; do not expand macros here.
 */
void  OS_Sched (void)
/*@ With (environment : TaskStackCallEnvironment) saved_local
         (critical : CriticalRegionResources) (sg : StableGlobVars)
         (context : OsSchedCallContext) (mask : Z) (before : UCOS2_Verify_State)
    Require os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            kernel_sched_ready_clients(critical) &&
            os_sched_continuation_call_pre(environment, saved_local, mutex_del_stack_resources,
              sg, context, mask, before)
    Ensure os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
             &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
             &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
           sched_del_history_return_post(environment, critical, saved_local,
             sg, context, mask, before)
*/
{
#if OS_CRITICAL_METHOD == 3u                           /* Allocate storage for CPU status register     */
    OS_CPU_SR  cpu_sr = 0u;
#endif
    /*@ os_sched_continuation_call_pre(environment, saved_local, mutex_del_stack_resources,
          sg, context, mask, before)
        which implies
        os_sched_call_cut(sg, context, before) &&
        sched_del_continuation_save_input(environment, critical, saved_local,
          sg, context, mask, before)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (scheduled : OsSchedCallContext) (entry : UCOS2_Verify_State),
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        kernel_sched_ready_clients(critical) &&
        task_tcb_init_stack_same_call(scheduled, context) &&
        sem_pend_modular_call_history(environment, critical, sg, context, before, scheduled, entry) &&
        task_tcb_init_stack_source_preserved(context, before, entry) &&
        interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, entry) &&
        os_sched_call_cut(sg, scheduled, entry) &&
        task_stack_live_coverage(TskState(entry), task_stack_call_active_key(scheduled)) &&
        critical_region_masked(task_stack_call_platform(environment), critical, sg,
          os_sched_call_invocation(scheduled), os_sched_call_origin(scheduled), cpu_sr, entry) *
        task_tcb_init_stack_context(environment, scheduled) *
        task_tcb_init_continuation_capsules(environment, saved_local, entry) *
                sched_del_continuation_frame(sg, entry) *
        data_at(&OSIntNesting, INT8U, os_sched_ints(entry)) *
        data_at(&OSLockNesting, INT8U, os_sched_locks(entry)) *
        sched_new_rep(sg, os_sched_group(entry), os_sched_rows(entry), os_sched_old_high(entry)) *
        PtrArray::full(OSTCBPrioTbl, 64, os_sched_table(sg, entry)) *
        data_at(&OSPrioCur, OS_PRIO, os_sched_current(entry)) *
        data_at(&OSTCBHighRdy, OS_TCB *, os_sched_old_pointer(sg, entry)) *
        data_at(&OSCtxSwCtr, INT32U, os_sched_counter(entry)) * os_sched_work_frame(sg, entry)
    */
    if (OSIntNesting == 0u) {                          /* Schedule only if all ISRs done and ...       */
        if (OSLockNesting == 0u) {                     /* ... scheduler is not locked                  */
            OS_SchedNew();
            /*@ Assert exists (scheduled : OsSchedCallContext) (entry : UCOS2_Verify_State),
                os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                  &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                  &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                kernel_sched_ready_clients(critical) &&
                task_tcb_init_stack_same_call(scheduled, context) &&
                sem_pend_modular_call_history(environment, critical, sg, context, before, scheduled, entry) &&
                task_tcb_init_stack_source_preserved(context, before, entry) &&
                interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, entry) &&
                os_sched_call_cut(sg, scheduled, entry) &&
                task_stack_live_coverage(TskState(entry), task_stack_call_active_key(scheduled)) &&
                os_sched_ints(entry) == 0 && os_sched_locks(entry) == 0 &&
                0 <= os_sched_selected(entry) && os_sched_selected(entry) < 64 &&
                Znth(os_sched_selected(entry), os_sched_table(sg, entry), 0) ==
                  os_sched_selected_tcb(sg, entry) &&
                critical_region_masked(task_stack_call_platform(environment), critical, sg,
                  os_sched_call_invocation(scheduled), os_sched_call_origin(scheduled), cpu_sr, entry) *
                task_tcb_init_stack_context(environment, scheduled) *
                task_tcb_init_continuation_capsules(environment, saved_local, entry) *
                sched_del_continuation_frame(sg, entry) *
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

                /*@ Assert exists (scheduled : OsSchedCallContext) (entry : UCOS2_Verify_State),
                    os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                      &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                      &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                    kernel_sched_ready_clients(critical) &&
                    task_tcb_init_stack_same_call(scheduled, context) &&
                    sem_pend_modular_call_history(environment, critical, sg, context, before, scheduled, entry) &&
                    task_tcb_init_stack_source_preserved(context, before, entry) &&
                    interrupt_saved_value(mask, cpu_sr) &&
                    os_sched_call_cut(sg, scheduled, entry) &&
                    os_sched_continuation_switch_pre(environment, critical, saved_local,
                      mutex_del_stack_resources, sg, scheduled, cpu_sr, entry, entry)
                */
                OS_TASK_SW();                          /* Perform a context switch                     */
            }
        }
    }
    /*@ Assert exists (scheduled returned : OsSchedCallContext)
                     (entry final : UCOS2_Verify_State),
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        kernel_sched_ready_clients(critical) &&
        task_tcb_init_stack_same_call(scheduled, context) &&
        sem_pend_modular_call_history(environment, critical, sg, context, before, scheduled, entry) &&
        task_tcb_init_stack_source_preserved(context, before, entry) &&
        interrupt_saved_value(mask, cpu_sr) &&
        os_sched_call_cut(sg, scheduled, entry) &&
        os_sched_c_return(task_stack_call_external(environment), critical, sg,
          entry, scheduled, returned, final) && UCOS2_state_inv(sg, final) &&
        sched_del_continuation_restore_input(environment, critical, saved_local,
          sg, returned, cpu_sr, entry, final)
    */
    OS_EXIT_CRITICAL();
}
