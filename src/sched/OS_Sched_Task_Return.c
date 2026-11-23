/* Annotation carrier for OS_Sched, pinned uC/OS-II V2.93.01.
 * Rebuild this report candidate with environment.c and annotation_carrier.py compose.
 * The first Save uses the exact configured OS_ENTER_CRITICAL expansion to bind its paired event.
 */
void  OS_Sched (void)
/*@ With (environment : TaskStackCallEnvironment) local
         (active : OsSchedCallContext -> UCOS2_Verify_State -> Assertion)
         (critical : CriticalRegionResources) (sg : StableGlobVars)
         (context : OsSchedCallContext) (mask : Z) (before : UCOS2_Verify_State)
    Require os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            kernel_sched_ready_clients(critical) &&
        FlagPendActiveProtocol::flag_pend_active_protocol(sg, active) &&
        FlagPendActiveCallerControl::flag_pend_active_requires_control(active) &&
        SchedStateDef::isRunning(SchedState(before)) == true &&
        os_sched_active_local_stable(active) &&
            kernel_tcb_stack_field_layout(sg) &&
            kernel_call_stack_available(context, before) &&
            task_idle_ready(sg, TskState(before)) &&
            (SchedStateDef::isRunning(SchedState(before)) == true &&
        SchedulerCalleePhaseComponent::os_sched_task_call_pre(task_sw_hook_call_environment(environment), local, active,
              sg, context, mask, before))
    Ensure os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
             &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
             &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
           SchedulerPhaseCandidate::os_sched_task_history_return_post(task_sw_hook_call_environment(environment), critical, active,
             sg, context, mask, before)
*/
{
#if OS_CRITICAL_METHOD == 3u                           /* Allocate storage for CPU status register     */
    OS_CPU_SR  cpu_sr = 0u;
#endif
    /*@ kernel_sched_ready_clients(critical) &&
        FlagPendActiveProtocol::flag_pend_active_protocol(sg, active) &&
        FlagPendActiveCallerControl::flag_pend_active_requires_control(active) &&
        os_sched_active_local_stable(active) &&
        (SchedStateDef::isRunning(SchedState(before)) == true &&
        SchedulerCalleePhaseComponent::os_sched_task_call_pre(task_sw_hook_call_environment(environment), local, active, sg, context, mask, before))
        which implies
        (SchedStateDef::isRunning(SchedState(before)) == true &&
        SchedulerCalleePhaseComponent::os_sched_task_entry_observation(context, before)) &&
        kernel_call_task_source(context, before) &&
        FlagPendActiveProtocol::flag_pend_active_protocol(sg, active) &&
        FlagPendActiveCallerControl::flag_pend_active_requires_control(active) &&
        os_sched_active_local_stable(active) &&
        (os_sched_ints(before) == 0 && os_sched_locks(before) == 0 && FlagPendEntryControl::flag_pend_active_entry(sg, active, before) &&
        os_sched_active_save_input(task_sw_hook_call_environment(environment), critical, local, active,
          sg, context, mask, before)) * unmap_table_rep(sg)
    */
    /*@ (os_sched_ints(before) == 0 && os_sched_locks(before) == 0 && FlagPendEntryControl::flag_pend_active_entry(sg, active, before) &&
        os_sched_active_save_input(task_sw_hook_call_environment(environment), critical, local, active,
          sg, context, mask, before)) * unmap_table_rep(sg)
        which implies
        os_sched_call_cut(sg, context, before) && kernel_sched_ready_clients(critical) &&
        ((os_sched_ints(before) == 0 && os_sched_locks(before) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, active, before)) &&
        flag_pend_caller_save_input(task_sw_hook_call_environment(environment), critical, local, active,
          sg, FlagPendTaskCaller(context), context, mask, before))
    */
    /*@ ((os_sched_ints(before) == 0 && os_sched_locks(before) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, active, before)) &&
        flag_pend_caller_save_input(task_sw_hook_call_environment(environment), critical, local, active,
          sg, FlagPendTaskCaller(context), context, mask, before))
        which implies exists (entry_heap : model),
        os_sched_active_heap_cut(flag_pend_caller_save_input(task_sw_hook_call_environment(environment),
          critical, local, active, sg, FlagPendTaskCaller(context), context, mask, before), entry_heap)
    */
    /*@ Given entry_heap */
    do {
        cpu_sr = OS_CPU_SR_Save()
        /*@ where environment=task_sw_hook_call_environment(environment),
            local=local, active=active, critical=critical, sg=sg,
            caller=FlagPendTaskCaller(context), call=context, mask=mask,
            before=before, entry_heap=entry_heap */;
    } while (0);
    /*@ (FlagPendActiveCallerControl::flag_pend_active_requires_control(active) &&
        os_sched_ints(before) == 0 && os_sched_locks(before) == 0 && SchedStateDef::isRunning(SchedState(before)) == true &&
        FlagPendActiveCaller::flag_pend_selected_caller_save_output(task_sw_hook_call_environment(environment), critical,
          local, active, sg, FlagPendTaskCaller(context), context, mask, before, entry_heap, cpu_sr))
        which implies exists (save_caller : FlagPendCaller) (save_scheduled : OsSchedCallContext)
          (save_entry : UCOS2_Verify_State) (save_local : Armv7aContinuation -> Assertion)
          (save_after_heap : model),
        SelectedCallerPhaseComponent::flag_pend_selected_caller_save_event(task_sw_hook_call_environment(environment), critical,
          local, active, sg, FlagPendTaskCaller(context), context, mask, cpu_sr, before,
          save_caller, save_scheduled, save_entry, save_local, entry_heap, save_after_heap) &&
        os_sched_active_heap_cut(flag_pend_caller_restore_input(task_sw_hook_call_environment(environment),
          critical, save_local, active, sg, save_caller, save_scheduled, cpu_sr, save_entry, save_entry), save_after_heap)
    */
    /*@ Given save_caller save_scheduled save_entry save_local save_after_heap */
    /*@ kernel_tcb_stack_field_layout(sg) && kernel_call_task_source(context, before) &&
        kernel_call_stack_available(context, before) && task_idle_ready(sg, TskState(before)) &&
        os_sched_call_cut(sg, context, before) && kernel_sched_ready_clients(critical) &&
        SelectedCallerPhaseComponent::flag_pend_selected_caller_save_event(task_sw_hook_call_environment(environment), critical,
          local, active, sg, FlagPendTaskCaller(context), context, mask, cpu_sr, before,
          save_caller, save_scheduled, save_entry, save_local, entry_heap, save_after_heap) &&
        os_sched_active_heap_cut(flag_pend_caller_restore_input(task_sw_hook_call_environment(environment),
          critical, save_local, active, sg, save_caller, save_scheduled, cpu_sr, save_entry, save_entry), save_after_heap)
        which implies exists (active_before : model),
        SelectedCallerPhaseComponent::flag_pend_selected_caller_save_event(task_sw_hook_call_environment(environment), critical,
          local, active, sg, FlagPendTaskCaller(context), context, mask, cpu_sr, before,
          save_caller, save_scheduled, save_entry, save_local, entry_heap, save_after_heap) &&
        SchedulerPairedPhaseComponent::os_sched_paired_save_entry_heap(task_sw_hook_call_environment(environment), critical, local,
          active, sg, context, mask, before, entry_heap, active_before) &&
        kernel_call_normal_return(context, before, save_scheduled, save_entry) &&
        kernel_call_control_rely(sg, before, save_entry) &&
        kernel_call_task_source(save_scheduled, save_entry) && os_sched_call_cut(sg, save_scheduled, save_entry) &&
        SchedulerActivePhaseComponent::os_sched_active_save_event(task_sw_hook_call_environment(environment), critical, local, active,
          sg, context, mask, cpu_sr, before, save_scheduled, save_entry, save_local, active_before) * unmap_table_rep(sg)
    */
    /*@ Given active_before */
    /* The next field-opening obligation retains the actual paired Save tuple.
     * Its current-priority cache transport remains to be supplied by that event. */
    /*@ Assert
        SelectedCallerPhaseComponent::flag_pend_selected_caller_save_event(task_sw_hook_call_environment(environment), critical,
          local, active, sg, FlagPendTaskCaller(context), context, mask, cpu_sr, before,
          save_caller, save_scheduled, save_entry, save_local, entry_heap, save_after_heap) &&
        SchedulerPairedPhaseComponent::os_sched_paired_save_entry_heap(task_sw_hook_call_environment(environment), critical, local,
          active, sg, context, mask, before, entry_heap, active_before) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        kernel_sched_ready_clients(critical) &&
        FlagPendActiveProtocol::flag_pend_active_protocol(sg, active) &&
        FlagPendActiveCallerControl::flag_pend_active_requires_control(active) &&
        os_sched_active_local_stable(active) &&
        SchedulerPhaseCandidate::os_sched_task_save_observation(task_sw_hook_call_environment(environment), critical, sg, context, mask, cpu_sr,
          before, save_scheduled, save_entry) &&
        (SchedStateDef::isRunning(SchedState(save_entry)) == true &&
        SchedulerCalleePhaseComponent::os_sched_task_entry_observation(save_scheduled, save_entry)) &&
        task_tcb_init_stack_same_call(save_scheduled, context) &&
        task_tcb_init_stack_source_preserved(context, before, save_entry) &&
        interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, save_entry) &&
        os_sched_call_cut(sg, save_scheduled, save_entry) &&
        task_stack_live_coverage(TskState(save_entry), task_stack_call_active_key(save_scheduled)) &&
        ContinuationPhaseEffects::os_sched_continuation_phase_save_effect(task_sw_hook_call_environment(environment), critical, sg,
          context, mask, cpu_sr, before, save_scheduled, save_entry) &&
        critical_region_masked(task_stack_call_platform(task_sw_hook_call_environment(environment)), critical, sg,
          os_sched_call_invocation(save_scheduled), os_sched_call_origin(save_scheduled), cpu_sr, save_entry) *
        task_tcb_init_stack_context(task_sw_hook_call_environment(environment), save_scheduled) *
        os_sched_fields_capsules(task_sw_hook_call_environment(environment), save_local, save_entry) * active(save_scheduled, save_entry) *
        data_at(&OSIntNesting, INT8U, os_sched_ints(save_entry)) *
        data_at(&OSLockNesting, INT8U, os_sched_locks(save_entry)) *
        sched_new_rep(sg, os_sched_group(save_entry), os_sched_rows(save_entry), os_sched_old_high(save_entry)) *
        PtrArray::full(OSTCBPrioTbl, 64, os_sched_table(sg, save_entry)) *
        data_at(&OSPrioCur, OS_PRIO, os_sched_current(save_entry)) *
        data_at(&OSTCBHighRdy, OS_TCB *, os_sched_old_pointer(sg, save_entry)) *
        data_at(&OSCtxSwCtr, INT32U, os_sched_counter(save_entry)) * os_sched_fields_work_frame(sg, save_entry)
    */
    if (OSIntNesting == 0u) {                          /* Schedule only if all ISRs done and ...       */
        if (OSLockNesting == 0u) {                     /* ... scheduler is not locked                  */
            OS_SchedNew();
            /*@ Assert exists (scheduled : OsSchedCallContext) (entry : UCOS2_Verify_State)
                     (entry_local : Armv7aContinuation -> Assertion),
                os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                  &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                  &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                kernel_sched_ready_clients(critical) &&
        FlagPendActiveProtocol::flag_pend_active_protocol(sg, active) &&
        FlagPendActiveCallerControl::flag_pend_active_requires_control(active) &&
        os_sched_active_local_stable(active) &&
                SchedulerPhaseCandidate::os_sched_task_save_observation(task_sw_hook_call_environment(environment), critical, sg, context, mask, cpu_sr,
          before, scheduled, entry) &&
        (SchedStateDef::isRunning(SchedState(entry)) == true &&
        SchedulerCalleePhaseComponent::os_sched_task_entry_observation(scheduled, entry)) &&
        task_tcb_init_stack_same_call(scheduled, context) &&
                task_tcb_init_stack_source_preserved(context, before, entry) &&
                interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, entry) &&
                os_sched_call_cut(sg, scheduled, entry) &&
                task_stack_live_coverage(TskState(entry), task_stack_call_active_key(scheduled)) &&
                os_sched_ints(entry) == 0 && os_sched_locks(entry) == 0 &&
                0 <= os_sched_selected(entry) && os_sched_selected(entry) < 64 &&
                Znth(os_sched_selected(entry), os_sched_table(sg, entry), 0) ==
                  os_sched_selected_tcb(sg, entry) &&
                ContinuationPhaseEffects::os_sched_continuation_phase_save_effect(task_sw_hook_call_environment(environment), critical, sg,
                  context, mask, cpu_sr, before, scheduled, entry) &&
                critical_region_masked(task_stack_call_platform(task_sw_hook_call_environment(environment)), critical, sg,
                  os_sched_call_invocation(scheduled), os_sched_call_origin(scheduled), cpu_sr, entry) *
                task_tcb_init_stack_context(task_sw_hook_call_environment(environment), scheduled) *
                os_sched_fields_capsules(task_sw_hook_call_environment(environment), entry_local, entry) * active(scheduled, entry) *
                data_at(&OSIntNesting, INT8U, os_sched_ints(entry)) *
                data_at(&OSLockNesting, INT8U, os_sched_locks(entry)) *
                data_at(&OSRdyGrp, OS_PRIO, os_sched_group(entry)) *
                UCharArray::full(OSRdyTbl, 8, os_sched_rows(entry)) * unmap_table_rep(sg) *
                data_at(&OSPrioHighRdy, OS_PRIO, os_sched_selected(entry)) *
                PtrArray::full(OSTCBPrioTbl, 64, os_sched_table(sg, entry)) *
                data_at(&OSPrioCur, OS_PRIO, os_sched_current(entry)) *
                data_at(&OSTCBHighRdy, OS_TCB *, os_sched_old_pointer(sg, entry)) *
                data_at(&OSCtxSwCtr, INT32U, os_sched_counter(entry)) * os_sched_fields_work_frame(sg, entry)
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

                /*@ Assert exists (scheduled : OsSchedCallContext) (entry : UCOS2_Verify_State)
                     (entry_local : Armv7aContinuation -> Assertion),
                    os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                      &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                      &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                    kernel_sched_ready_clients(critical) &&
        FlagPendActiveProtocol::flag_pend_active_protocol(sg, active) &&
        FlagPendActiveCallerControl::flag_pend_active_requires_control(active) &&
        os_sched_active_local_stable(active) &&
                    SchedulerPhaseCandidate::os_sched_task_save_observation(task_sw_hook_call_environment(environment), critical, sg, context, mask, cpu_sr,
          before, scheduled, entry) &&
        (SchedStateDef::isRunning(SchedState(entry)) == true &&
        SchedulerCalleePhaseComponent::os_sched_task_entry_observation(scheduled, entry)) &&
        task_tcb_init_stack_same_call(scheduled, context) &&
                    task_tcb_init_stack_source_preserved(context, before, entry) &&
                    interrupt_saved_value(mask, cpu_sr) &&
                    os_sched_call_cut(sg, scheduled, entry) &&
                    ContinuationPhaseEffects::os_sched_continuation_phase_save_effect(task_sw_hook_call_environment(environment), critical, sg,
                      context, mask, cpu_sr, before, scheduled, entry) &&
                    SchedulerCalleePhaseComponent::os_sched_task_switch_pre(task_sw_hook_call_environment(environment), critical, entry_local, active, sg, scheduled, cpu_sr, entry, entry)
                */
                    /*@ Given scheduled entry entry_local */
                /*@ SchedulerCalleePhaseComponent::os_sched_task_switch_pre(task_sw_hook_call_environment(environment), critical, entry_local, active,
                      sg, scheduled, cpu_sr, entry, entry)
                    which implies exists (switch_heap : model),
                    os_sched_active_heap_cut(SchedulerCalleePhaseComponent::os_sched_task_switch_pre(task_sw_hook_call_environment(environment), critical, entry_local, active,
                      sg, scheduled, cpu_sr, entry, entry), switch_heap)
                */
                /*@ Given switch_heap */
                OS_TASK_SW();                          /* Perform a context switch                     */
                /*@ SchedulerCalleePhaseComponent::os_sched_task_switch_source_output(task_sw_hook_call_environment(environment), critical,
                      entry_local, active, sg, scheduled, cpu_sr, entry, entry, switch_heap)
                    which implies
                    SchedulerCalleePhaseComponent::os_sched_task_switch_output(task_sw_hook_call_environment(environment), critical,
                      entry_local, active, sg, scheduled, cpu_sr, entry, entry, switch_heap)
                */
            }
        }
    }
    /*@ Assert exists (history_scheduled history_returned : OsSchedCallContext)
                     (history_entry history_final : UCOS2_Verify_State)
                     (history_local : Armv7aContinuation -> Assertion),
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        kernel_sched_ready_clients(critical) &&
        FlagPendActiveProtocol::flag_pend_active_protocol(sg, active) &&
        FlagPendActiveCallerControl::flag_pend_active_requires_control(active) &&
        os_sched_active_local_stable(active) &&
        SchedulerPhaseCandidate::os_sched_task_save_observation(task_sw_hook_call_environment(environment), critical, sg, context, mask, cpu_sr,
          before, history_scheduled, history_entry) &&
        kernel_call_task_source(history_scheduled, history_entry) &&
        SchedulerPhaseCandidate::os_sched_task_body_observation(task_sw_hook_call_environment(environment), critical, sg, history_scheduled,
          history_entry, history_returned, history_final) &&
        task_tcb_init_stack_same_call(history_scheduled, context) &&
        task_tcb_init_stack_source_preserved(context, before, history_entry) &&
        interrupt_saved_value(mask, cpu_sr) &&
        os_sched_call_cut(sg, history_scheduled, history_entry) &&
        SchedulerPhaseCandidate::os_sched_task_body_source(task_sw_hook_call_environment(environment), critical, sg,
          history_entry, history_scheduled, history_returned, history_final) && UCOS2_state_inv(sg, history_final) &&
        ContinuationPhaseEffects::os_sched_continuation_phase_save_effect(task_sw_hook_call_environment(environment), critical, sg,
          context, mask, cpu_sr, before, history_scheduled, history_entry) &&
        (SchedStateDef::isRunning(SchedState(history_final)) == true &&
        (os_sched_ints(history_final) == 0 && os_sched_locks(history_final) == 0 &&
        SchedulerCalleePhaseComponent::os_sched_task_restore_input(task_sw_hook_call_environment(environment), critical, history_local, active,
          sg, history_returned, cpu_sr, history_entry, history_final))) * unmap_table_rep(sg)
    */
    /*@ Given history_scheduled history_returned history_entry history_final history_local */
    /*@ FlagPendActiveProtocol::flag_pend_active_protocol(sg, active) &&
        FlagPendActiveCallerControl::flag_pend_active_requires_control(active) &&
        (SchedStateDef::isRunning(SchedState(history_final)) == true &&
        (os_sched_ints(history_final) == 0 && os_sched_locks(history_final) == 0 &&
        SchedulerCalleePhaseComponent::os_sched_task_restore_input(task_sw_hook_call_environment(environment), critical, history_local, active,
          sg, history_returned, cpu_sr, history_entry, history_final))) * unmap_table_rep(sg)
        which implies
        os_sched_task_current_ready(history_returned, history_final) &&
        ((os_sched_ints(history_final) == 0 && os_sched_locks(history_final) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, active, history_final)) &&
        flag_pend_caller_restore_input(task_sw_hook_call_environment(environment), critical, history_local, active,
          sg, FlagPendTaskCaller(history_returned), history_returned, cpu_sr, history_entry, history_final))
    */
    /*@ ((os_sched_ints(history_final) == 0 && os_sched_locks(history_final) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, active, history_final)) &&
        flag_pend_caller_restore_input(task_sw_hook_call_environment(environment), critical, history_local, active,
          sg, FlagPendTaskCaller(history_returned), history_returned, cpu_sr, history_entry, history_final))
        which implies exists (restore_heap : model),
          os_sched_active_heap_cut(flag_pend_caller_restore_input(task_sw_hook_call_environment(environment), critical,
            history_local, active, sg, FlagPendTaskCaller(history_returned), history_returned, cpu_sr,
            history_entry, history_final), restore_heap)
    */
    /*@ Given restore_heap */
    do {
        OS_CPU_SR_Restore(cpu_sr)
        /*@ where environment=task_sw_hook_call_environment(environment), critical=critical,
            local=history_local, active=active, sg=sg,
            caller=FlagPendTaskCaller(history_returned), call=history_returned, saved=cpu_sr,
            acquired=history_entry, released=history_final, release_heap=restore_heap */;
        /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(active) &&
            FlagPendActiveCaller::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(environment), critical, history_local, active, sg, FlagPendTaskCaller(history_returned), history_returned, cpu_sr, history_entry, history_final, restore_heap)
            which implies
            SelectedCallerPhaseComponent::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(environment), critical, history_local, active, sg, FlagPendTaskCaller(history_returned), history_returned, cpu_sr, history_entry, history_final, restore_heap)
        */
    } while (0);
}
