/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSTaskCreateExt (void   (*task)(void *p_arg),
                        void    *p_arg,
                        OS_STK  *ptos,
                        INT8U    prio,
                        INT16U   id,
                        OS_STK  *pbos,
                        INT32U   stk_size,
                        void    *pext,
                        INT16U   opt)
/*@ boot_phase_spec
    With (environment : TaskStackCallEnvironment) saved_local (critical : CriticalRegionResources)
         (sg : StableGlobVars) (args : TaskCreateArgs) (region : TaskStackRegion) (task_return : Z)
         (lower old_frame upper prefix middle suffix : list (option Z))
         (after_lower after_frame after_upper : list (option Z)) (call : OsSchedCallContext)
         (mask : Z) (initial : UCOS2_Verify_State) (LitMap : String -> Z) (literals : list String)
         (X : Z -> UCOS2_Verify_State -> Prop)
    Require task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
          task_create_ext_arguments(args, task, p_arg, ptos, prio, id, pbos, stk_size, pext, opt) && task_return == &OS_TaskReturn &&
          task_create_ext_clear_binding(region, args, task_create_stack_old_image(lower, old_frame, upper), prefix, middle, suffix) &&
          after_lower == task_create_ext_after_lower(args, lower, old_frame, upper, prefix, middle, suffix) &&
          after_frame == task_create_ext_after_frame(args, lower, old_frame, upper, prefix, middle, suffix) &&
          after_upper == task_create_ext_after_upper(args, lower, old_frame, upper, prefix, middle, suffix) &&
          kernel_sched_ready_clients(critical) && kernel_tcb_stack_field_layout(sg) &&
          task_create_safe(initial, task_create_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), call, mask), X) &&
          task_create_runtime_call_input(args, call, initial) &&
          task_create_name_api_pre(environment, critical, saved_local, sg, region, args, task_return,
            lower, old_frame, upper, call, mask, initial, LitMap, literals)
    Ensure task_create_ext_boot_phase_post(environment, critical, saved_local, sg, region, args, task_return,
            lower, old_frame, upper, prefix, middle, suffix, call, mask, initial, __return, X) * GlobalStrings_missing(LitMap, literals)
*/
{
    OS_STK     *psp;
    INT8U       err;
#if OS_CRITICAL_METHOD == 3u                 /* Allocate storage for CPU status register               */
    OS_CPU_SR   cpu_sr = 0u;
#endif

/*@ task_create_name_api_pre(environment, critical, saved_local, sg, region, args, task_return,
          lower, old_frame, upper, call, mask, initial, LitMap, literals)
    which implies
          task_create_default_name_binding(LitMap("?"), initial) &&
          task_create_continuation_pre(environment, critical, saved_local, sg, region, args, task_return,
            lower, old_frame, upper, LitMap("?"), call, mask, initial) *
          GlobalStrings_missing(LitMap, literals)
*/

#ifdef OS_SAFETY_CRITICAL_IEC61508
    if (OSSafetyCriticalStartFlag == OS_TRUE) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return (OS_ERR_ILLEGAL_CREATE_RUN_TIME);
    }
#endif

/*@ 0 <= prio && prio < 256 by local */
#if OS_ARG_CHK_EN > 0u
    if (prio > OS_LOWEST_PRIO) {             /* Make sure priority is within allowable range           */
        return (OS_ERR_PRIO_INVALID);
    }
#endif
/*@ task_create_ext_arguments(args, task, p_arg, ptos, prio, id, pbos, stk_size, pext, opt) &&
          0 <= prio && prio < 64 &&
          task_create_runtime_call_input(args, call, initial) &&
          task_return == &OS_TaskReturn && task_create_safe(initial, task_create_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), call, mask), X) &&
          task_create_continuation_pre(environment, critical, saved_local, sg, region, args, task_return,
          lower, old_frame, upper, LitMap("?"), call, mask, initial)
    which implies
          task_create_runtime_call_input(args, call, initial) &&
          task_create_ext_arguments(args, task, p_arg, ptos, prio, id, pbos, stk_size, pext, opt) &&
          task == createEntry(args) && p_arg == createArgument(args) && ptos == createStackTop(args) &&
          prio == createPriority(args) && task_create_options(args) == opt && task_return == &OS_TaskReturn &&
          0 <= prio && prio < 64 && task_create_stack_entry(sg, args, LitMap("?"), call, initial) &&
          task_create_stack_buffer_domain(region, args, task_return, lower, old_frame, upper) &&
          task_create_safe(initial, task_create_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), call, mask), X) &&
          task_tcb_init_continuation_save_input(environment, critical, saved_local, sg, call, mask, initial) *
          task_stack_storage(region, task_create_stack_old_image(lower, old_frame, upper)) * unmap_table_rep(sg)
*/    OS_ENTER_CRITICAL();/*@ Assert exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
          task_create_ext_arguments(args, task, p_arg, ptos, prio, id, pbos, stk_size, pext, opt) &&
          task_create_ext_clear_binding(region, args, task_create_stack_old_image(lower, old_frame, upper), prefix, middle, suffix) &&
          after_lower == task_create_ext_after_lower(args, lower, old_frame, upper, prefix, middle, suffix) &&
          after_frame == task_create_ext_after_frame(args, lower, old_frame, upper, prefix, middle, suffix) &&
          after_upper == task_create_ext_after_upper(args, lower, old_frame, upper, prefix, middle, suffix) &&
          task == createEntry(args) && p_arg == createArgument(args) && ptos == createStackTop(args) &&
          prio == createPriority(args) && task_create_options(args) == opt && task_return == &OS_TaskReturn &&
          0 <= prio && prio < 64 &&
          0 <= prio && prio < 64 &&
          task_create_stack_entry(sg, args, LitMap("?"), call, acquired) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_create_default_name_binding(LitMap("?"), acquired) &&
          task_create_runtime_call_input(args, current_call, acquired) &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) &&
          kernel_sched_ready_clients(critical) && kernel_tcb_stack_field_layout(sg) &&
          task_create_stack_buffer_domain(region, args, task_return, lower, old_frame, upper) &&
          task_create_safe(acquired, task_create_acquired_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), call, current_call, mask), X) &&
          task_create_ext_phase_frame(initial, acquired) &&
          task_tcb_init_continuation_restore_input(environment, critical, saved_local, sg, current_call, cpu_sr, acquired, acquired) *
          task_stack_storage(region, task_create_stack_old_image(lower, old_frame, upper)) * unmap_table_rep(sg) * GlobalStrings_missing(LitMap, literals) *
          undef_data_at(&psp, OS_STK *) * undef_data_at(&err, INT8U)
*//*@ exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
          task_create_stack_entry(sg, args, LitMap("?"), call, acquired) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_create_default_name_binding(LitMap("?"), acquired) &&
          task_create_runtime_call_input(args, current_call, acquired) &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) &&
          task_create_safe(acquired, task_create_acquired_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), call, current_call, mask), X) &&
          task_create_ext_phase_frame(initial, acquired) &&
          task_tcb_init_continuation_restore_input(environment, critical, saved_local, sg, current_call, cpu_sr, acquired, acquired)
    which implies exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
          task_create_stack_entry(sg, args, LitMap("?"), call, acquired) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_create_default_name_binding(LitMap("?"), acquired) &&
          task_create_runtime_call_input(args, current_call, acquired) &&
          task_stack_live_coverage(TskState(acquired), task_stack_call_active_key(current_call)) &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) &&
          task_create_safe(acquired, task_create_acquired_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), call, current_call, mask), X) &&
          task_create_ext_phase_frame(initial, acquired) &&
          critical_region_masked(task_stack_call_platform(environment), critical, sg,
            os_sched_call_invocation(current_call), os_sched_call_origin(current_call), cpu_sr, acquired) *
          task_tcb_init_stack_context(environment, current_call) * task_tcb_init_continuation_capsules(environment, saved_local, acquired) *
          data_at(&OSIntNesting, INT8U, task_create_stack_nesting(acquired)) *
          task_create_stack_without_nesting(sg, acquired)
*/
    if (OSIntNesting > 0u) {                 /* Make sure we don't create the task from within an ISR  */
/*@ exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && task_create_stack_entry(sg, args, LitMap("?"), call, acquired) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_create_default_name_binding(LitMap("?"), acquired) &&
          task_create_runtime_call_input(args, current_call, acquired) &&
          task_stack_live_coverage(TskState(acquired), task_stack_call_active_key(current_call)) &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) &&
          task_create_safe(acquired, task_create_acquired_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), call, current_call, mask), X) &&
          task_create_ext_phase_frame(initial, acquired) &&
          task_create_stack_nesting(acquired) > 0 &&
          critical_region_masked(task_stack_call_platform(environment), critical, sg,
            os_sched_call_invocation(current_call), os_sched_call_origin(current_call), cpu_sr, acquired) *
          task_tcb_init_stack_context(environment, current_call) * task_tcb_init_continuation_capsules(environment, saved_local, acquired) * data_at(&OSIntNesting, INT8U, task_create_stack_nesting(acquired)) *
          task_create_stack_without_nesting(sg, acquired)
    which implies exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && task_create_stack_entry(sg, args, LitMap("?"), call, acquired) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_create_default_name_binding(LitMap("?"), acquired) &&
          task_create_runtime_call_input(args, current_call, acquired) &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) &&
          task_create_safe(acquired, task_create_restore_return_program(environment, critical, sg, current_call, 60), X) &&
          task_create_ext_phase_frame(initial, acquired) &&
          task_tcb_init_continuation_restore_input(environment, critical, saved_local, sg, current_call, cpu_sr, acquired, acquired)
*/        OS_EXIT_CRITICAL();
        return (OS_ERR_TASK_CREATE_ISR);
    }
/*@ exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && task_create_stack_entry(sg, args, LitMap("?"), call, acquired) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_create_default_name_binding(LitMap("?"), acquired) &&
          task_create_runtime_call_input(args, current_call, acquired) &&
          task_create_stack_nesting(acquired) <= 0 &&
          task_stack_live_coverage(TskState(acquired), task_stack_call_active_key(current_call)) &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) &&
          task_create_safe(acquired, task_create_acquired_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), call, current_call, mask), X) &&
          task_create_ext_phase_frame(initial, acquired) &&
          critical_region_masked(task_stack_call_platform(environment), critical, sg,
            os_sched_call_invocation(current_call), os_sched_call_origin(current_call), cpu_sr, acquired) *
          task_tcb_init_stack_context(environment, current_call) * task_tcb_init_continuation_capsules(environment, saved_local, acquired) * data_at(&OSIntNesting, INT8U, task_create_stack_nesting(acquired)) *
          task_create_stack_without_nesting(sg, acquired)
    which implies exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && task_create_stack_entry(sg, args, LitMap("?"), call, acquired) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_create_default_name_binding(LitMap("?"), acquired) &&
          task_create_runtime_call_input(args, current_call, acquired) &&
          task_create_stack_nesting(acquired) == 0 &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) &&
          task_create_safe(acquired, task_create_acquired_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), call, current_call, mask), X) &&
          task_create_ext_phase_frame(initial, acquired) &&
          task_tcb_init_continuation_restore_input(environment, critical, saved_local, sg, current_call, cpu_sr, acquired, acquired)
*//*@ exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && task_create_stack_entry(sg, args, LitMap("?"), call, acquired) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_create_default_name_binding(LitMap("?"), acquired) &&
          task_create_runtime_call_input(args, current_call, acquired) &&
          task_create_stack_nesting(acquired) == 0 &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) && prio == createPriority(args) && 0 <= prio && prio < 64 &&
          task_create_safe(acquired, task_create_acquired_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), call, current_call, mask), X) &&
          task_create_ext_phase_frame(initial, acquired) &&
          task_tcb_init_continuation_restore_input(environment, critical, saved_local, sg, current_call, cpu_sr, acquired, acquired)
    which implies exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && task_create_stack_entry(sg, args, LitMap("?"), call, acquired) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_create_default_name_binding(LitMap("?"), acquired) &&
          task_create_runtime_call_input(args, current_call, acquired) &&
          task_create_stack_nesting(acquired) == 0 &&
          task_stack_live_coverage(TskState(acquired), task_stack_call_active_key(current_call)) &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) && prio == createPriority(args) && 0 <= prio && prio < 64 &&
          task_create_safe(acquired, task_create_acquired_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), call, current_call, mask), X) &&
          task_create_ext_phase_frame(initial, acquired) &&
          critical_region_masked(task_stack_call_platform(environment), critical, sg,
            os_sched_call_invocation(current_call), os_sched_call_origin(current_call), cpu_sr, acquired) *
          task_tcb_init_stack_context(environment, current_call) * task_tcb_init_continuation_capsules(environment, saved_local, acquired) * data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), OS_TCB *, task_create_stack_priority(sg, args, acquired)) *
          task_create_stack_without_priority(sg, args, acquired)
*/    if (OSTCBPrioTbl[prio] == (OS_TCB *)0) { /* Make sure task doesn't already exist at this priority  */
        OSTCBPrioTbl[prio] = ((OS_TCB *)1);/* Reserve the priority to prevent others from doing ...  */
                                             /* ... the same thing until task is created.              */
/*@ exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && task_create_stack_entry(sg, args, LitMap("?"), call, acquired) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_create_default_name_binding(LitMap("?"), acquired) &&
          task_create_runtime_call_input(args, current_call, acquired) &&
          task_create_stack_nesting(acquired) == 0 &&
          task_stack_live_coverage(TskState(acquired), task_stack_call_active_key(current_call)) &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) && prio == createPriority(args) && 0 <= prio && prio < 64 &&
          task_create_stack_priority(sg, args, acquired) == 0 &&
          task_create_safe(acquired, task_create_acquired_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), call, current_call, mask), X) &&
          task_create_ext_phase_frame(initial, acquired) &&
          critical_region_masked(task_stack_call_platform(environment), critical, sg,
            os_sched_call_invocation(current_call), os_sched_call_origin(current_call), cpu_sr, acquired) *
          task_tcb_init_stack_context(environment, current_call) * task_tcb_init_continuation_capsules(environment, saved_local, acquired) * data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), OS_TCB *, 1) *
          task_create_stack_without_priority(sg, args, acquired)
    which implies exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          prio == createPriority(args) &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, task_tcb_init_stack_call_args(args, LitMap("?")),
            os_sched_call_invocation(call), os_sched_call_origin(call), task_create_stack_reserved(args, call, acquired)) &&
          task_tcb_init_stack_source_preserved(call, initial, task_create_stack_reserved(args, call, acquired)) &&
          task_create_default_name_binding(LitMap("?"), task_create_stack_reserved(args, call, acquired)) &&
          task_create_runtime_call_input(args, current_call, task_create_stack_reserved(args, call, acquired)) &&
          task_create_stack_nesting(task_create_stack_reserved(args, call, acquired)) == 0 &&
          task_create_safe(task_create_stack_reserved(args, call, acquired), task_create_reserved_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), current_call, mask), X) &&
          task_create_ext_phase_frame(initial, task_create_stack_reserved(args, call, acquired)) &&
          task_tcb_init_continuation_restore_input(environment, critical, saved_local, sg, current_call, cpu_sr, acquired,
            task_create_stack_reserved(args, call, acquired))
*/        OS_EXIT_CRITICAL();
/*@ exists
          (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          task_create_ext_arguments(args, task, p_arg, ptos, prio, id, pbos, stk_size, pext, opt) &&
          task_create_ext_clear_binding(region, args, task_create_stack_old_image(lower, old_frame, upper), prefix, middle, suffix) &&
          after_lower == task_create_ext_after_lower(args, lower, old_frame, upper, prefix, middle, suffix) &&
          after_frame == task_create_ext_after_frame(args, lower, old_frame, upper, prefix, middle, suffix) &&
          after_upper == task_create_ext_after_upper(args, lower, old_frame, upper, prefix, middle, suffix) &&
          task_return == &OS_TaskReturn &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, task_tcb_init_stack_call_args(args, LitMap("?")),
            os_sched_call_invocation(call), os_sched_call_origin(call), task_create_stack_reserved(args, call, acquired)) &&
          task_tcb_init_stack_source_preserved(call, initial, task_create_stack_reserved(args, call, acquired)) &&
          task_create_default_name_binding(LitMap("?"), task_create_stack_reserved(args, call, acquired)) &&
          task_create_runtime_call_input(args, current_call, task_create_stack_reserved(args, call, acquired)) &&
          task_create_stack_nesting(task_create_stack_reserved(args, call, acquired)) == 0 &&
          task_create_stack_buffer_domain(region, args, task_return, lower, old_frame, upper) &&
          task_create_safe(task_create_stack_reserved(args, call, acquired), task_create_reserved_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), current_call, mask), X) &&
          task_create_ext_phase_frame(initial, task_create_stack_reserved(args, call, acquired)) &&
          task_tcb_init_modular_restore_output(environment, critical, saved_local, sg, current_call, cpu_sr,
            task_create_stack_reserved(args, call, acquired)) *
          task_stack_storage(region, task_create_stack_old_image(lower, old_frame, upper))
    which implies exists (stack_call : OsSchedCallContext) (checkpoint : UCOS2_Verify_State),
          task_return == &OS_TaskReturn &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_stack_same_call(stack_call, call) &&
          task_tcb_init_entry(sg, task_tcb_init_stack_call_args(args, LitMap("?")),
            os_sched_call_invocation(call), os_sched_call_origin(call), checkpoint) &&
          task_tcb_init_stack_source_preserved(call, initial, checkpoint) &&
          task_create_default_name_binding(LitMap("?"), checkpoint) &&
          task_create_runtime_call_input(args, stack_call, checkpoint) &&
          task_create_stack_nesting(checkpoint) == 0 &&
          task_create_stack_buffer_domain(region, args, task_return, lower, old_frame, upper) &&
          task_create_ext_arguments(args, task, p_arg, ptos, prio, id, pbos, stk_size, pext, opt) &&
          0 <= stk_size && stk_size <= 4294967295 && 0 <= opt && opt <= 65535 &&
          task_create_ext_clear_binding(region, args, task_create_stack_old_image(lower, old_frame, upper), prefix, middle, suffix) &&
          after_lower == task_create_ext_after_lower(args, lower, old_frame, upper, prefix, middle, suffix) &&
          after_frame == task_create_ext_after_frame(args, lower, old_frame, upper, prefix, middle, suffix) &&
          after_upper == task_create_ext_after_upper(args, lower, old_frame, upper, prefix, middle, suffix) &&
          task_create_safe(checkpoint, task_create_initialize_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), stack_call, mask), X) &&
          task_create_ext_phase_frame(initial, checkpoint) &&
          task_tcb_init_continuation_save_input(environment, critical, saved_local, sg, stack_call, mask, checkpoint) *
          task_stk_clr_pre(pbos, stk_size, opt, middle) *
          task_create_ext_clear_frame(region, args, task_create_stack_old_image(lower, old_frame, upper), prefix, middle, suffix)
*/
#if (OS_TASK_STAT_STK_CHK_EN > 0u)
        OS_TaskStkClr(pbos, stk_size, opt)/*@ where initial = middle,
          R = task_create_ext_clear_frame(region, args, task_create_stack_old_image(lower, old_frame, upper), prefix, middle, suffix) */; /* Clear the task stack (if needed) */
#endif

/*@ exists (stack_call : OsSchedCallContext) (checkpoint : UCOS2_Verify_State),
          task_return == &OS_TaskReturn &&
          task_tcb_init_stack_same_call(stack_call, call) &&
          task_tcb_init_entry(sg, task_tcb_init_stack_call_args(args, LitMap("?")),
            os_sched_call_invocation(call), os_sched_call_origin(call), checkpoint) &&
          task_tcb_init_stack_source_preserved(call, initial, checkpoint) &&
          task_create_default_name_binding(LitMap("?"), checkpoint) &&
          task_create_runtime_call_input(args, stack_call, checkpoint) &&
          task_create_stack_nesting(checkpoint) == 0 &&
          task_create_ext_arguments(args, task, p_arg, ptos, prio, id, pbos, stk_size, pext, opt) &&
          task_create_ext_clear_binding(region, args, task_create_stack_old_image(lower, old_frame, upper), prefix, middle, suffix) &&
          after_lower == task_create_ext_after_lower(args, lower, old_frame, upper, prefix, middle, suffix) &&
          after_frame == task_create_ext_after_frame(args, lower, old_frame, upper, prefix, middle, suffix) &&
          after_upper == task_create_ext_after_upper(args, lower, old_frame, upper, prefix, middle, suffix) &&
          task_create_stack_buffer_domain(region, args, task_return, lower, old_frame, upper) &&
          task_create_safe(checkpoint, task_create_initialize_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), stack_call, mask), X) &&
          task_create_ext_phase_frame(initial, checkpoint) &&
          task_stk_clr_post(pbos, stk_size, opt, middle) *
          task_create_ext_clear_frame(region, args, task_create_stack_old_image(lower, old_frame, upper), prefix, middle, suffix) *
          task_tcb_init_continuation_save_input(environment, critical, saved_local, sg, stack_call, mask, checkpoint)
    which implies exists (stack_call : OsSchedCallContext) (checkpoint : UCOS2_Verify_State),
          task_return == &OS_TaskReturn &&
          task_tcb_init_stack_same_call(stack_call, call) &&
          task_tcb_init_entry(sg, task_tcb_init_stack_call_args(args, LitMap("?")),
            os_sched_call_invocation(call), os_sched_call_origin(call), checkpoint) &&
          task_tcb_init_stack_source_preserved(call, initial, checkpoint) &&
          task_create_default_name_binding(LitMap("?"), checkpoint) &&
          task_create_runtime_call_input(args, stack_call, checkpoint) &&
          task_create_stack_nesting(checkpoint) == 0 &&
          task_create_ext_arguments(args, task, p_arg, ptos, prio, id, pbos, stk_size, pext, opt) &&
          task_create_ext_clear_binding(region, args, task_create_stack_old_image(lower, old_frame, upper), prefix, middle, suffix) &&
          after_lower == task_create_ext_after_lower(args, lower, old_frame, upper, prefix, middle, suffix) &&
          after_frame == task_create_ext_after_frame(args, lower, old_frame, upper, prefix, middle, suffix) &&
          after_upper == task_create_ext_after_upper(args, lower, old_frame, upper, prefix, middle, suffix) &&
          task_create_stack_buffer_domain(region, args, task_return, after_lower, after_frame, after_upper) &&
          task_create_safe(checkpoint, task_create_initialize_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), stack_call, mask), X) &&
          task_create_ext_phase_frame(initial, checkpoint) &&
          task_create_continuation_init_input(environment, critical, saved_local, sg, region, args, &OS_TaskReturn,
            after_lower, after_frame, after_upper, stack_call, mask, checkpoint)
*/        psp = OSTaskStkInit(task, p_arg, ptos, opt);           /* Initialize the task's stack          */
/*@ exists
          (stack_call : OsSchedCallContext) (checkpoint : UCOS2_Verify_State),
          kernel_sched_ready_clients(critical) &&
          task_return == &OS_TaskReturn &&
          task_tcb_init_stack_same_call(stack_call, call) &&
          task_tcb_init_entry(sg, task_tcb_init_stack_call_args(args, LitMap("?")),
            os_sched_call_invocation(call), os_sched_call_origin(call), checkpoint) &&
          task_tcb_init_stack_source_preserved(call, initial, checkpoint) &&
          task_create_default_name_binding(LitMap("?"), checkpoint) &&
          task_create_runtime_call_input(args, stack_call, checkpoint) &&
          task_create_stack_nesting(checkpoint) == 0 &&
          task_create_stack_buffer_domain(region, args, task_return, after_lower, after_frame, after_upper) &&
          task_create_ext_arguments(args, task, p_arg, ptos, prio, id, pbos, stk_size, pext, opt) &&
          task_create_safe(checkpoint, task_create_initialize_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), stack_call, mask), X) &&
          task_create_ext_phase_frame(initial, checkpoint) &&
          task_create_modular_init_phase_output(environment, critical, saved_local, sg, region, args, &OS_TaskReturn,
            after_lower, after_upper, stack_call, mask, checkpoint, psp)
    which implies exists (tcb_call : OsSchedCallContext) (tcb_initial : UCOS2_Verify_State),
          kernel_sched_ready_clients(critical) &&
          task_create_ext_arguments(args, task, p_arg, ptos, prio, id, pbos, stk_size, pext, opt) &&
          task_tcb_init_stack_same_call(tcb_call, call) &&
          task_tcb_init_entry(sg, task_tcb_init_stack_call_args(args, LitMap("?")),
            os_sched_call_invocation(call), os_sched_call_origin(call), tcb_initial) &&
          task_tcb_init_stack_source_preserved(call, initial, tcb_initial) &&
          task_create_default_name_binding(LitMap("?"), tcb_initial) &&
          UCOS2_state_inv(sg, tcb_initial) &&
          task_create_runtime_call_input(args, tcb_call, tcb_initial) &&
          task_create_stack_nesting(tcb_initial) == 0 &&
          task_tcb_init_arguments(task_tcb_init_stack_call_args(args, LitMap("?")),
            prio, psp, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          task_create_safe(tcb_initial, task_create_initialized_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), tcb_call, mask), X) &&
          task_create_ext_phase_frame(initial, tcb_initial) &&
          task_tcb_init_continuation_call_pre(environment, critical, saved_local, sg, region, args, task_return,
            after_lower, after_upper, LitMap("?"), os_sched_call_invocation(call), os_sched_call_origin(call),
            mask, tcb_initial, tcb_call)
*/        err = OS_TCBInit(prio, psp, pbos, id, stk_size, pext, opt)/*@ where LitMap = LitMap, literals = literals */;
        if (err == OS_ERR_NONE) {
            OS_TRACE_TASK_CREATE(OSTCBPrioTbl[prio]);
/*@ exists
          (tcb_call : OsSchedCallContext) (tcb_initial : UCOS2_Verify_State),
          task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
          createPriority(args) <= 63 &&
          task_tcb_init_stack_same_call(tcb_call, call) && err <= 0 &&
          task_tcb_init_stack_source_preserved(call, initial, tcb_initial) &&
          task_create_default_name_binding(LitMap("?"), tcb_initial) &&
          UCOS2_state_inv(sg, tcb_initial) &&
          task_create_runtime_call_input(args, tcb_call, tcb_initial) &&
          task_create_stack_nesting(tcb_initial) == 0 &&
          task_create_safe(tcb_initial, task_create_initialized_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), tcb_call, mask), X) &&
          task_create_ext_phase_frame(initial, tcb_initial) &&
          task_return == &OS_TaskReturn &&
          task_tcb_init_modular_phase_call_post(environment, critical, saved_local, sg, region, args, &OS_TaskReturn,
            after_lower, after_upper, LitMap("?"), os_sched_call_invocation(call), os_sched_call_origin(call),
            mask, tcb_initial, tcb_call, err)
    which implies exists (returned : OsSchedCallContext) (current : UCOS2_Verify_State),
          task_tcb_init_stack_same_call(returned, call) && UCOS2_state_inv(sg, current) && err == 0 &&
          task_tcb_init_stack_source_preserved(call, initial, current) &&
          task_create_default_name_binding(LitMap("?"), current) &&
          task_create_runtime_call_input(args, returned, current) &&
          task_create_stack_nesting(current) == 0 &&
          createPriority(args) <= 63 && kernel_sched_ready_inv(sg, current) &&
          task_create_safe(current, task_create_tcb_return_program(environment, critical, sg, args, returned, mask, 0), X) &&
          task_create_ext_phase_frame(initial, current) &&
          data_at(&OSRunning, INT8U, task_create_stack_running(current)) *
          task_create_continuation_without_running(environment, critical, saved_local, sg, returned, mask, current)
*/            if (OSRunning == OS_TRUE) {                        /* Find HPT if multitasking has started */
/*@ exists
          (returned : OsSchedCallContext) (current : UCOS2_Verify_State),
          task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
          task_tcb_init_stack_same_call(returned, call) && UCOS2_state_inv(sg, current) &&
          task_tcb_init_stack_source_preserved(call, initial, current) &&
          task_create_default_name_binding(LitMap("?"), current) &&
          task_create_runtime_call_input(args, returned, current) &&
          task_create_stack_nesting(current) == 0 &&
          createPriority(args) <= 63 && kernel_sched_ready_inv(sg, current) &&
          kernel_tcb_stack_field_layout(sg) && task_create_stack_running(current) == 1 &&
          kernel_sched_ready_clients(critical) &&
          task_create_safe(current, task_create_tcb_return_program(environment, critical, sg, args, returned, mask, 0), X) &&
          task_create_ext_phase_frame(initial, current) &&
          data_at(&OSRunning, INT8U, task_create_stack_running(current)) *
          task_create_continuation_without_running(environment, critical, saved_local, sg, returned, mask, current) *
          unmap_table_rep(sg)
    which implies exists (returned : OsSchedCallContext) (current : UCOS2_Verify_State),
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
          createPriority(args) <= 63 &&
          kernel_sched_ready_clients(critical) &&
          task_tcb_init_stack_same_call(returned, call) &&
          task_tcb_init_stack_source_preserved(call, initial, current) &&
          task_create_default_name_binding(LitMap("?"), current) &&
          task_create_safe(current, task_create_schedule_program(environment, critical, sg, returned, mask), X) &&
          task_create_ext_phase_frame(initial, current) &&
          task_create_ext_initial_running(initial) &&
          os_sched_continuation_call_pre(environment, saved_local, kernel_program_inv, sg, returned, mask, current)
*/                OS_Sched()/*@ where critical = critical */;/*@ exists
          (returned : OsSchedCallContext) (current : UCOS2_Verify_State),
          createPriority(args) <= 63 &&
          task_tcb_init_stack_same_call(returned, call) &&
          task_create_safe(current, task_create_schedule_program(environment, critical, sg, returned, mask), X) &&
          task_create_ext_initial_running(initial) &&
          os_sched_continuation_history_return_post(environment, critical, saved_local, kernel_program_inv, sg, returned, mask, current)
    which implies
          createPriority(args) <= 63 &&
          task_create_ext_initial_running(initial) &&
          task_create_schedule_post(environment, critical, saved_local, sg, call, mask, X)
*/
            }
        } else {
/*@ exists
          (tcb_call : OsSchedCallContext) (tcb_initial : UCOS2_Verify_State),
          task_return == &OS_TaskReturn &&
          task_tcb_init_stack_same_call(tcb_call, call) && err != 0 &&
          task_tcb_init_entry(sg, task_tcb_init_stack_call_args(args, LitMap("?")),
            os_sched_call_invocation(call), os_sched_call_origin(call), tcb_initial) &&
          task_tcb_init_stack_source_preserved(call, initial, tcb_initial) &&
          task_create_default_name_binding(LitMap("?"), tcb_initial) &&
          UCOS2_state_inv(sg, tcb_initial) &&
          task_create_safe(tcb_initial, task_create_initialized_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), tcb_call, mask), X) &&
          task_create_ext_phase_frame(initial, tcb_initial) &&
          task_tcb_init_modular_phase_call_post(environment, critical, saved_local, sg, region, args, &OS_TaskReturn,
            after_lower, after_upper, LitMap("?"), os_sched_call_invocation(call), os_sched_call_origin(call),
            mask, tcb_initial, tcb_call, err)
    which implies exists (tcb_initial released checkpoint : UCOS2_Verify_State)
          (checkpoint_call : OsSchedCallContext),
          err == 66 && task_tcb_init_stack_same_call(checkpoint_call, call) &&
          task_create_safe(checkpoint, task_create_rollback_program(environment, critical, sg, args, checkpoint_call, mask), X) &&
          task_create_ext_phase_frame(initial, checkpoint) &&
          task_create_stack_no_free_history(critical, sg, args, LitMap("?"), call, tcb_initial, released, checkpoint) *
          task_tcb_init_continuation_save_input(environment, critical, saved_local, sg, checkpoint_call, mask, checkpoint) *
          task_stack_storage(region, task_create_stack_image(TaskStackNoVFP, args, task_return, after_lower, after_upper))
*/            OS_ENTER_CRITICAL();
/*@ exists
          (tcb_initial released checkpoint : UCOS2_Verify_State) (checkpoint_call : OsSchedCallContext),
          task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
          task_tcb_init_stack_same_call(checkpoint_call, call) && prio == createPriority(args) &&
          task_create_safe(checkpoint, task_create_rollback_program(environment, critical, sg, args, checkpoint_call, mask), X) &&
          task_create_ext_phase_frame(initial, checkpoint) &&
          task_create_stack_no_free_history(critical, sg, args, LitMap("?"), call, tcb_initial, released, checkpoint) *
          task_tcb_init_modular_save_output(environment, critical, saved_local, sg, checkpoint_call, mask, cpu_sr, checkpoint)
    which implies exists (tcb_initial released acquired : UCOS2_Verify_State)
          (current_call : OsSchedCallContext),
          task_stack_live_coverage(TskState(acquired), task_stack_call_active_key(current_call)) &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) &&
          prio == createPriority(args) &&
          task_create_safe(acquired, task_create_rollback_acquired_program(environment, critical, sg, args, current_call), X) &&
          task_create_ext_phase_frame(initial, acquired) &&
          task_create_stack_no_free_history(critical, sg, args, LitMap("?"), call, tcb_initial, released, acquired) *
          critical_region_masked(task_stack_call_platform(environment), critical, sg,
            os_sched_call_invocation(current_call), os_sched_call_origin(current_call), cpu_sr, acquired) *
          task_tcb_init_stack_context(environment, current_call) * task_tcb_init_continuation_capsules(environment, saved_local, acquired) * data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), OS_TCB *, task_create_stack_priority(sg, args, acquired)) *
          task_create_stack_without_priority(sg, args, acquired)
*/
            OSTCBPrioTbl[prio] = (OS_TCB *)0;                  /* Make this priority avail. to others  */
/*@ exists
          (tcb_initial released acquired : UCOS2_Verify_State) (current_call : OsSchedCallContext),
          task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
          task_stack_live_coverage(TskState(acquired), task_stack_call_active_key(current_call)) &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) &&
          prio == createPriority(args) &&
          task_create_safe(acquired, task_create_rollback_acquired_program(environment, critical, sg, args, current_call), X) &&
          task_create_ext_phase_frame(initial, acquired) &&
          task_create_stack_no_free_history(critical, sg, args, LitMap("?"), call, tcb_initial, released, acquired) *
          critical_region_masked(task_stack_call_platform(environment), critical, sg,
            os_sched_call_invocation(current_call), os_sched_call_origin(current_call), cpu_sr, acquired) *
          task_tcb_init_stack_context(environment, current_call) * task_tcb_init_continuation_capsules(environment, saved_local, acquired) *
          data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), OS_TCB *, 0) *
          task_create_stack_without_priority(sg, args, acquired)
    which implies exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          prio == createPriority(args) &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) &&
          task_create_safe(task_create_stack_rolled_back(args, acquired), task_create_restore_return_program(environment, critical, sg, current_call, 66), X) &&
          task_create_ext_phase_frame(initial, task_create_stack_rolled_back(args, acquired)) &&
          task_tcb_init_continuation_restore_input(environment, critical, saved_local, sg, current_call, cpu_sr,
            acquired, task_create_stack_rolled_back(args, acquired))
*/            OS_EXIT_CRITICAL();
        }
        return (err);
    }
/*@ exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && task_create_stack_entry(sg, args, LitMap("?"), call, acquired) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_create_default_name_binding(LitMap("?"), acquired) &&
          task_stack_live_coverage(TskState(acquired), task_stack_call_active_key(current_call)) &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) && prio == createPriority(args) && 0 <= prio && prio < 64 &&
          task_create_safe(acquired, task_create_acquired_program(environment, critical, sg, region, args, task_return, after_lower, after_upper, LitMap("?"), call, current_call, mask), X) &&
          task_create_ext_phase_frame(initial, acquired) &&
          task_create_stack_nesting(acquired) == 0 && task_create_stack_priority(sg, args, acquired) != 0 &&
          critical_region_masked(task_stack_call_platform(environment), critical, sg,
            os_sched_call_invocation(current_call), os_sched_call_origin(current_call), cpu_sr, acquired) *
          task_tcb_init_stack_context(environment, current_call) * task_tcb_init_continuation_capsules(environment, saved_local, acquired) * data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), OS_TCB *, task_create_stack_priority(sg, args, acquired)) *
          task_create_stack_without_priority(sg, args, acquired)
    which implies exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl,
            &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && task_create_stack_entry(sg, args, LitMap("?"), call, acquired) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_create_default_name_binding(LitMap("?"), acquired) &&
          task_tcb_init_stack_same_call(current_call, call) && interrupt_saved_value(mask, cpu_sr) && prio == createPriority(args) && 0 <= prio && prio < 64 &&
          task_create_safe(acquired, task_create_restore_return_program(environment, critical, sg, current_call, 40), X) &&
          task_create_ext_phase_frame(initial, acquired) &&
          task_tcb_init_continuation_restore_input(environment, critical, saved_local, sg, current_call, cpu_sr, acquired, acquired)
*/    OS_EXIT_CRITICAL();
    return (OS_ERR_PRIO_EXIST);
}
