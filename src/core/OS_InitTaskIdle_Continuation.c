/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

static  void  OS_InitTaskIdle (void)
/*@
    With (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
         (saved_local : Armv7aContinuation -> Assertion) (sg : StableGlobVars)
         (entry base task_return mask : Z) (lower old_frame upper : list (option Z))
         (call : OsSchedCallContext) (initial : UCOS2_Verify_State)
         (LitMap : String -> Z) (literals : list String) (X : OsSchedCallContext -> UCOS2_Verify_State -> Prop)
    Require entry == &OS_TaskIdle && base == OSTaskIdleStk && task_return == &OS_TaskReturn &&
      task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
      task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
      os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
        &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
      coq_prop(task_name_set_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
      coq_prop(task_name_set_layout(sg)) && kernel_sched_ready_clients(critical) && kernel_tcb_stack_field_layout(sg) &&
      task_create_runtime_call_input(init_task_idle_create_args(entry, base), call, initial) &&
      init_task_idle_stopped(initial) &&
      init_task_idle_continuation_safe(environment, critical, sg, entry, base, task_return, lower, old_frame, upper, call, mask, LitMap, initial, X) &&
      init_task_idle_entry(environment, critical, saved_local, sg, entry, base, task_return, lower, old_frame, upper,
        call, mask, LitMap, literals, initial)
    Ensure init_task_idle_continuation_post(environment, critical, saved_local, sg, entry, base, task_return, lower, old_frame, upper,
      call, mask, LitMap, literals, initial, X)
*/
{
#if OS_TASK_NAME_EN > 0u
    INT8U  err;
#endif

/*@ init_task_idle_stopped(initial) &&
    init_task_idle_continuation_safe(environment, critical, sg, entry, base, task_return, lower, old_frame, upper, call, mask, LitMap, initial, X) &&
    init_task_idle_entry(environment, critical, saved_local, sg, entry, base, task_return, lower, old_frame, upper,
      call, mask, LitMap, literals, initial)
    which implies
    init_task_idle_stopped(initial) && 0 < base && base + 512 <= 4294967295 &&
    task_create_ext_clear_binding(init_task_idle_stack_region(base), init_task_idle_create_args(entry, base),
      task_create_stack_old_image(lower, old_frame, upper), init_task_idle_empty_stack, task_create_stack_old_image(lower, old_frame, upper), init_task_idle_empty_stack) &&
    task_create_ext_continuation_safe(initial, init_task_idle_continuation_create_program(environment, critical, sg, entry, base, task_return,
      lower, old_frame, upper, call, mask, LitMap),
      init_task_idle_continuation_create_postcondition(environment, critical, sg, entry, base, task_return, lower, old_frame, upper, call, mask, LitMap, initial, X)) &&
    task_create_name_api_pre(environment, critical, saved_local, sg, init_task_idle_stack_region(base),
      init_task_idle_create_args(entry, base), task_return, lower, old_frame, upper, call, mask, initial, LitMap, literals)
*/

#if OS_TASK_CREATE_EXT_EN > 0u
    #if OS_STK_GROWTH == 1u
    (void)OSTaskCreateExt(OS_TaskIdle,
                          (void *)0,                                 /* No arguments passed to OS_TaskIdle() */
                          &OSTaskIdleStk[OS_TASK_IDLE_STK_SIZE - 1u],/* Set Top-Of-Stack                     */
                          OS_TASK_IDLE_PRIO,                         /* Lowest priority level                */
                          OS_TASK_IDLE_ID,
                          &OSTaskIdleStk[0],                         /* Set Bottom-Of-Stack                  */
                          OS_TASK_IDLE_STK_SIZE,
                          (void *)0,                                 /* No TCB extension                     */
                          OS_TASK_OPT_STK_CHK | OS_TASK_OPT_STK_CLR)
    /*@ where environment=environment, saved_local=saved_local, critical=critical, sg=sg,
      args=init_task_idle_create_args(entry, base), region=init_task_idle_stack_region(base), task_return=task_return,
      lower=lower, old_frame=old_frame, upper=upper, prefix=init_task_idle_empty_stack,
      middle=task_create_stack_old_image(lower, old_frame, upper), suffix=init_task_idle_empty_stack,
      after_lower=init_task_idle_after_lower(entry, base, lower, old_frame, upper),
      after_frame=task_create_ext_after_frame(init_task_idle_create_args(entry, base), lower, old_frame, upper,
        init_task_idle_empty_stack, task_create_stack_old_image(lower, old_frame, upper), init_task_idle_empty_stack),
      after_upper=init_task_idle_after_upper(entry, base, lower, old_frame, upper), call=call, mask=mask,
      initial=initial, LitMap=LitMap, literals=literals,
      X=init_task_idle_continuation_create_postcondition(environment, critical, sg, entry, base, task_return, lower, old_frame, upper,
        call, mask, LitMap, initial, X) */;/* Enable stack checking + clear stack  */
    #else
    (void)OSTaskCreateExt(OS_TaskIdle,
                          (void *)0,                                 /* No arguments passed to OS_TaskIdle() */
                          &OSTaskIdleStk[0],                         /* Set Top-Of-Stack                     */
                          OS_TASK_IDLE_PRIO,                         /* Lowest priority level                */
                          OS_TASK_IDLE_ID,
                          &OSTaskIdleStk[OS_TASK_IDLE_STK_SIZE - 1u],/* Set Bottom-Of-Stack                  */
                          OS_TASK_IDLE_STK_SIZE,
                          (void *)0,                                 /* No TCB extension                     */
                          OS_TASK_OPT_STK_CHK | OS_TASK_OPT_STK_CLR);/* Enable stack checking + clear stack  */
    #endif
#else
    #if OS_STK_GROWTH == 1u
    (void)OSTaskCreate(OS_TaskIdle,
                       (void *)0,
                       &OSTaskIdleStk[OS_TASK_IDLE_STK_SIZE - 1u],
                       OS_TASK_IDLE_PRIO);
    #else
    (void)OSTaskCreate(OS_TaskIdle,
                       (void *)0,
                       &OSTaskIdleStk[0],
                       OS_TASK_IDLE_PRIO);
    #endif
#endif

#if OS_TASK_NAME_EN > 0u
/*@ init_task_idle_stopped(initial) && exists (create_error : Z),
    task_create_ext_continuation_boot_phase_post(environment, critical, saved_local, sg, init_task_idle_stack_region(base),
      init_task_idle_create_args(entry, base), task_return, lower, old_frame, upper, init_task_idle_empty_stack,
      task_create_stack_old_image(lower, old_frame, upper), init_task_idle_empty_stack, call, mask, initial, create_error,
      init_task_idle_continuation_create_postcondition(environment, critical, sg, entry, base, task_return, lower, old_frame, upper,
        call, mask, LitMap, initial, X)) * GlobalStrings_missing(LitMap, literals)
    which implies exists (returned : OsSchedCallContext) (middle : UCOS2_Verify_State) (create_error : Z),
    coq_prop(init_task_idle_continuation_created(environment, critical, sg, entry, base, task_return, lower, old_frame, upper,
      call, mask, LitMap, initial, X, returned, middle, create_error)) &&
    coq_prop(init_task_idle_continuation_phase_frame(initial, middle)) &&
    coq_prop(UCOS2_state_inv(sg, middle)) &&
    coq_prop(task_name_set_continuation_call_binding(environment, returned, task_stack_call_platform(environment),
      os_sched_call_invocation(returned), os_sched_call_origin(returned))) &&
    coq_prop(task_name_set_continuation_admission(sg, returned, 63, LitMap("uC/OS-II Idle"), middle)) &&
    coq_prop(task_name_set_continuation_call_safe(environment, critical, sg, returned, mask, 63, LitMap("uC/OS-II Idle"), middle,
      init_task_idle_continuation_name_postcondition(X))) &&
    store_stringLit(LitMap("uC/OS-II Idle"), "uC/OS-II Idle") *
    init_task_idle_continuation_literal_residual(environment, critical, saved_local, sg, returned, mask, middle, LitMap("uC/OS-II Idle")) *
    init_task_idle_continuation_failure_buffer(entry, base, task_return, lower, old_frame, upper, create_error) *
    GlobalStrings_missing(LitMap, literals)
*/
/*@ Given returned middle create_error */
    OSTaskNameSet(OS_TASK_IDLE_PRIO, (INT8U *)(void *)"uC/OS-II Idle", &err)
    /*@ where(borrowed_literal_spec) environment=environment, saved_local=saved_local,
      platform=task_stack_call_platform(environment), critical=critical, sg=sg, before=middle, call=returned,
      invocation=os_sched_call_invocation(returned), origin=os_sched_call_origin(returned), mask=mask,
      request=63, name=LitMap("uC/OS-II Idle"), error_addr=&err, X=init_task_idle_continuation_name_postcondition(X) */;
#endif
}
