/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

static  void  OSTmr_InitTask (void)
/*@ phase_spec
    With (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
         (saved_local : Armv7aContinuation -> Assertion) (sg : StableGlobVars)
         (entry base task_return mask : Z) (lower old_frame upper : list (option Z))
         (call : OsSchedCallContext) (initial : UCOS2_Verify_State)
         (LitMap : String -> Z) (literals : list String) (X : unit -> UCOS2_Verify_State -> Prop)
    Require entry == &OSTmr_Task && base == OSTmrTaskStk && task_return == &OS_TaskReturn &&
      task_create_stack_global_addresses(sg, &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
      task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
      os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
        &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
      coq_prop(task_name_set_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
      coq_prop(task_name_set_layout(sg)) && kernel_sched_ready_clients(critical) && kernel_tcb_stack_field_layout(sg) &&
      task_create_runtime_call_input(tmr_init_task_create_args(entry, base), call, initial) &&
      tmr_init_task_stopped(initial) &&
      tmr_init_task_safe(environment, critical, sg, entry, base, task_return, lower, old_frame, upper, call, mask, LitMap, initial, X) &&
      tmr_init_task_entry(environment, critical, saved_local, sg, entry, base, task_return, lower, old_frame, upper,
        call, mask, LitMap, literals, initial)
    Ensure tmr_init_task_phase_post(environment, critical, saved_local, sg, entry, base, task_return, lower, old_frame, upper,
      call, mask, LitMap, literals, initial, X)
*/
{
#if OS_TASK_NAME_EN > 0u
    INT8U  err;
#endif

/*@ tmr_init_task_stopped(initial) &&
    tmr_init_task_safe(environment, critical, sg, entry, base, task_return, lower, old_frame, upper, call, mask, LitMap, initial, X) &&
    tmr_init_task_entry(environment, critical, saved_local, sg, entry, base, task_return, lower, old_frame, upper,
      call, mask, LitMap, literals, initial)
    which implies
    tmr_init_task_stopped(initial) && 0 < base && base + 512 <= 4294967295 &&
    task_create_ext_clear_binding(tmr_init_task_stack_region(base), tmr_init_task_create_args(entry, base),
      task_create_stack_old_image(lower, old_frame, upper), tmr_init_task_empty_stack, task_create_stack_old_image(lower, old_frame, upper), tmr_init_task_empty_stack) &&
    task_create_safe(initial, tmr_init_task_create_program(environment, critical, sg, entry, base, task_return,
      lower, old_frame, upper, call, mask, LitMap),
      tmr_init_task_create_postcondition(environment, critical, sg, entry, base, task_return, lower, old_frame, upper, call, mask, LitMap, initial, X)) &&
    task_create_name_api_pre(environment, critical, saved_local, sg, tmr_init_task_stack_region(base),
      tmr_init_task_create_args(entry, base), task_return, lower, old_frame, upper, call, mask, initial, LitMap, literals)
*/

#if OS_TASK_CREATE_EXT_EN > 0u
    #if OS_STK_GROWTH == 1u
    (void)OSTaskCreateExt(OSTmr_Task,
                          (void *)0,                                       /* No arguments passed to OSTmrTask()      */
                          &OSTmrTaskStk[OS_TASK_TMR_STK_SIZE - 1u],        /* Set Top-Of-Stack                        */
                          OS_TASK_TMR_PRIO,
                          OS_TASK_TMR_ID,
                          &OSTmrTaskStk[0],                                /* Set Bottom-Of-Stack                     */
                          OS_TASK_TMR_STK_SIZE,
                          (void *)0,                                       /* No TCB extension                        */
                          OS_TASK_OPT_STK_CHK | OS_TASK_OPT_STK_CLR)
    /*@ where environment=environment, saved_local=saved_local, critical=critical, sg=sg,
      args=tmr_init_task_create_args(entry, base), region=tmr_init_task_stack_region(base), task_return=task_return,
      lower=lower, old_frame=old_frame, upper=upper, prefix=tmr_init_task_empty_stack,
      middle=task_create_stack_old_image(lower, old_frame, upper), suffix=tmr_init_task_empty_stack,
      after_lower=tmr_init_task_after_lower(entry, base, lower, old_frame, upper),
      after_frame=task_create_ext_after_frame(tmr_init_task_create_args(entry, base), lower, old_frame, upper,
        tmr_init_task_empty_stack, task_create_stack_old_image(lower, old_frame, upper), tmr_init_task_empty_stack),
      after_upper=tmr_init_task_after_upper(entry, base, lower, old_frame, upper), call=call, mask=mask,
      initial=initial, LitMap=LitMap, literals=literals,
      X=tmr_init_task_create_postcondition(environment, critical, sg, entry, base, task_return, lower, old_frame, upper,
        call, mask, LitMap, initial, X) */;      /* Enable stack checking + clear stack     */
    #else
    (void)OSTaskCreateExt(OSTmr_Task,
                          (void *)0,                                       /* No arguments passed to OSTmrTask()      */
                          &OSTmrTaskStk[0],                                /* Set Top-Of-Stack                        */
                          OS_TASK_TMR_PRIO,
                          OS_TASK_TMR_ID,
                          &OSTmrTaskStk[OS_TASK_TMR_STK_SIZE - 1u],        /* Set Bottom-Of-Stack                     */
                          OS_TASK_TMR_STK_SIZE,
                          (void *)0,                                       /* No TCB extension                        */
                          OS_TASK_OPT_STK_CHK | OS_TASK_OPT_STK_CLR);      /* Enable stack checking + clear stack     */
    #endif
#else
    #if OS_STK_GROWTH == 1u
    (void)OSTaskCreate(OSTmr_Task,
                       (void *)0,
                       &OSTmrTaskStk[OS_TASK_TMR_STK_SIZE - 1u],
                       OS_TASK_TMR_PRIO);
    #else
    (void)OSTaskCreate(OSTmr_Task,
                       (void *)0,
                       &OSTmrTaskStk[0],
                       OS_TASK_TMR_PRIO);
    #endif
#endif

#if OS_TASK_NAME_EN > 0u
/*@ tmr_init_task_stopped(initial) && exists (create_error : Z),
    task_create_ext_boot_phase_post(environment, critical, saved_local, sg, tmr_init_task_stack_region(base),
      tmr_init_task_create_args(entry, base), task_return, lower, old_frame, upper, tmr_init_task_empty_stack,
      task_create_stack_old_image(lower, old_frame, upper), tmr_init_task_empty_stack, call, mask, initial, create_error,
      tmr_init_task_create_postcondition(environment, critical, sg, entry, base, task_return, lower, old_frame, upper,
        call, mask, LitMap, initial, X)) * GlobalStrings_missing(LitMap, literals)
    which implies exists (returned : OsSchedCallContext) (middle : UCOS2_Verify_State) (create_error : Z) (receipt : option (prod Z nat)),
    coq_prop(tmr_init_task_phase_created(environment, critical, sg, entry, base, task_return, lower, old_frame, upper,
      call, mask, LitMap, initial, X, returned, middle, create_error, receipt)) &&
    coq_prop(UCOS2_state_inv(sg, middle)) &&
    coq_prop(task_name_set_admission(critical, sg, os_sched_call_invocation(returned), 61, LitMap("uC/OS-II Tmr"), middle)) &&
    coq_prop(task_name_set_safe(critical, sg, os_sched_call_invocation(returned), 61, LitMap("uC/OS-II Tmr"), middle,
      tmr_init_task_name_continuation(X))) &&
    store_stringLit(LitMap("uC/OS-II Tmr"), "uC/OS-II Tmr") *
    tmr_init_task_name_call_residual(task_stack_call_platform(environment), critical, sg, os_sched_call_invocation(returned),
      os_sched_call_origin(returned), mask, middle, LitMap("uC/OS-II Tmr")) *
    tmr_init_task_create_residual(environment, saved_local, sg, entry, base, task_return, lower, old_frame, upper,
      returned, middle, create_error) * GlobalStrings_missing(LitMap, literals)
*/
/*@ Given returned middle create_error receipt */
    OSTaskNameSet(OS_TASK_TMR_PRIO, (INT8U *)(void *)"uC/OS-II Tmr", &err)
    /*@ where(borrowed_literal_spec) platform=task_stack_call_platform(environment), critical=critical, sg=sg, before=middle,
      invocation=os_sched_call_invocation(returned), origin=os_sched_call_origin(returned), mask=mask,
      request=61, name=LitMap("uC/OS-II Tmr"), error_addr=&err, X=tmr_init_task_name_continuation(X) */;
#endif
}
