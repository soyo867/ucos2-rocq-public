/* Fields-owner annotation candidate with the authorized signal lifetime.
 * Executable tokens match task-fields-static-input-candidate/OSTmr_Task.c.
 * Application callbacks use the source-backed fields contract and actual
 * continuation-prefix registry. Kernel callee obligations stay separate.
 */
static  void  OSTmr_Task (void *p_arg)
/*@ With {Application} (AppRep : Application -> Assertion)
         (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
         (sg : StableGlobVars)
         (callback : prod (prod Z Z) Z -> OsSchedCallContext -> program (tmr_task_scan_world Application) OsSchedCallContext)
         (initial_context : OsSchedCallContext) (initial : tmr_task_scan_world Application)
         (mask argument : Z)
         (X : prod (list TmrTaskIterationObservation) OsSchedCallContext -> tmr_task_scan_world Application -> Prop)
    Require p_arg == argument && tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(initial_context), tmr_task_kernel(initial)) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
             tmr_create_c_bindings(sg) && tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        valid_timer_state(sg, tmr_task_timers(initial)) && timer_api_initialized(tmr_task_timers(initial)) &&
        tmr_task_fields_iteration_entry(critical, sg, initial_context, tmr_task_kernel(initial)) &&
        tmr_task_client_loop_safe(environment, critical, sg, mask, tmr_task_framed_effects(callback),
            initial_context, nil, initial, X) &&
        tmr_task_fields_base_owned(AppRep, environment, sg, mask, initial_context, initial) *
        tmr_task_client_status_callback_capabilities(AppRep, environment, critical, sg, callback,
            mask, initial_context, initial) * tmr_task_call_residual
    Ensure exists (final_context : OsSchedCallContext) (final : tmr_task_scan_world Application)
                  (completed : list TmrTaskIterationObservation),
        tmr_task_client_outer_facts(environment, critical, sg, mask, tmr_task_framed_effects(callback),
            initial_context, initial, final_context, completed, final, X) &&
        tmr_task_fields_base_owned(AppRep, environment, sg, mask, final_context, final) *
        tmr_task_client_status_callback_capabilities(AppRep, environment, critical, sg, callback,
            mask, initial_context, initial) * tmr_task_call_residual */
{
    INT8U            err;
    OS_TMR          *ptmr;
    OS_TMR          *ptmr_next;
    OS_TMR_CALLBACK  pfnct;
    OS_TMR_WHEEL    *pspoke;
    INT16U           spoke;

    /*@ tmr_task_fields_iteration_entry(critical, sg, initial_context, tmr_task_kernel(initial)) &&
        tmr_task_fields_base_owned(AppRep, environment, sg, mask, initial_context, initial) *
        undef_data_at(&err, unsigned char)
            which implies
            tmr_task_client_status_iteration_entry(critical, sg, initial_context, tmr_task_kernel(initial)) &&
            tmr_task_client_clear_status_pend_entry(sg, initial_context, tmr_task_kernel(initial)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, initial_context, initial) */
    p_arg = p_arg;
    /*@ Inv Assert exists (context : OsSchedCallContext) (world : tmr_task_scan_world Application)
        (completed : list TmrTaskIterationObservation), tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(context), tmr_task_kernel(world)) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
             tmr_create_c_bindings(sg) && tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        valid_timer_state(sg, tmr_task_timers(world)) && timer_api_initialized(tmr_task_timers(world)) &&
        tmr_task_client_status_iteration_entry(critical, sg, context, tmr_task_kernel(world)) &&
        tmr_task_client_outer_facts(environment, critical, sg, mask, tmr_task_framed_effects(callback),
            initial_context, initial, context, completed, world, X) && tmr_task_client_clear_status_pend_entry(sg, context, tmr_task_kernel(world)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, context, world) * data_at(&p_arg, void *, argument) * undef_data_at(&ptmr, OS_TMR *) *
            undef_data_at(&ptmr_next, OS_TMR *) * undef_data_at(&pfnct, OS_TMR_CALLBACK) *
            undef_data_at(&pspoke, OS_TMR_WHEEL *) * undef_data_at(&spoke, unsigned short) * tmr_task_client_status_callback_capabilities(AppRep, environment, critical, sg, callback,
            mask, initial_context, initial) * tmr_task_call_residual */
    for (;;) {
        /*@ Given context world completed */
        /* The actual next-Pend entry permits suspension and retains clear
         * pending status. The ordered physical guard is checked separately;
         * no old observed-admission relation is required. */
        /*@ Assert exists (eid : EventID) (observed : OSEventAbstractState),
            tmr_task_client_clear_status_pend_entry(sg, context, tmr_task_kernel(world)) &&
            tmr_task_client_clear_status_pend_domain(critical, sg, context,
                timerSignalSem(tmr_task_timers(world)), tmr_task_kernel(world), eid, observed) &&
            sem_pend_call_input(critical, sg, os_sched_call_invocation(context),
                timerSignalSem(tmr_task_timers(world)), tmr_task_kernel(world), eid, observed) &&
            tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(context), tmr_task_kernel(world)) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
             tmr_create_c_bindings(sg) && tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        valid_timer_state(sg, tmr_task_timers(world)) && timer_api_initialized(tmr_task_timers(world)) &&
        tmr_task_client_outer_facts(environment, critical, sg, mask, tmr_task_framed_effects(callback),
            initial_context, initial, context, completed, world, X) && tmr_task_client_clear_status_pend_entry(sg, context, tmr_task_kernel(world)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, context, world) * data_at(&p_arg, void *, argument) * undef_data_at(&ptmr, OS_TMR *) *
            undef_data_at(&ptmr_next, OS_TMR *) * undef_data_at(&pfnct, OS_TMR_CALLBACK) *
            undef_data_at(&pspoke, OS_TMR_WHEEL *) * undef_data_at(&spoke, unsigned short) * tmr_task_client_status_callback_capabilities(AppRep, environment, critical, sg, callback,
            mask, initial_context, initial) * tmr_task_call_residual */
        /*@ Given eid observed */
        /*@ tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(context), tmr_task_kernel(world)) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
            
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(world)) &&
            tmr_task_client_clear_status_pend_domain(critical, sg, context, timerSignalSem(tmr_task_timers(world)), tmr_task_kernel(world), eid, observed) &&
            tmr_task_client_clear_status_pend_entry(sg, context, tmr_task_kernel(world)) &&
            tmr_task_client_clear_status_pend_entry(sg, context, tmr_task_kernel(world)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, context, world)
            which implies
            UCOS2_state_inv(sg, tmr_task_kernel(world)) &&
            tmr_task_client_clear_status_pend_entry(sg, context, tmr_task_kernel(world)) &&
            tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(context), tmr_task_kernel(world)) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
            
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(world)) &&
            tmr_task_client_clear_status_pend_domain(critical, sg, context, timerSignalSem(tmr_task_timers(world)), tmr_task_kernel(world), eid, observed) &&
            tmr_task_client_clear_status_pend_entry(sg, context, tmr_task_kernel(world)) &&
            tmr_task_client_pend_address_guard(sg, tmr_task_kernel(world),
                timerSignalSem(tmr_task_timers(world)), eid,
                &((OS_EVENT *)timerSignalSem(tmr_task_timers(world)))->OSEventType,
                &((OS_EVENT *)timerSignalSem(tmr_task_timers(world)))->OSEventCnt,
                &OSIntNesting, &OSLockNesting, &OSTCBCur, &OSRdyGrp, &OSRdyTbl) &&
            os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
                &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            exists (pend_local : Armv7aContinuation -> TmrTaskLegacyAssertion),
            data_at(&OSTmrSemSignal, OS_EVENT *, timerSignalSem(tmr_task_timers(world))) *
            tmr_task_client_clear_status_pend_argument_rest(environment, pend_local, critical, sg, context, mask,
                timerSignalSem(tmr_task_timers(world)), 0, &err, tmr_task_kernel(world), eid, observed,
                tmr_task_legacy_any, &OSTmrSemSignal) * AppRep(tmr_task_application(world)) */
        /*@ Given pend_local */
        OSSemPend(OSTmrSemSignal, 0u, &err)
        /*@ where(timer_task_client_pend_spec) environment=environment, local=pend_local, critical=critical,
            sg=sg, context=context, mask=mask, pe=timerSignalSem(tmr_task_timers(world)), ticks=0,
            pd=&err, signal_address=&OSTmrSemSignal, before=tmr_task_kernel(world),
            eid=eid, observed=observed, Xk=tmr_task_legacy_any */;
        /* Exact error, same-call relation, actual returned local and the
         * SemPend separated pure carrier are consumed; its heap is residual. */
        /*@ Assert exists (wait_context : OsSchedCallContext) (waited : tmr_task_scan_world Application)
            (wait_local : Armv7aContinuation -> TmrTaskLegacyAssertion) (wait_error : Z),
            tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(wait_context), tmr_task_kernel(waited)) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
             tmr_create_c_bindings(sg) && tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(world)) &&
            tmr_task_client_outer_facts(environment, critical, sg, mask, tmr_task_framed_effects(callback),
            initial_context, initial, context, completed, world, X) &&
            tmr_task_client_pend_program(environment, critical, sg, tmr_task_framed_effects(callback),
                context, timerSignalSem(tmr_task_timers(world)), world, pair(wait_error, wait_context), waited) &&
            tmr_task_client_clear_status_pend_entry(sg, wait_context, tmr_task_kernel(waited)) &&
            tmr_task_fields_owned(AppRep, environment, sg, mask, &err, wait_local, wait_context, waited) * data_at(&p_arg, void *, argument) * undef_data_at(&ptmr, OS_TMR *) *
            undef_data_at(&ptmr_next, OS_TMR *) * undef_data_at(&pfnct, OS_TMR_CALLBACK) *
            undef_data_at(&pspoke, OS_TMR_WHEEL *) * undef_data_at(&spoke, unsigned short) * tmr_task_client_status_callback_capabilities(AppRep, environment, critical, sg, callback,
            mask, initial_context, initial) * tmr_task_call_residual */
        /*@ Given wait_context waited wait_local wait_error */
        /*@ tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(wait_context), tmr_task_kernel(waited)) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(world)) &&
            tmr_task_client_clear_status_pend_entry(sg, wait_context, tmr_task_kernel(waited)) &&
            tmr_task_fields_owned(AppRep, environment, sg, mask, &err, wait_local, wait_context, waited)
            which implies
            UCOS2_state_inv(sg, tmr_task_kernel(waited)) &&
            tmr_task_client_clear_status_pend_entry(sg, wait_context, tmr_task_kernel(waited)) &&
            tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(wait_context), tmr_task_kernel(waited)) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(world)) &&
            os_sched_lock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting) &&
            tmr_task_fields_lock_pre(environment, critical, wait_local, sg, wait_context, mask,
                tmr_task_kernel(waited), tmr_task_fields_kernel_any) *
            tmr_task_fields_client(AppRep, &err, waited) */
        OSSchedLock()
        /*@ where(timer_task_lock_fields_spec) environment=environment, local=wait_local, critical=critical,
            sg=sg, context=wait_context, mask=mask, before=tmr_task_kernel(waited), Xk=tmr_task_fields_kernel_any */;
        /* HISTORY: locked context is the actual Lock result, independent
         * of wait_context. Build the source history from both real calls. */
        /*@ Assert exists (history : TmrTaskContinuationHistory Application),
            tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(tmr_task_continuation_lock_context(history)), tmr_task_kernel(tmr_task_continuation_locked(history))) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
             tmr_create_c_bindings(sg) && tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && tmr_task_client_outer_facts(environment, critical, sg, mask, tmr_task_framed_effects(callback),
            initial_context, initial, context, completed, world, X) &&
            tmr_task_continuation_before(history) == world &&
            tmr_task_continuation_context(history) == context &&
            tmr_task_continuation_completed(history) == completed &&
            tmr_task_continuation_error(history) == wait_error &&
            tmr_task_continuation_waited(history) == waited &&
            tmr_task_continuation_wait_context(history) == wait_context &&
            tmr_task_client_history(environment, critical, sg, mask, tmr_task_framed_effects(callback),
            initial_context, initial, history) &&
            os_sched_lock_fields_return_sources(environment, critical, sg, wait_context, mask,
                tmr_task_kernel(waited), tmr_task_continuation_lock_context(history), tmr_task_kernel(tmr_task_continuation_locked(history))) &&
            timer_api_initialized(tmr_task_timers(tmr_task_continuation_locked(history))) &&
            tmr_task_client_clear_status_pend_entry(sg, tmr_task_continuation_lock_context(history), tmr_task_kernel(tmr_task_continuation_locked(history))) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, tmr_task_continuation_lock_context(history), tmr_task_continuation_locked(history)) * data_at(&p_arg, void *, argument) * undef_data_at(&ptmr, OS_TMR *) *
            undef_data_at(&ptmr_next, OS_TMR *) * undef_data_at(&pfnct, OS_TMR_CALLBACK) *
            undef_data_at(&pspoke, OS_TMR_WHEEL *) * undef_data_at(&spoke, unsigned short) * tmr_task_client_status_callback_capabilities(AppRep, environment, critical, sg, callback,
            mask, initial_context, initial) * tmr_task_call_residual */
        /*@ Given history */
        /*@ tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(tmr_task_continuation_locked(history))) &&
            tmr_task_client_clear_status_pend_entry(sg, tmr_task_continuation_lock_context(history), tmr_task_kernel(tmr_task_continuation_locked(history))) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, tmr_task_continuation_lock_context(history), tmr_task_continuation_locked(history))
            which implies
            tmr_task_client_clear_status_pend_entry(sg, tmr_task_continuation_lock_context(history), tmr_task_kernel(tmr_task_continuation_locked(history))) &&
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(tmr_task_continuation_locked(history))) &&
            data_at(&OSTmrTime, unsigned int, timerTime(tmr_task_timers(tmr_task_continuation_locked(history)))) *
            tmr_task_fields_time_rest(AppRep, environment, sg, mask, &err, tmr_task_continuation_lock_context(history), tmr_task_continuation_locked(history)) */
        OSTmrTime++;
        /* The physical residual stays indexed by locked, while the one
         * updated cell contains the real unsigned increment. */
        /*@ tmr_task_client_clear_status_pend_entry(sg, tmr_task_continuation_lock_context(history), tmr_task_kernel(tmr_task_continuation_locked(history))) &&
             tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(tmr_task_continuation_lock_context(history)), tmr_task_kernel(tmr_task_continuation_locked(history))) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(tmr_task_continuation_locked(history))) &&
            data_at(&OSTmrTime, unsigned int, timerTime(tmr_task_timers(tmr_task_continuation_start(history)))) *
            tmr_task_fields_time_rest(AppRep, environment, sg, mask, &err, tmr_task_continuation_lock_context(history), tmr_task_continuation_locked(history))
            which implies
            tmr_task_client_clear_status_pend_entry(sg, tmr_task_continuation_lock_context(history), tmr_task_kernel(tmr_task_continuation_start(history))) &&
            tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(tmr_task_continuation_lock_context(history)), tmr_task_kernel(tmr_task_continuation_start(history))) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(tmr_task_continuation_locked(history))) &&
            data_at(&OSTmrTime, unsigned int, timerTime(tmr_task_timers(tmr_task_continuation_start(history)))) *
            tmr_task_fields_time_rest(AppRep, environment, sg, mask, &err, tmr_task_continuation_lock_context(history), tmr_task_continuation_start(history)) */
        spoke  = (INT16U)(OSTmrTime % OS_TMR_CFG_WHEEL_SIZE);
        /*@ tmr_task_client_clear_status_pend_entry(sg, tmr_task_continuation_lock_context(history), tmr_task_kernel(tmr_task_continuation_start(history))) &&
             tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(tmr_task_continuation_start(history))) &&
            data_at(&OSTmrTime, unsigned int, timerTime(tmr_task_timers(tmr_task_continuation_start(history)))) *
            tmr_task_fields_time_rest(AppRep, environment, sg, mask, &err, tmr_task_continuation_lock_context(history), tmr_task_continuation_start(history))
            which implies
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(tmr_task_continuation_start(history))) &&
            tmr_task_client_clear_status_pend_entry(sg, tmr_task_continuation_lock_context(history), tmr_task_kernel(tmr_task_continuation_start(history))) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, tmr_task_continuation_lock_context(history), tmr_task_continuation_start(history)) */
        /*@ Assert tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(tmr_task_continuation_lock_context(history)), tmr_task_kernel(tmr_task_continuation_start(history))) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
             tmr_create_c_bindings(sg) && tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && tmr_task_client_scan_facts(environment, critical, sg, mask, tmr_task_framed_effects(callback),
            initial_context, initial, history, nil, tmr_task_continuation_lock_context(history), tmr_task_continuation_start(history), tmr_task_continuation_scan(sg, history), X) &&
            tmr_task_client_clear_status_pend_entry(sg, tmr_task_continuation_lock_context(history), tmr_task_kernel(tmr_task_continuation_start(history))) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, tmr_task_continuation_lock_context(history), tmr_task_continuation_start(history)) * data_at(&p_arg, void *, argument) *
            undef_data_at(&ptmr, OS_TMR *) * undef_data_at(&ptmr_next, OS_TMR *) *
            undef_data_at(&pfnct, OS_TMR_CALLBACK) * undef_data_at(&pspoke, OS_TMR_WHEEL *) *
            data_at(&spoke, unsigned short, Z_of_nat(tmr_task_continuation_spoke(sg, history))) * tmr_task_client_status_callback_capabilities(AppRep, environment, critical, sg, callback,
            mask, initial_context, initial) * tmr_task_call_residual */
        pspoke = &OSTmrWheelTbl[spoke];
        /*@ tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(tmr_task_continuation_start(history))) &&
            tmr_task_spoke_in_range(sg, tmr_task_continuation_spoke(sg, history)) &&
            tmr_task_client_clear_status_pend_entry(sg, tmr_task_continuation_lock_context(history), tmr_task_kernel(tmr_task_continuation_start(history))) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, tmr_task_continuation_lock_context(history), tmr_task_continuation_start(history))
            which implies
            tmr_task_client_clear_status_pend_entry(sg, tmr_task_continuation_lock_context(history), tmr_task_kernel(tmr_task_continuation_start(history))) &&
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(tmr_task_continuation_start(history))) &&
            tmr_task_spoke_in_range(sg, tmr_task_continuation_spoke(sg, history)) &&
            data_at(field_addr(pointer_offset(&OSTmrWheelTbl, Z_of_nat(tmr_task_continuation_spoke(sg, history)), struct os_tmr_wheel), OS_TMR_WHEEL, OSTmrFirst), OS_TMR *, tmr_task_head(sg, tmr_task_continuation_spoke(sg, history), tmr_task_timers(tmr_task_continuation_start(history)))) * tmr_task_fields_head_rest(AppRep, environment, sg, mask, &err, tmr_task_continuation_lock_context(history), tmr_task_continuation_start(history), tmr_task_continuation_spoke(sg, history)) */
        ptmr   = pspoke->OSTmrFirst;
        /*@ tmr_task_client_clear_status_pend_entry(sg, tmr_task_continuation_lock_context(history), tmr_task_kernel(tmr_task_continuation_start(history))) &&
             tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(tmr_task_continuation_start(history))) &&
            tmr_task_spoke_in_range(sg, tmr_task_continuation_spoke(sg, history)) &&
            data_at(field_addr(pointer_offset(&OSTmrWheelTbl, Z_of_nat(tmr_task_continuation_spoke(sg, history)), struct os_tmr_wheel), OS_TMR_WHEEL, OSTmrFirst), OS_TMR *, tmr_task_head(sg, tmr_task_continuation_spoke(sg, history), tmr_task_timers(tmr_task_continuation_start(history)))) * tmr_task_fields_head_rest(AppRep, environment, sg, mask, &err, tmr_task_continuation_lock_context(history), tmr_task_continuation_start(history), tmr_task_continuation_spoke(sg, history))
            which implies
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(tmr_task_continuation_start(history))) &&
            tmr_task_spoke_in_range(sg, tmr_task_continuation_spoke(sg, history)) &&
            tmr_task_client_clear_status_pend_entry(sg, tmr_task_continuation_lock_context(history), tmr_task_kernel(tmr_task_continuation_start(history))) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, tmr_task_continuation_lock_context(history), tmr_task_continuation_start(history)) */
        /*@ Inv Assert exists (visited : list tmr_task_scan_event) (scan_context : OsSchedCallContext)
            (scan_world : tmr_task_scan_world Application) (cursor : TimerScanState),
            tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(scan_world)) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
             tmr_create_c_bindings(sg) && tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && tmr_task_client_scan_facts(environment, critical, sg, mask, tmr_task_framed_effects(callback),
            initial_context, initial, history, visited, scan_context, scan_world, cursor, X) &&
        tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(scan_world)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, scan_world) * data_at(&p_arg, void *, argument) * data_at(&ptmr, OS_TMR *, timer_scan_next_pointer(sg, cursor)) *
            undef_data_at(&ptmr_next, OS_TMR *) * undef_data_at(&pfnct, OS_TMR_CALLBACK) *
            data_at(&pspoke, OS_TMR_WHEEL *, pointer_offset(&OSTmrWheelTbl, Z_of_nat(tmr_task_continuation_spoke(sg, history)), struct os_tmr_wheel)) *
            data_at(&spoke, unsigned short, Z_of_nat(tmr_task_continuation_spoke(sg, history))) * tmr_task_client_status_callback_capabilities(AppRep, environment, critical, sg, callback,
            mask, initial_context, initial) * tmr_task_call_residual */
        while (ptmr != (OS_TMR *)0) {
            /*@ Given visited scan_context scan_world cursor */
            /*@ Assert exists (index cached : Z) (tail : list Z) (future : TimerScanState) (image : TimerImage),
                tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(scan_world)) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
             tmr_create_c_bindings(sg) && tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && tmr_task_client_scan_facts(environment, critical, sg, mask, tmr_task_framed_effects(callback),
            initial_context, initial, history, visited, scan_context, scan_world, cursor, X) &&
                timerScanRemaining(cursor) == cons(index, tail) &&
                timer_scan_advance(tmr_task_timers(scan_world), cursor) == Some(future) &&
                tmr_task_fields_index_valid(sg, index) && tmr_task_fields_image_at(scan_world, index, image) &&
                tmr_unlink_running(tmr_task_timers(scan_world), index) &&
                cached == tmr_task_image_value(TaskNextField, image) && tmr_task_image_read(scan_world, index, TaskNextField, cached) &&
                tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(scan_world)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, scan_world) * data_at(&p_arg, void *, argument) * data_at(&ptmr, OS_TMR *, timer_pool_addr(sg, index)) *
            undef_data_at(&ptmr_next, OS_TMR *) * undef_data_at(&pfnct, OS_TMR_CALLBACK) *
            data_at(&pspoke, OS_TMR_WHEEL *, pointer_offset(&OSTmrWheelTbl, Z_of_nat(tmr_task_continuation_spoke(sg, history)), struct os_tmr_wheel)) *
            data_at(&spoke, unsigned short, Z_of_nat(tmr_task_continuation_spoke(sg, history))) * tmr_task_client_status_callback_capabilities(AppRep, environment, critical, sg, callback,
            mask, initial_context, initial) * tmr_task_call_residual */
            /*@ Given index cached tail future image */
            /*@ tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(scan_world)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(scan_world, index, image) &&
            cached == tmr_task_image_value(TaskNextField, image) &&
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(scan_world)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, scan_world)
            which implies
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(scan_world)) &&
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(scan_world)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(scan_world, index, image) &&
            cached == tmr_task_image_value(TaskNextField, image) &&
            data_at(&((OS_TMR *)timer_pool_addr(sg, index))->OSTmrNext, void *, cached) *
                tmr_task_fields_image_rest(AppRep, environment, sg, mask, &err, scan_context, scan_world, index, image, TaskNextField) */
            ptmr_next = (OS_TMR *)ptmr->OSTmrNext;
            /*@ tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(scan_world)) &&
             tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(scan_world)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(scan_world, index, image) &&
            cached == tmr_task_image_value(TaskNextField, image) &&
            data_at(&((OS_TMR *)timer_pool_addr(sg, index))->OSTmrNext, void *, cached) *
                tmr_task_fields_image_rest(AppRep, environment, sg, mask, &err, scan_context, scan_world, index, image, TaskNextField)
            which implies
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(scan_world)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(scan_world, index, image) &&
            cached == tmr_task_image_value(TaskNextField, image) &&
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(scan_world)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, scan_world) */
            /*@ tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(scan_world)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(scan_world, index, image) &&
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(scan_world)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, scan_world)
            which implies
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(scan_world)) &&
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(scan_world)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(scan_world, index, image) &&
            data_at(&OSTmrTime, unsigned int, timerTime(tmr_task_timers(scan_world))) *
                data_at(&((OS_TMR *)timer_pool_addr(sg, index))->OSTmrMatch, unsigned int, tmr_task_image_value(TaskMatchField, image)) * tmr_task_fields_match_rest(AppRep, environment, sg, mask, &err, scan_context, scan_world, index, image) */
            if (OSTmrTime == ptmr->OSTmrMatch) {
                /*@ tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(scan_world)) &&
             tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(scan_world)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(scan_world, index, image) &&
            data_at(&OSTmrTime, unsigned int, timerTime(tmr_task_timers(scan_world))) *
                    data_at(&((OS_TMR *)timer_pool_addr(sg, index))->OSTmrMatch, unsigned int, tmr_task_image_value(TaskMatchField, image)) * tmr_task_fields_match_rest(AppRep, environment, sg, mask, &err, scan_context, scan_world, index, image)
            which implies
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(scan_world)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(scan_world, index, image) &&
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(scan_world)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, scan_world) */
                OS_TRACE_TMR_EXPIRED(ptmr);
                /*@ tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(scan_world)) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(scan_world)) &&
            tmr_unlink_running(tmr_task_timers(scan_world), index) &&
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(scan_world)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, scan_world)
            which implies
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(scan_world)) &&
            tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(scan_world)) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(scan_world)) &&
            tmr_unlink_running(tmr_task_timers(scan_world), index) &&
            exists (raw_match raw_next previous first entries : Z)
                        (unlink_frame : TmrTaskLegacyAssertion) (unlink_local : Armv7aContinuation -> TmrTaskLegacyAssertion),
                    tmr_task_fields_unlink_pre(timer_pool_addr(sg, index), OSTmrWheelTbl, raw_match, raw_next, previous, first, entries, unlink_frame) *
                    tmr_task_fields_unlink_rest(AppRep, environment, sg, mask, &err, unlink_local, scan_context,
                        scan_world, index, raw_match, raw_next, previous, first, entries, unlink_frame) */
                /*@ Given raw_match raw_next previous first entries unlink_frame unlink_local */
                OSTmr_Unlink(ptmr)
                /*@ where(timer_task_unlink_fields_spec) p=timer_pool_addr(sg, index), base=OSTmrWheelTbl,
                    match_time=raw_match, next=raw_next, prev=previous, first=first, entries=entries, R=unlink_frame */;
                /*@ tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(scan_world)) &&
             tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(scan_world)) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(scan_world)) &&
            tmr_unlink_running(tmr_task_timers(scan_world), index) &&
            tmr_task_fields_unlink_post(timer_pool_addr(sg, index), OSTmrWheelTbl, raw_match, raw_next, previous, first, entries, unlink_frame) *
                    tmr_task_fields_unlink_rest(AppRep, environment, sg, mask, &err, unlink_local, scan_context,
                        scan_world, index, raw_match, raw_next, previous, first, entries, unlink_frame)
            which implies
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(scan_world)) &&
            tmr_unlink_running(tmr_task_timers(scan_world), index) &&
            exists (unlinked : tmr_task_scan_world Application),
                    tmr_task_unlink_world(sg, scan_world, index, unlinked) &&
                tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(unlinked)) &&
                timer_api_initialized(tmr_task_timers(unlinked)) &&
                tmr_link_eligible(tmr_task_timers(unlinked), index) &&
                tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(unlinked)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, unlinked) */
                /*@ Given unlinked */
                /*@ tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(unlinked)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_link_eligible(tmr_task_timers(unlinked), index) &&
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(unlinked)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, unlinked)
            which implies
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(unlinked)) &&
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(unlinked)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_link_eligible(tmr_task_timers(unlinked), index) &&
            exists (unlinked_image : TimerImage),
                    tmr_task_fields_image_at(unlinked, index, unlinked_image) &&
                data_at(&((OS_TMR *)timer_pool_addr(sg, index))->OSTmrOpt, unsigned char, tmr_task_image_value(TaskOptionField, unlinked_image)) *
                    tmr_task_fields_image_rest(AppRep, environment, sg, mask, &err, scan_context, unlinked, index, unlinked_image, TaskOptionField) */
                /*@ Given unlinked_image */
                if (ptmr->OSTmrOpt == OS_TMR_OPT_PERIODIC) {
                    /*@ tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(unlinked)) &&
             tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(unlinked)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(unlinked, index, unlinked_image) &&
            data_at(&((OS_TMR *)timer_pool_addr(sg, index))->OSTmrOpt, unsigned char, tmr_task_image_value(TaskOptionField, unlinked_image)) *
                        tmr_task_fields_image_rest(AppRep, environment, sg, mask, &err, scan_context, unlinked, index, unlinked_image, TaskOptionField)
            which implies
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(unlinked)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(unlinked, index, unlinked_image) &&
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(unlinked)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, unlinked) */
                    /*@ tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(unlinked)) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(unlinked)) &&
            tmr_link_eligible(tmr_task_timers(unlinked), index) &&
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(unlinked)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, unlinked)
            which implies
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(unlinked)) &&
            tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(unlinked)) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(unlinked)) &&
            tmr_link_eligible(tmr_task_timers(unlinked), index) &&
            exists (delay period link_first link_entries : Z)
                            (link_frame : TmrTaskLegacyAssertion) (link_local : Armv7aContinuation -> TmrTaskLegacyAssertion),
                        tmr_task_fields_link_pre(timer_pool_addr(sg, index), OSTmrWheelTbl, &OSTmrTime, 1,
                            timerTime(tmr_task_timers(unlinked)), delay, period, link_first, link_entries, link_frame) *
                        tmr_task_fields_link_rest(AppRep, environment, sg, mask, &err, link_local, scan_context,
                            unlinked, index, delay, period, link_first, link_entries, link_frame) */
                    /*@ Given delay period link_first link_entries link_frame link_local */
                    OSTmr_Link(ptmr, OS_TMR_LINK_PERIODIC)
                    /*@ where(timer_task_link_fields_spec) p=timer_pool_addr(sg, index), base=OSTmrWheelTbl,
                        clock=&OSTmrTime, kind=1, time=timerTime(tmr_task_timers(unlinked)), delay=delay,
                        period=period, first=link_first, entries=link_entries, R=link_frame */;
                    /*@ tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(unlinked)) &&
             tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(unlinked)) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(unlinked)) &&
            tmr_task_fields_link_post(timer_pool_addr(sg, index), OSTmrWheelTbl, &OSTmrTime, 1,
                            timerTime(tmr_task_timers(unlinked)), delay, period, link_first, link_entries, link_frame) *
                        tmr_task_fields_link_rest(AppRep, environment, sg, mask, &err, link_local, scan_context,
                            unlinked, index, delay, period, link_first, link_entries, link_frame)
            which implies
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(unlinked)) &&
            exists (linked : tmr_task_scan_world Application),
                        tmr_task_link_world(sg, unlinked, index, linked) &&
                tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(linked)) &&
                tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(linked)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, linked) */
                } else {
                    /*@ tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(unlinked)) &&
             tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(unlinked)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(unlinked, index, unlinked_image) &&
            data_at(&((OS_TMR *)timer_pool_addr(sg, index))->OSTmrOpt, unsigned char, tmr_task_image_value(TaskOptionField, unlinked_image)) *
                        tmr_task_fields_image_rest(AppRep, environment, sg, mask, &err, scan_context, unlinked, index, unlinked_image, TaskOptionField)
            which implies
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(unlinked)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(unlinked, index, unlinked_image) &&
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(unlinked)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, unlinked) */
                    /*@ tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(unlinked)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(unlinked, index, unlinked_image) &&
            tmr_link_eligible(tmr_task_timers(unlinked), index) &&
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(unlinked)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, unlinked)
            which implies
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(unlinked)) &&
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(unlinked)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(unlinked, index, unlinked_image) &&
            tmr_link_eligible(tmr_task_timers(unlinked), index) &&
            data_at(&((OS_TMR *)timer_pool_addr(sg, index))->OSTmrState, unsigned char, tmr_task_image_value(TaskStateField, unlinked_image)) *
                        tmr_task_fields_complete_rest(AppRep, environment, sg, mask, &err,
                            scan_context, unlinked, index, unlinked_image) */
                    ptmr->OSTmrState = OS_TMR_STATE_COMPLETED;
                    /*@ tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(unlinked)) &&
             tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(unlinked)) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(unlinked)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(unlinked, index, unlinked_image) &&
            tmr_link_eligible(tmr_task_timers(unlinked), index) &&
            data_at(&((OS_TMR *)timer_pool_addr(sg, index))->OSTmrState, unsigned char, 2) *
                        tmr_task_fields_complete_rest(AppRep, environment, sg, mask, &err,
                            scan_context, unlinked, index, unlinked_image)
            which implies
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(unlinked)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(unlinked, index, unlinked_image) &&
            tmr_link_eligible(tmr_task_timers(unlinked), index) &&
            exists (completed_world : tmr_task_scan_world Application),
                        tmr_task_complete_world(unlinked, index, completed_world) &&
                tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(completed_world)) &&
                tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(completed_world)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, completed_world) */
                }
                /*@ Assert exists (dispatched : tmr_task_scan_world Application) (dispatch_image : TimerImage),
                    tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(dispatched)) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
             tmr_create_c_bindings(sg) && tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && tmr_task_client_scan_facts(environment, critical, sg, mask, tmr_task_framed_effects(callback),
            initial_context, initial, history, visited, scan_context, scan_world, cursor, X) &&
                    timerScanRemaining(cursor) == cons(index, tail) &&
                    timer_scan_advance(tmr_task_timers(scan_world), cursor) == Some(future) &&
                    tmr_task_fields_index_valid(sg, index) &&
                    tmr_task_image_read(scan_world, index, TaskMatchField, timerTime(tmr_task_timers(scan_world))) &&
                    tmr_task_dispatch_prepared(sg, scan_world, index, cached, dispatched) && tmr_task_fields_image_at(dispatched, index, dispatch_image) &&
                    tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(dispatched)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, dispatched) *
                    data_at(&p_arg, void *, argument) * data_at(&ptmr, OS_TMR *, timer_pool_addr(sg, index)) *
            data_at(&ptmr_next, OS_TMR *, cached) * undef_data_at(&pfnct, OS_TMR_CALLBACK) *
            data_at(&pspoke, OS_TMR_WHEEL *, pointer_offset(&OSTmrWheelTbl, Z_of_nat(tmr_task_continuation_spoke(sg, history)), struct os_tmr_wheel)) *
            data_at(&spoke, unsigned short, Z_of_nat(tmr_task_continuation_spoke(sg, history))) * tmr_task_client_status_callback_capabilities(AppRep, environment, critical, sg, callback,
            mask, initial_context, initial) * tmr_task_call_residual */
                /*@ Given dispatched dispatch_image */
                /*@ tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(dispatched)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(dispatched, index, dispatch_image) &&
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(dispatched)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, dispatched)
            which implies
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(dispatched)) &&
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(dispatched)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(dispatched, index, dispatch_image) &&
            data_at(&((OS_TMR *)timer_pool_addr(sg, index))->OSTmrCallback, OS_TMR_CALLBACK, tmr_task_image_value(TaskCallbackField, dispatch_image)) *
                    tmr_task_fields_image_rest(AppRep, environment, sg, mask, &err, scan_context, dispatched, index, dispatch_image, TaskCallbackField) */
                pfnct = ptmr->OSTmrCallback;
                /*@ tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(dispatched)) &&
             tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(dispatched)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(dispatched, index, dispatch_image) &&
            data_at(&((OS_TMR *)timer_pool_addr(sg, index))->OSTmrCallback, OS_TMR_CALLBACK, tmr_task_image_value(TaskCallbackField, dispatch_image)) *
                    tmr_task_fields_image_rest(AppRep, environment, sg, mask, &err, scan_context, dispatched, index, dispatch_image, TaskCallbackField)
            which implies
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(dispatched)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(dispatched, index, dispatch_image) &&
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(dispatched)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, dispatched) */
                if (pfnct != (OS_TMR_CALLBACK)0) {
                    /* Select the fields capability registered for this actual
                     * source prefix. Its application-side producer requires
                     * concrete body evidence for all-frame safety, every
                     * normal outcome and the fields postcondition. */
                    /*@ Assert exists (function_pointer callback_argument callback_error_address : Z),
                        function_pointer == tmr_task_image_value(TaskCallbackField, dispatch_image) &&
                        callback_argument == tmr_task_image_value(TaskArgumentField, dispatch_image) &&
                        callback_error_address == &err && function_pointer != 0 &&
                        tmr_task_callback_dispatch_domain(sg, function_pointer, timer_pool_addr(sg, index), callback_argument, dispatched) &&
                        tmr_task_fields_scan_ready(sg, dispatched) &&
                        tmr_task_fields_index_valid(sg, index) &&
                        tmr_task_fields_image_at(dispatched, index, dispatch_image) &&
                        tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(dispatched)) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
             tmr_create_c_bindings(sg) && tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && tmr_task_client_scan_facts(environment, critical, sg, mask, tmr_task_framed_effects(callback),
            initial_context, initial, history, visited, scan_context, scan_world, cursor, X) &&
                        timerScanRemaining(cursor) == cons(index, tail) &&
                        timer_scan_advance(tmr_task_timers(scan_world), cursor) == Some(future) &&
                        tmr_task_image_read(scan_world, index, TaskMatchField, timerTime(tmr_task_timers(scan_world))) &&
                        tmr_task_dispatch_prepared(sg, scan_world, index, cached, dispatched) &&
                        tmr_task_image_read(dispatched, index, TaskCallbackField, function_pointer) &&
                        tmr_task_image_read(dispatched, index, TaskArgumentField, callback_argument) &&
                        (function_pointer |= void(void *cb_self, void *cb_arg)
                        With (call_context : OsSchedCallContext) (call_before : tmr_task_scan_world Application)
                        Require tmr_task_client_status_callback_pre(AppRep, environment, sg, mask, callback_error_address,
                            function_pointer, timer_pool_addr(sg, index), callback_argument, call_context, call_before, pair(cb_self, cb_arg))
                        Ensure tmr_task_client_status_callback_post(AppRep, environment, sg, callback, mask, callback_error_address,
                            function_pointer, timer_pool_addr(sg, index), callback_argument, call_context, call_before, pair(cb_self, cb_arg), tt)) * tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(dispatched)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, dispatched) *
                        data_at(&p_arg, void *, argument) * data_at(&ptmr, OS_TMR *, timer_pool_addr(sg, index)) *
            data_at(&ptmr_next, OS_TMR *, cached) * data_at(&pfnct, OS_TMR_CALLBACK, function_pointer) *
            data_at(&pspoke, OS_TMR_WHEEL *, pointer_offset(&OSTmrWheelTbl, Z_of_nat(tmr_task_continuation_spoke(sg, history)), struct os_tmr_wheel)) *
            data_at(&spoke, unsigned short, Z_of_nat(tmr_task_continuation_spoke(sg, history))) * tmr_task_client_status_callback_capabilities(AppRep, environment, critical, sg, callback,
            mask, initial_context, initial) * tmr_task_call_residual */
                    /*@ Given function_pointer callback_argument callback_error_address */
                    /* Only the readable argument view changes. The existing
                     * fields capability remains the source-evidence producer;
                     * HoareFun_conseq retains all source normal outcomes. */
                    /*@ (function_pointer |= void(void *cb_self, void *cb_arg)
                        With (call_context : OsSchedCallContext) (call_before : tmr_task_scan_world Application)
                        Require tmr_task_client_status_callback_pre(AppRep, environment, sg, mask, callback_error_address,
                            function_pointer, timer_pool_addr(sg, index), callback_argument, call_context, call_before, pair(cb_self, cb_arg))
                        Ensure tmr_task_client_status_callback_post(AppRep, environment, sg, callback, mask, callback_error_address,
                            function_pointer, timer_pool_addr(sg, index), callback_argument, call_context, call_before, pair(cb_self, cb_arg), tt))
                        which implies
                        (function_pointer |= void(void *cb_self, void *cb_arg)
                        With (call_context : OsSchedCallContext) (call_before : tmr_task_scan_world Application)
                        Require data_at(&((OS_TMR *)timer_pool_addr(sg, index))->OSTmrCallbackArg, void *, callback_argument) *
                            tmr_task_fields_callback_argument_rest(AppRep, environment, sg, mask, callback_error_address,
                                function_pointer, timer_pool_addr(sg, index), callback_argument, call_context, call_before,
                                pair(cb_self, cb_arg), &((OS_TMR *)timer_pool_addr(sg, index))->OSTmrCallbackArg)
                        Ensure tmr_task_client_status_callback_post(AppRep, environment, sg, callback, mask, callback_error_address,
                            function_pointer, timer_pool_addr(sg, index), callback_argument, call_context, call_before, pair(cb_self, cb_arg), tt)) */
                    /*@ tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(dispatched)) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(dispatched)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(dispatched, index, dispatch_image) &&
            callback_argument == tmr_task_image_value(TaskArgumentField, dispatch_image) &&
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(dispatched)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, dispatched)
            which implies
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(dispatched)) &&
            tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(dispatched)) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(dispatched)) &&
            tmr_task_fields_index_valid(sg, index) &&
            tmr_task_fields_image_at(dispatched, index, dispatch_image) &&
            callback_argument == tmr_task_image_value(TaskArgumentField, dispatch_image) &&
            data_at(&((OS_TMR *)timer_pool_addr(sg, index))->OSTmrCallbackArg, void *, callback_argument) *
                        tmr_task_fields_image_rest(AppRep, environment, sg, mask, &err, scan_context, dispatched, index, dispatch_image, TaskArgumentField) */
                    /* The actual image residual is consumed by the
                     * read-merge consequence. The argument cell stays exposed
                     * until C evaluates ptmr->OSTmrCallbackArg. */
                    /*@ tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(dispatched)) &&
             tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(dispatched)) && tmr_create_c_bindings(sg) &&
                        tmr_task_fields_index_valid(sg, index) &&
                        tmr_task_fields_image_at(dispatched, index, dispatch_image) &&
                        callback_argument == tmr_task_image_value(TaskArgumentField, dispatch_image) &&
                        callback_error_address == &err &&
                        tmr_task_callback_dispatch_domain(sg, function_pointer, timer_pool_addr(sg, index), callback_argument, dispatched) &&
                        tmr_task_fields_scan_ready(sg, dispatched) &&
                        tmr_task_fields_image_rest(AppRep, environment, sg, mask, &err,
                            scan_context, dispatched, index, dispatch_image, TaskArgumentField)
                        which implies
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(dispatched)) &&
                        tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(dispatched)) && tmr_create_c_bindings(sg) &&
                        tmr_task_fields_index_valid(sg, index) &&
                        tmr_task_fields_image_at(dispatched, index, dispatch_image) &&
                        callback_argument == tmr_task_image_value(TaskArgumentField, dispatch_image) &&
                        callback_error_address == &err &&
                        tmr_task_callback_dispatch_domain(sg, function_pointer, timer_pool_addr(sg, index), callback_argument, dispatched) &&
                        tmr_task_fields_scan_ready(sg, dispatched) &&
                        tmr_task_fields_callback_argument_rest(AppRep, environment, sg, mask, callback_error_address,
                            function_pointer, timer_pool_addr(sg, index), callback_argument, scan_context, dispatched,
                            pair(timer_pool_addr(sg, index), callback_argument),
                            &((OS_TMR *)timer_pool_addr(sg, index))->OSTmrCallbackArg) */
                    (*pfnct)((void *)ptmr, ptmr->OSTmrCallbackArg)
                    /*@ where call_context=scan_context, call_before=dispatched */;
                    /*@ Assert exists (callback_context : OsSchedCallContext) (callback_world : tmr_task_scan_world Application),
                        tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(callback_context), tmr_task_kernel(callback_world)) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
             tmr_create_c_bindings(sg) && tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && tmr_task_client_scan_facts(environment, critical, sg, mask, tmr_task_framed_effects(callback),
            initial_context, initial, history, visited, scan_context, scan_world, cursor, X) &&
                        timerScanRemaining(cursor) == cons(index, tail) &&
                        timer_scan_advance(tmr_task_timers(scan_world), cursor) == Some(future) &&
                        tmr_task_image_read(scan_world, index, TaskMatchField, timerTime(tmr_task_timers(scan_world))) &&
                        tmr_task_dispatch_prepared(sg, scan_world, index, cached, dispatched) &&
                        tmr_task_image_read(dispatched, index, TaskCallbackField, function_pointer) &&
                        tmr_task_image_read(dispatched, index, TaskArgumentField, callback_argument) &&
                        function_pointer != 0 &&
                        tmr_task_client_status_callback_return_facts(sg, callback, function_pointer, timer_pool_addr(sg, index),
                            callback_argument, scan_context, dispatched, callback_context, callback_world) &&
                        tmr_task_client_clear_status_pend_entry(sg, callback_context, tmr_task_kernel(callback_world)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, callback_context, callback_world) *
                        data_at(&p_arg, void *, argument) * data_at(&ptmr, OS_TMR *, timer_pool_addr(sg, index)) *
            data_at(&ptmr_next, OS_TMR *, cached) * data_at(&pfnct, OS_TMR_CALLBACK, function_pointer) *
            data_at(&pspoke, OS_TMR_WHEEL *, pointer_offset(&OSTmrWheelTbl, Z_of_nat(tmr_task_continuation_spoke(sg, history)), struct os_tmr_wheel)) *
            data_at(&spoke, unsigned short, Z_of_nat(tmr_task_continuation_spoke(sg, history))) * tmr_task_client_status_callback_capabilities(AppRep, environment, critical, sg, callback,
            mask, initial_context, initial) * tmr_task_call_residual */
                    /*@ Given callback_context callback_world */
                    /* Reload the current saved spoke. The returned owner
                     * contains its actual existential local, never old local. */
                    /*@ tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(callback_world)) &&
            tmr_task_spoke_in_range(sg, tmr_task_continuation_spoke(sg, history)) &&
            tmr_task_client_clear_status_pend_entry(sg, callback_context, tmr_task_kernel(callback_world)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, callback_context, callback_world)
            which implies
            tmr_task_client_clear_status_pend_entry(sg, callback_context, tmr_task_kernel(callback_world)) &&
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(callback_world)) &&
            tmr_task_spoke_in_range(sg, tmr_task_continuation_spoke(sg, history)) &&
            data_at(field_addr(pointer_offset(&OSTmrWheelTbl, Z_of_nat(tmr_task_continuation_spoke(sg, history)), struct os_tmr_wheel), OS_TMR_WHEEL, OSTmrFirst), OS_TMR *, tmr_task_head(sg, tmr_task_continuation_spoke(sg, history), tmr_task_timers(callback_world))) *
                        tmr_task_fields_head_rest(AppRep, environment, sg, mask, &err, callback_context, callback_world, tmr_task_continuation_spoke(sg, history)) */
                    ptmr_next = pspoke->OSTmrFirst;
                    /*@ tmr_task_client_clear_status_pend_entry(sg, callback_context, tmr_task_kernel(callback_world)) &&
             tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(callback_world)) &&
            tmr_task_spoke_in_range(sg, tmr_task_continuation_spoke(sg, history)) &&
            data_at(field_addr(pointer_offset(&OSTmrWheelTbl, Z_of_nat(tmr_task_continuation_spoke(sg, history)), struct os_tmr_wheel), OS_TMR_WHEEL, OSTmrFirst), OS_TMR *, tmr_task_head(sg, tmr_task_continuation_spoke(sg, history), tmr_task_timers(callback_world))) *
                        tmr_task_fields_head_rest(AppRep, environment, sg, mask, &err, callback_context, callback_world, tmr_task_continuation_spoke(sg, history))
            which implies
            tmr_task_profile(sg) &&
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(callback_world)) &&
            tmr_task_spoke_in_range(sg, tmr_task_continuation_spoke(sg, history)) &&
            tmr_task_client_clear_status_pend_entry(sg, callback_context, tmr_task_kernel(callback_world)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, callback_context, callback_world) */
                }
            }
            /*@ Assert exists (after_context : OsSchedCallContext) (after : tmr_task_scan_world Application)
                (next_cursor : TimerScanState) (event : tmr_task_scan_event),
                tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(after_context), tmr_task_kernel(after)) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
             tmr_create_c_bindings(sg) && tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                tmr_task_scan_step(sg, callback, tmr_task_continuation_spoke(sg, history),
                    scan_world, scan_context, cursor, event, after, after_context, next_cursor) &&
                tmr_task_client_scan_facts(environment, critical, sg, mask, tmr_task_framed_effects(callback),
            initial_context, initial, history, app(visited, cons(event, nil)), after_context, after, next_cursor, X) &&
                tmr_task_client_clear_status_pend_entry(sg, after_context, tmr_task_kernel(after)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, after_context, after) *
                data_at(&p_arg, void *, argument) * data_at(&ptmr, OS_TMR *, timer_pool_addr(sg, index)) *
            data_at(&ptmr_next, OS_TMR *, timer_scan_next_pointer(sg, next_cursor)) * undef_data_at(&pfnct, OS_TMR_CALLBACK) *
            data_at(&pspoke, OS_TMR_WHEEL *, pointer_offset(&OSTmrWheelTbl, Z_of_nat(tmr_task_continuation_spoke(sg, history)), struct os_tmr_wheel)) *
            data_at(&spoke, unsigned short, Z_of_nat(tmr_task_continuation_spoke(sg, history))) * tmr_task_client_status_callback_capabilities(AppRep, environment, critical, sg, callback,
            mask, initial_context, initial) * tmr_task_call_residual */
            /*@ Given after_context after next_cursor event */
            ptmr = ptmr_next;
        }
        /*@ Given visited scan_context scan_world cursor */
        /* UNLOCK-ENTRY: static registered-client and stack-layout facts
         * are supplied here. Actual Fresh/Scheduler admission inside the
         * callee remains the source obligation of that fields candidate. */
        /*@ tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(scan_world)) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
            
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(scan_world)) &&
            kernel_sched_ready_clients(critical) &&
            kernel_tcb_stack_field_layout(sg) &&
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(scan_world)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, scan_context, scan_world)
            which implies
            UCOS2_state_inv(sg, tmr_task_kernel(scan_world)) &&
            tmr_task_client_clear_status_pend_entry(sg, scan_context, tmr_task_kernel(scan_world)) &&
            tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(scan_context), tmr_task_kernel(scan_world)) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
            
            tmr_create_c_bindings(sg) &&
            tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            timer_api_initialized(tmr_task_timers(scan_world)) &&
            kernel_sched_ready_clients(critical) &&
            kernel_tcb_stack_field_layout(sg) &&
            os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
                &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            exists (unlock_local : Armv7aContinuation -> TmrTaskLegacyAssertion),
            tmr_task_fields_lift(tmr_task_unlock_fields_pre(environment, critical, unlock_local, sg, scan_context, mask,
                tmr_task_kernel(scan_world), tmr_task_fields_kernel_any)) *
            tmr_task_fields_client(AppRep, &err, scan_world) */
        /*@ Given unlock_local */
        OSSchedUnlock()
        /*@ where(timer_task_unlock_fields_spec) environment=environment, local=unlock_local, critical=critical,
            sg=sg, context=scan_context, mask=mask, before=tmr_task_kernel(scan_world), Xk=tmr_task_fields_kernel_any */;
        /* Open the actual checked Unlock post once, before rebuilding the
         * application world and the outer-loop continuation. */
        /*@ tmr_task_fields_lift(tmr_task_unlock_fields_entry_post(environment, critical,
                unlock_local, sg, scan_context, mask, tmr_task_kernel(scan_world), tmr_task_fields_kernel_any)) *
            tmr_task_fields_client(AppRep, &err, scan_world)
            which implies
            exists (returned : OsSchedCallContext) (unlock_kernel : UCOS2_Verify_State),
            os_sched_unlock_continuation_return_facts(environment, critical, sg, scan_context, mask,
                tmr_task_kernel(scan_world), tmr_task_fields_kernel_any, returned, unlock_kernel) &&
            os_sched_unlock_fields_return_sources(environment, critical, sg, scan_context, mask,
                tmr_task_kernel(scan_world), returned, unlock_kernel) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(returned), unlock_kernel) &&
            tmr_task_client_clear_status_pend_entry(sg, returned, unlock_kernel) &&
            tmr_task_unlock_return_branch(environment, critical, sg, scan_context, mask,
                tmr_task_kernel(scan_world), returned, unlock_kernel) &&
            tmr_task_fields_lift(os_sched_unlock_fields_return_world(environment, unlock_local,
                sg, returned, mask, unlock_kernel)) * tmr_task_fields_client(AppRep, &err, scan_world)
        */
        /*@ Given returned unlock_kernel */
        /*@ Assert exists (after : tmr_task_scan_world Application)
            (all_completed : list TmrTaskIterationObservation),
            tmr_task_kernel(after) == unlock_kernel &&
            tmr_task_continuation_unlock_program(environment, critical, sg, mask, tmr_task_framed_effects(callback),
                scan_context, scan_world, returned, after) &&
            os_sched_unlock_fields_return_sources(environment, critical, sg, scan_context, mask,
                tmr_task_kernel(scan_world), returned, tmr_task_kernel(after)) &&
            tmr_task_profile(sg) &&
            tmr_task_signal_lifetime(critical, sg, os_sched_call_invocation(returned), tmr_task_kernel(after)) &&
            event_table_layout_prop(sg) &&
            tmr_task_registered_source_coverage(task_stack_call_external(environment), critical) &&
            task_sw_hook_source_binding(task_stack_call_external(environment)) &&
            tmr_task_callback_signal_lifetime(sg, callback) &&
             tmr_create_c_bindings(sg) && tmr_task_global_addresses(sg, &OSTmrSemSignal, OSTmrWheelTbl, &OSTmrTime, &OSTCBCur,
            &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
            &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        valid_timer_state(sg, tmr_task_timers(after)) && timer_api_initialized(tmr_task_timers(after)) &&
        tmr_task_client_status_iteration_entry(critical, sg, returned, tmr_task_kernel(after)) &&
        tmr_task_client_outer_facts(environment, critical, sg, mask, tmr_task_framed_effects(callback),
            initial_context, initial, returned, all_completed, after, X) && tmr_task_client_clear_status_pend_entry(sg, returned, tmr_task_kernel(after)) &&
            tmr_task_current_fields_owned(AppRep, environment, sg, mask, &err, returned, after) * data_at(&p_arg, void *, argument) * undef_data_at(&ptmr, OS_TMR *) *
            undef_data_at(&ptmr_next, OS_TMR *) * undef_data_at(&pfnct, OS_TMR_CALLBACK) *
            undef_data_at(&pspoke, OS_TMR_WHEEL *) * undef_data_at(&spoke, unsigned short) * tmr_task_client_status_callback_capabilities(AppRep, environment, critical, sg, callback,
            mask, initial_context, initial) * tmr_task_call_residual */
        /* The preceding assertion must re-establish the actual current
         * iteration entry from this Unlock return before the back edge. */
    }
}

