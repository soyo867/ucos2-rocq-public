/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

OS_TMR  *OSTmrCreate (INT32U           dly,
                      INT32U           period,
                      INT8U            opt,
                      OS_TMR_CALLBACK  callback,
                      void            *callback_arg,
                      INT8U           *pname,
                      INT8U           *perr)
/*@ With (env : TmrCreateEnvironment) (args : TmrCreateArguments)
         (before : UCOS2_Verify_State) (perr0 : Z) (LitMap : String -> Z) X
    Require dly == tmr_create_delay(args) && period == tmr_create_period(args) &&
      opt == tmr_create_option(args) && callback == tmr_create_callback(args) &&
      callback_arg == tmr_create_callback_arg(args) && pname == tmr_create_name_argument(args) &&
      tmr_create_output_binding(perr, perr0) && tmr_create_default_name(args) == LitMap("?") &&
      tmr_create_api_pre(env, args, before, perr, X) *
      tmr_create_global_strings(env, LitMap)
    Ensure tmr_create_api_post(env, args, before, perr0, __return, X) *
      tmr_create_global_strings(env, LitMap)
*/
{
    OS_TMR   *ptmr;

    /*@ tmr_create_api_pre(env, args, before, perr, X)
        which implies
        tmr_create_entry_facts(env, args, before) &&
        safeExec(tmr_create_at_state(before), tmr_create_program(env, args), X) &&
        tmr_create_return_frame(env, tmr_create_caller(env), before) *
        tmr_create_name_storage(tmr_create_name_plan(env)) *
        undef_data_at(perr, unsigned char)
    */

#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return ((OS_TMR *)0);
    }
#endif

#ifdef OS_SAFETY_CRITICAL_IEC61508
    if (OSSafetyCriticalStartFlag == OS_TRUE) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        *perr = OS_ERR_ILLEGAL_CREATE_RUN_TIME;
        return ((OS_TMR *)0);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    switch (opt) {                                          /* Validate arguments                                     */
        case OS_TMR_OPT_PERIODIC:
             if (period == 0u) {
                 *perr = OS_ERR_TMR_INVALID_PERIOD;
                 return ((OS_TMR *)0);
             }
             break;

        case OS_TMR_OPT_ONE_SHOT:
             if (dly == 0u) {
                 *perr = OS_ERR_TMR_INVALID_DLY;
                 return ((OS_TMR *)0);
             }
             break;

        default:
             *perr = OS_ERR_TMR_INVALID_OPT;
             return ((OS_TMR *)0);
    }
#endif
    /*@ tmr_create_argument_error(tmr_create_delay(args), tmr_create_period(args),
          tmr_create_option(args)) == None by local */
    /*@ tmr_create_entry_facts(env, args, before) &&
        tmr_create_return_frame(env, tmr_create_caller(env), before)
        which implies
        tmr_create_entry_facts(env, args, before) &&
        data_at(&OSIntNesting, unsigned char, tmr_create_nesting(before)) *
        tmr_create_observation_rest(env, before)
    */
    if (OSIntNesting > 0u) {                                /* See if trying to call from an ISR                      */
        *perr  = OS_ERR_TMR_ISR;
        return ((OS_TMR *)0);
    }
    /*@ tmr_create_first_error(args, before) == None by local */
    /*@ tmr_create_entry_facts(env, args, before) &&
        data_at(&OSIntNesting, unsigned char, tmr_create_nesting(before)) *
        tmr_create_observation_rest(env, before)
        which implies
        tmr_create_entry_facts(env, args, before) &&
        os_sched_lock_global_addresses(tmr_create_globals(env), &OSRunning, &OSIntNesting, &OSLockNesting) &&
        os_sched_lock_pre(tmr_create_platform(env), tmr_create_critical(env), tmr_create_globals(env),
        os_sched_call_invocation(tmr_create_caller(env)), os_sched_call_origin(tmr_create_caller(env)),
        tmr_create_mask(env), before) *
        os_sched_context_resources(tmr_create_external(env), tmr_create_caller(env)) *
        unmap_table_rep(tmr_create_globals(env))
    */
    OSSchedLock() /*@ where platform = tmr_create_platform(env),
        critical = tmr_create_critical(env), sg = tmr_create_globals(env),
        invocation = os_sched_call_invocation(tmr_create_caller(env)),
        origin = os_sched_call_origin(tmr_create_caller(env)),
        mask = tmr_create_mask(env), before = before */;
    /*@ tmr_create_entry_facts(env, args, before) && tmr_create_first_error(args, before) == None &&
        os_sched_lock_post(tmr_create_platform(env), tmr_create_critical(env), tmr_create_globals(env),
        os_sched_call_invocation(tmr_create_caller(env)), os_sched_call_origin(tmr_create_caller(env)),
        tmr_create_mask(env), before) *
        os_sched_context_resources(tmr_create_external(env), tmr_create_caller(env)) *
        unmap_table_rep(tmr_create_globals(env))
        which implies
        exists (locked : UCOS2_Verify_State) (head : Z) (next : Z) (prev : Z)
          (used : Z) (free : Z) (alloc_frame : Assertion),
        tmr_create_locked_facts(env, args, before, locked) &&
        tmr_create_alloc_consequence(tmr_create_globals(env), tmr_create_timers(locked),
          head, next, prev, used, free, alloc_frame) &&
        tmr_alloc_low_pre(head, next, prev, used, free) * alloc_frame *
        tmr_create_kernel_frame(env, locked)
    */
    /*@ Given locked head next prev used free alloc_frame */
    ptmr = OSTmr_Alloc() /*@ where head = head, next = next, prev = prev,
        used = used, free = free, frame = alloc_frame */;
    /*@ tmr_create_alloc_consequence(tmr_create_globals(env), tmr_create_timers(locked),
          head, next, prev, used, free, alloc_frame) &&
        tmr_alloc_low_post(head, next, prev, used, free, ptmr) * alloc_frame
        which implies
        tmr_alloc_configured_result(tmr_create_globals(env), tmr_create_timers(locked), ptmr)
    */
    if (ptmr == (OS_TMR *)0) {
        /*@ tmr_create_locked_facts(env, args, before, locked) && tmr_create_pointer_null(ptmr) &&
            tmr_alloc_configured_result(tmr_create_globals(env), tmr_create_timers(locked), ptmr) *
            tmr_create_kernel_frame(env, locked)
            which implies
            tmr_create_pointer_null(ptmr) &&
            tmr_create_prefix(env, args, before, TmrCreateExhausted, locked) &&
            os_sched_unlock_global_addresses(tmr_create_globals(env), &OSRunning, &OSIntNesting,
          &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            os_sched_unlock_pre(tmr_create_external(env), tmr_create_platform(env),
          tmr_create_critical(env), tmr_create_globals(env), tmr_create_caller(env),
          tmr_create_mask(env), locked)
        */
        OSSchedUnlock() /*@ where external = tmr_create_external(env), platform = tmr_create_platform(env),
            critical = tmr_create_critical(env), sg = tmr_create_globals(env),
            context = tmr_create_caller(env), mask = tmr_create_mask(env), before = locked */;
        *perr = OS_ERR_TMR_NON_AVAIL;
        return ((OS_TMR *)0);
    }
    /*@ tmr_create_locked_facts(env, args, before, locked) && ptmr != 0 &&
        tmr_alloc_configured_result(tmr_create_globals(env), tmr_create_timers(locked), ptmr)
        which implies
        exists (i : Z) (private : TimerPrivateAllocation) (allocated : GlobTimerState),
        tmr_create_allocated_facts(env, args, before, locked, ptmr, i, private, allocated) &&
        timer_inv(tmr_create_globals(env), allocated) *
        timer_private_rep(tmr_create_globals(env), i, private)
    */
    /*@ Given i private allocated */
    /*@ tmr_create_allocated_facts(env, args, before, locked, ptmr, i, private, allocated) &&
        timer_private_rep(tmr_create_globals(env), i, private)
        which implies
        tmr_create_allocated_facts(env, args, before, locked, ptmr, i, private, allocated) &&
        data_at(&(ptmr->OSTmrState), unsigned char, timerImageState(timerPrivateImage(private))) *
        data_at(&(ptmr->OSTmrDly), INT32U, timerImageDelay(timerPrivateImage(private))) *
        data_at(&(ptmr->OSTmrPeriod), INT32U, timerImagePeriod(timerPrivateImage(private))) *
        data_at(&(ptmr->OSTmrOpt), unsigned char, timerImageOption(timerPrivateImage(private))) *
        data_at(&(ptmr->OSTmrCallback), OS_TMR_CALLBACK, timerImageCallback(timerPrivateImage(private))) *
        data_at(&(ptmr->OSTmrCallbackArg), void *, timerImageArg(timerPrivateImage(private))) *
        data_at(&(ptmr->OSTmrName), INT8U *, timerImageName(timerPrivateImage(private))) *
        tmr_create_retained_fields(ptmr, timerPrivateImage(private))
    */
    ptmr->OSTmrState       = OS_TMR_STATE_STOPPED;          /* Indicate that timer is not running yet                 */
    ptmr->OSTmrDly         = dly;
    ptmr->OSTmrPeriod      = period;
    ptmr->OSTmrOpt         = opt;
    ptmr->OSTmrCallback    = callback;
    ptmr->OSTmrCallbackArg = callback_arg;
#if OS_TMR_CFG_NAME_EN > 0u
    if (pname == (INT8U *)0) {                              /* Is 'pname' a NULL pointer?                             */
        /*@ tmr_create_allocated_facts(env, args, before, locked, ptmr, i, private, allocated) &&
            tmr_create_name_argument(args) == 0 && tmr_create_default_name(args) == LitMap("?") &&
            tmr_create_kernel_frame(env, locked) *
            tmr_create_name_storage(tmr_create_name_plan(env)) * tmr_create_global_strings(env, LitMap)
            which implies
            exists (literal_rest : Assertion),
            tmr_create_allocated_facts(env, args, before, locked, ptmr, i, private, allocated) &&
            tmr_create_literal_rejoin(env, locked, LitMap, literal_rest) &&
            store_stringLit(LitMap("?"), "?") * literal_rest *
            GlobalStrings_missing(LitMap, cons("?", nil))
        */
        /*@ Given literal_rest */
        ptmr->OSTmrName    = (INT8U *)(void *)"?";
        /*@ tmr_create_literal_rejoin(env, locked, LitMap, literal_rest) &&
            store_stringLit(LitMap("?"), "?") * literal_rest *
            GlobalStrings_missing(LitMap, cons("?", nil))
            which implies
            tmr_create_kernel_frame(env, locked) *
            tmr_create_name_storage(tmr_create_name_plan(env)) * tmr_create_global_strings(env, LitMap)
        */
    } else {
        ptmr->OSTmrName    = pname;
    }
#endif
    /*@ tmr_create_allocated_facts(env, args, before, locked, ptmr, i, private, allocated) &&
        data_at(&(ptmr->OSTmrState), unsigned char, 1) *
        data_at(&(ptmr->OSTmrDly), INT32U, tmr_create_delay(args)) *
        data_at(&(ptmr->OSTmrPeriod), INT32U, tmr_create_period(args)) *
        data_at(&(ptmr->OSTmrOpt), unsigned char, tmr_create_option(args)) *
        data_at(&(ptmr->OSTmrCallback), OS_TMR_CALLBACK, tmr_create_callback(args)) *
        data_at(&(ptmr->OSTmrCallbackArg), void *, tmr_create_callback_arg(args)) *
        data_at(&(ptmr->OSTmrName), INT8U *, tmr_create_chosen_name(args)) *
        tmr_create_retained_fields(ptmr, timerPrivateImage(private)) *
        timer_inv(tmr_create_globals(env), allocated) *
        tmr_create_kernel_frame(env, locked) *
        tmr_create_name_storage(tmr_create_name_plan(env))
        which implies
        exists (completion : UCOS2_Verify_State),
        tmr_create_allocated_facts(env, args, before, locked, ptmr, i, private, allocated) &&
        tmr_create_prefix(env, args, before, TmrCreateStored(i, private), completion) &&
        os_sched_unlock_global_addresses(tmr_create_globals(env), &OSRunning, &OSIntNesting,
          &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        os_sched_unlock_pre(tmr_create_external(env), tmr_create_platform(env),
          tmr_create_critical(env), tmr_create_globals(env), tmr_create_caller(env),
          tmr_create_mask(env), completion) *
        tmr_create_result_storage(env, args, TmrCreateStored(i, private))
    */
    /*@ Given completion */
    OSSchedUnlock() /*@ where external = tmr_create_external(env), platform = tmr_create_platform(env),
            critical = tmr_create_critical(env), sg = tmr_create_globals(env),
            context = tmr_create_caller(env), mask = tmr_create_mask(env), before = completion */;
    OS_TRACE_TMR_CREATE(ptmr, ptmr->OSTmrName);
    *perr = OS_ERR_NONE;
    return (ptmr);
}
