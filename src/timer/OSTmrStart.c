/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

BOOLEAN  OSTmrStart (OS_TMR   *ptmr,
                     INT8U    *perr)
/*@ With (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
         (critical : CriticalRegionResources) (sg : StableGlobVars)
         (context : OsSchedCallContext) (mask : Z) (pooled : bool)
         (p i ty raw_state error_addr : Z) (before : UCOS2_Verify_State)
         (X : tmr_start_result -> UCOS2_Verify_State -> Prop)
    Require ptmr == p && perr == error_addr &&
            tmr_start_layout(p, &(ptmr->OSTmrType), &(ptmr->OSTmrState)) &&
            os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            &OSIntNesting == g_OSIntNesting(sg) &&
            OSTmrWheelTbl == g_OSTmrWheelTbl(sg) && &OSTmrTime == g_OSTmrTime(sg) &&
            tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
            tmr_start_owned(external, platform, sg, context, mask, pooled, p, ty, raw_state, before, before) *
            undef_data_at(perr, INT8U)
    Ensure tmr_start_post(external, platform, critical, sg, context, mask,
             pooled, p, i, ty, raw_state, error_addr, __return, before, X)
*/
{
#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return (OS_FALSE);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (ptmr == (OS_TMR *)0) {
        *perr = OS_ERR_TMR_INVALID;
        return (OS_FALSE);
    }
#endif

    OS_TRACE_TMR_START_ENTER(ptmr);

    /*@ ptmr == p && p != 0 && tmr_start_layout(p, &(ptmr->OSTmrType), &(ptmr->OSTmrState)) &&
        tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
        tmr_start_owned(external, platform, sg, context, mask, pooled, p, ty, raw_state, before, before)
        which implies
        ptmr == p && p != 0 && tmr_start_layout(p, &(ptmr->OSTmrType), &(ptmr->OSTmrState)) &&
        tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
        data_at(&(ptmr->OSTmrType), INT8U, ty) *
        tmr_start_type_rest(external, platform, sg, context, mask, pooled, p, i, ty, raw_state, before)
    */
    if (ptmr->OSTmrType != OS_TMR_TYPE) {                   /* Validate timer structure                               */
        /*@ ptmr == p && p != 0 && tmr_start_layout(p, &(ptmr->OSTmrType), &(ptmr->OSTmrState)) &&
            tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
            data_at(&(ptmr->OSTmrType), INT8U, ty) *
            tmr_start_type_rest(external, platform, sg, context, mask, pooled, p, i, ty, raw_state, before)
            which implies
            ptmr == p && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
            tmr_start_owned(external, platform, sg, context, mask, pooled, p, ty, raw_state, before, before)
        */
        *perr = OS_ERR_TMR_INVALID_TYPE;
        OS_TRACE_TMR_START_EXIT(*perr);
        return (OS_FALSE);
    }
    /*@ &OSIntNesting == g_OSIntNesting(sg) && ptmr == p && p != 0 && tmr_start_layout(p, &(ptmr->OSTmrType), &(ptmr->OSTmrState)) &&
        tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
        data_at(&(ptmr->OSTmrType), INT8U, ty) *
        tmr_start_type_rest(external, platform, sg, context, mask, pooled, p, i, ty, raw_state, before)
        which implies
        &OSIntNesting == g_OSIntNesting(sg) && ptmr == p && tmr_start_layout(p, &(ptmr->OSTmrType), &(ptmr->OSTmrState)) &&
        tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
        0 <= ty && ty <= 255 &&
        0 <= os_sched_lock_ints(before) && os_sched_lock_ints(before) <= 255 &&
        UCOS2_state_inv(sg, before) &&
        data_at(&OSIntNesting, INT8U, os_sched_lock_ints(before)) *
        tmr_start_int_rest(external, platform, sg, context, mask, pooled, p, ty, raw_state, before)
    */
    if (OSIntNesting > 0u) {                                /* See if trying to call from an ISR                      */
        /*@ &OSIntNesting == g_OSIntNesting(sg) && ptmr == p && UCOS2_state_inv(sg, before) &&
            data_at(&OSIntNesting, INT8U, os_sched_lock_ints(before)) *
            tmr_start_int_rest(external, platform, sg, context, mask, pooled, p, ty, raw_state, before)
            which implies
            &OSIntNesting == g_OSIntNesting(sg) && ptmr == p && tmr_start_owned(external, platform, sg, context, mask, pooled, p, ty, raw_state, before, before)
        */
        *perr  = OS_ERR_TMR_ISR;
        OS_TRACE_TMR_START_EXIT(*perr);
        return (OS_FALSE);
    }
    /*@ &OSIntNesting == g_OSIntNesting(sg) && ptmr == p && UCOS2_state_inv(sg, before) &&
        data_at(&OSIntNesting, INT8U, os_sched_lock_ints(before)) *
        tmr_start_int_rest(external, platform, sg, context, mask, pooled, p, ty, raw_state, before)
        which implies
        &OSIntNesting == g_OSIntNesting(sg) && ptmr == p && os_sched_lock_pre(platform, critical, sg, os_sched_call_invocation(context),
          os_sched_call_origin(context), mask, before) *
        os_sched_context_resources(external, context) * unmap_table_rep(sg) *
        tmr_start_raw_rep(pooled, p, ty, raw_state, before)
    */
    OSSchedLock() /*@ where platform=platform, critical=critical, sg=sg,
      invocation=os_sched_call_invocation(context), origin=os_sched_call_origin(context), mask=mask, before=before */;
    /*@ ptmr == p && p != 0 && ty == 100 && os_sched_lock_ints(before) == 0 &&
        tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
        os_sched_lock_post(platform, critical, sg, os_sched_call_invocation(context),
          os_sched_call_origin(context), mask, before) *
        os_sched_context_resources(external, context) * unmap_table_rep(sg) *
        tmr_start_raw_rep(pooled, p, ty, raw_state, before)
        which implies
        exists (lock_entry locked : UCOS2_Verify_State) (status : Z),
        ptmr == p && p != 0 && ty == 100 && os_sched_lock_ints(before) == 0 &&
        tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
        os_sched_lock_call_relation(critical, sg, os_sched_call_invocation(context), before, lock_entry, locked) &&
        tmr_start_current(sg, pooled, p, i, raw_state, status, locked) &&
        tmr_start_owned(external, platform, sg, context, mask, pooled, p, ty, raw_state, before, locked)
    */
    /*@ Given lock_entry locked status */
    /*@ ptmr == p && p != 0 && ty == 100 && os_sched_lock_ints(before) == 0 &&
        tmr_start_layout(p, &(ptmr->OSTmrType), &(ptmr->OSTmrState)) &&
        tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
        tmr_start_current(sg, pooled, p, i, raw_state, status, locked) &&
        tmr_start_owned(external, platform, sg, context, mask, pooled, p, ty, raw_state, before, locked)
        which implies
        ptmr == p && p != 0 && ty == 100 && os_sched_lock_ints(before) == 0 &&
        tmr_start_layout(p, &(ptmr->OSTmrType), &(ptmr->OSTmrState)) &&
        tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
        tmr_start_current(sg, pooled, p, i, raw_state, status, locked) &&
        data_at(&(ptmr->OSTmrState), INT8U, status) *
        tmr_start_state_rest(external, platform, sg, context, mask, pooled, p, i, ty, raw_state, status, before, locked)
    */
    switch (ptmr->OSTmrState) {
        case OS_TMR_STATE_RUNNING:                          /* Restart the timer                                      */
             /*@ ptmr == p && p != 0 && ty == 100 && os_sched_lock_ints(before) == 0 && status == 3 &&
                 tmr_start_layout(p, &(ptmr->OSTmrType), &(ptmr->OSTmrState)) &&
                 tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) && os_sched_lock_call_relation(critical, sg, os_sched_call_invocation(context), before, lock_entry, locked) && tmr_start_current(sg, pooled, p, i, raw_state, status, locked) &&
                 data_at(&(ptmr->OSTmrState), INT8U, status) * tmr_start_state_rest(external, platform, sg, context, mask, pooled, p, i, ty, raw_state, status, before, locked)
                 which implies
                 ptmr == p && p != 0 && ty == 100 && os_sched_lock_ints(before) == 0 && status == 3 && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) && os_sched_lock_call_relation(critical, sg, os_sched_call_invocation(context), before, lock_entry, locked) && tmr_start_current(sg, pooled, p, i, raw_state, status, locked) &&
                 pooled == true && p == timer_pool_addr(sg, i) &&
                 tmr_link_layout && tmr_unlink_layout && tmr_link_profile(sg) && tmr_unlink_profile(sg) &&
                 UCOS2_state_inv(sg, locked) && timer_api_initialized(TimerState(locked)) &&
                 tmr_unlink_running(TimerState(locked), i) &&
                 timer_inv(sg, TimerState(locked)) * tmr_start_timer_frame(external, platform, sg, context, mask, locked)
             */
             OSTmr_Unlink(ptmr) /*@ where (configured_spec)
               sg=sg, s=TimerState(locked), i=i, R=tmr_start_timer_frame(external, platform, sg, context, mask, locked) */;
             /*@ ptmr == p && UCOS2_state_inv(sg, locked) && timer_api_initialized(TimerState(locked)) &&
                 tmr_link_profile(sg) && tmr_unlink_running(TimerState(locked), i) &&
                 tmr_unlink_configured_post(sg, TimerState(locked), i) * tmr_start_timer_frame(external, platform, sg, context, mask, locked)
                 which implies
                 exists (stopped : GlobTimerState),
                 ptmr == p && tmr_start_unlinked(sg, TimerState(locked), i, stopped) &&
                 UCOS2_state_inv(sg, replace_TimerS(stopped, locked)) &&
                 timer_api_initialized(stopped) && tmr_link_eligible(stopped, i) &&
                 timer_inv(sg, stopped) * tmr_start_timer_frame(external, platform, sg, context, mask, locked)
             */
             /*@ Given stopped */
             OSTmr_Link(ptmr, OS_TMR_LINK_DLY) /*@ where (configured_spec)
               sg=sg, s=stopped, i=i, kind=0, R=tmr_start_timer_frame(external, platform, sg, context, mask, locked) */;
             /*@ ptmr == p && p != 0 && ty == 100 && os_sched_lock_ints(before) == 0 && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) && os_sched_lock_call_relation(critical, sg, os_sched_call_invocation(context), before, lock_entry, locked) && tmr_start_current(sg, pooled, p, i, raw_state, status, locked) &&
                 pooled == true && status == 3 && tmr_start_unlinked(sg, TimerState(locked), i, stopped) &&
                 tmr_link_eligible(stopped, i) &&
                 UCOS2_state_inv(sg, replace_TimerS(stopped, locked)) &&
                 timer_api_initialized(stopped) &&
                 tmr_link_configured_post(sg, stopped, i, 0) * tmr_start_timer_frame(external, platform, sg, context, mask, locked)
                 which implies
                 exists (started : GlobTimerState),
                 ptmr == p && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
                 tmr_start_prefix(critical, sg, context, pooled, p, i, ty, raw_state, 1, 0, before, lock_entry, locked, replace_TimerS(started, locked)) &&
                 tmr_start_owned(external, platform, sg, context, mask, pooled, p, ty, raw_state, before, replace_TimerS(started, locked))
             */
             /*@ Given started */

             /*@ ptmr == p && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
                 tmr_start_prefix(critical, sg, context, pooled, p, i, ty, raw_state, 1, 0, before, lock_entry, locked, replace_TimerS(started, locked)) && tmr_start_owned(external, platform, sg, context, mask, pooled, p, ty, raw_state, before, replace_TimerS(started, locked))
                 which implies
                 ptmr == p && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) && tmr_start_prefix(critical, sg, context, pooled, p, i, ty, raw_state, 1, 0, before, lock_entry, locked, replace_TimerS(started, locked)) &&
                 os_sched_unlock_pre(external, platform, critical, sg, context, mask, replace_TimerS(started, locked)) *
                 tmr_start_raw_rep(pooled, p, ty, raw_state, before)
             */
             OSSchedUnlock() /*@ where external=external, platform=platform, critical=critical,
               sg=sg, context=context, mask=mask, before=replace_TimerS(started, locked) */;
             /*@ ptmr == p && os_sched_unlock_post(external, platform, critical, sg, context, mask, replace_TimerS(started, locked))
                 which implies
                 exists (returned : OsSchedCallContext) (final : UCOS2_Verify_State),
                 ptmr == p && tmr_start_unlock_return(external, critical, sg, context, replace_TimerS(started, locked), returned, final) &&
                 tmr_start_return_resources(external, platform, critical, sg, context, returned, mask, final)
             */
             /*@ Given returned final */
             *perr = OS_ERR_NONE;
             OS_TRACE_TMR_START_EXIT(*perr);
             return (OS_TRUE);

        case OS_TMR_STATE_STOPPED:                          /* Start the timer                                        */
        case OS_TMR_STATE_COMPLETED:
             /*@ ptmr == p && p != 0 && ty == 100 && os_sched_lock_ints(before) == 0 && tmr_start_nonrunning_status(status) &&
                 tmr_start_layout(p, &(ptmr->OSTmrType), &(ptmr->OSTmrState)) &&
                 tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) && os_sched_lock_call_relation(critical, sg, os_sched_call_invocation(context), before, lock_entry, locked) && tmr_start_current(sg, pooled, p, i, raw_state, status, locked) &&
                 data_at(&(ptmr->OSTmrState), INT8U, status) * tmr_start_state_rest(external, platform, sg, context, mask, pooled, p, i, ty, raw_state, status, before, locked)
                 which implies
                 ptmr == p && p != 0 && ty == 100 && os_sched_lock_ints(before) == 0 && tmr_start_nonrunning_status(status) && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) && os_sched_lock_call_relation(critical, sg, os_sched_call_invocation(context), before, lock_entry, locked) && tmr_start_current(sg, pooled, p, i, raw_state, status, locked) &&
                 pooled == true && p == timer_pool_addr(sg, i) &&
                 tmr_link_layout && tmr_unlink_layout && tmr_link_profile(sg) && tmr_unlink_profile(sg) &&
                 UCOS2_state_inv(sg, locked) && timer_api_initialized(TimerState(locked)) &&
                 tmr_link_eligible(TimerState(locked), i) &&
                 timer_inv(sg, TimerState(locked)) * tmr_start_timer_frame(external, platform, sg, context, mask, locked)
             */
             OSTmr_Link(ptmr, OS_TMR_LINK_DLY) /*@ where (configured_spec)
               sg=sg, s=TimerState(locked), i=i, kind=0, R=tmr_start_timer_frame(external, platform, sg, context, mask, locked) */;
             /*@ ptmr == p && p != 0 && ty == 100 && os_sched_lock_ints(before) == 0 && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) && os_sched_lock_call_relation(critical, sg, os_sched_call_invocation(context), before, lock_entry, locked) && tmr_start_current(sg, pooled, p, i, raw_state, status, locked) &&
                 pooled == true && tmr_start_nonrunning_status(status) &&
                 tmr_link_eligible(TimerState(locked), i) &&
                 UCOS2_state_inv(sg, locked) &&
                 timer_api_initialized(TimerState(locked)) &&
                 tmr_link_configured_post(sg, TimerState(locked), i, 0) * tmr_start_timer_frame(external, platform, sg, context, mask, locked)
                 which implies
                 exists (started : GlobTimerState),
                 ptmr == p && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
                 tmr_start_prefix(critical, sg, context, pooled, p, i, ty, raw_state, 1, 0, before, lock_entry, locked, replace_TimerS(started, locked)) &&
                 tmr_start_owned(external, platform, sg, context, mask, pooled, p, ty, raw_state, before, replace_TimerS(started, locked))
             */
             /*@ Given started */

             /*@ ptmr == p && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
                 tmr_start_prefix(critical, sg, context, pooled, p, i, ty, raw_state, 1, 0, before, lock_entry, locked, replace_TimerS(started, locked)) && tmr_start_owned(external, platform, sg, context, mask, pooled, p, ty, raw_state, before, replace_TimerS(started, locked))
                 which implies
                 ptmr == p && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) && tmr_start_prefix(critical, sg, context, pooled, p, i, ty, raw_state, 1, 0, before, lock_entry, locked, replace_TimerS(started, locked)) &&
                 os_sched_unlock_pre(external, platform, critical, sg, context, mask, replace_TimerS(started, locked)) *
                 tmr_start_raw_rep(pooled, p, ty, raw_state, before)
             */
             OSSchedUnlock() /*@ where external=external, platform=platform, critical=critical,
               sg=sg, context=context, mask=mask, before=replace_TimerS(started, locked) */;
             /*@ ptmr == p && os_sched_unlock_post(external, platform, critical, sg, context, mask, replace_TimerS(started, locked))
                 which implies
                 exists (returned : OsSchedCallContext) (final : UCOS2_Verify_State),
                 ptmr == p && tmr_start_unlock_return(external, critical, sg, context, replace_TimerS(started, locked), returned, final) &&
                 tmr_start_return_resources(external, platform, critical, sg, context, returned, mask, final)
             */
             /*@ Given returned final */
             *perr = OS_ERR_NONE;
             OS_TRACE_TMR_START_EXIT(*perr);
             return (OS_TRUE);

        case OS_TMR_STATE_UNUSED:                           /* Timer not created                                      */
             /*@ ptmr == p && p != 0 && ty == 100 && os_sched_lock_ints(before) == 0 && status == 0 &&
                 tmr_start_layout(p, &(ptmr->OSTmrType), &(ptmr->OSTmrState)) &&
                 tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) && os_sched_lock_call_relation(critical, sg, os_sched_call_invocation(context), before, lock_entry, locked) && tmr_start_current(sg, pooled, p, i, raw_state, status, locked) &&
                 data_at(&(ptmr->OSTmrState), INT8U, status) * tmr_start_state_rest(external, platform, sg, context, mask, pooled, p, i, ty, raw_state, status, before, locked)
                 which implies
                 ptmr == p && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) && tmr_start_prefix(critical, sg, context, pooled, p, i, ty, raw_state, 0, 135, before, lock_entry, locked, locked) && tmr_start_owned(external, platform, sg, context, mask, pooled, p, ty, raw_state, before, locked)
             */

             /*@ ptmr == p && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
                 tmr_start_prefix(critical, sg, context, pooled, p, i, ty, raw_state, 0, 135, before, lock_entry, locked, locked) && tmr_start_owned(external, platform, sg, context, mask, pooled, p, ty, raw_state, before, locked)
                 which implies
                 ptmr == p && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) && tmr_start_prefix(critical, sg, context, pooled, p, i, ty, raw_state, 0, 135, before, lock_entry, locked, locked) &&
                 os_sched_unlock_pre(external, platform, critical, sg, context, mask, locked) *
                 tmr_start_raw_rep(pooled, p, ty, raw_state, before)
             */
             OSSchedUnlock() /*@ where external=external, platform=platform, critical=critical,
               sg=sg, context=context, mask=mask, before=locked */;
             /*@ ptmr == p && os_sched_unlock_post(external, platform, critical, sg, context, mask, locked)
                 which implies
                 exists (returned : OsSchedCallContext) (final : UCOS2_Verify_State),
                 ptmr == p && tmr_start_unlock_return(external, critical, sg, context, locked, returned, final) &&
                 tmr_start_return_resources(external, platform, critical, sg, context, returned, mask, final)
             */
             /*@ Given returned final */
             *perr = OS_ERR_TMR_INACTIVE;
             OS_TRACE_TMR_START_EXIT(*perr);
             return (OS_FALSE);

        default:
             /*@ ptmr == p && p != 0 && ty == 100 && os_sched_lock_ints(before) == 0 && status != 0 && status != 1 && status != 2 && status != 3 &&
                 tmr_start_layout(p, &(ptmr->OSTmrType), &(ptmr->OSTmrState)) &&
                 tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) && os_sched_lock_call_relation(critical, sg, os_sched_call_invocation(context), before, lock_entry, locked) && tmr_start_current(sg, pooled, p, i, raw_state, status, locked) &&
                 data_at(&(ptmr->OSTmrState), INT8U, status) * tmr_start_state_rest(external, platform, sg, context, mask, pooled, p, i, ty, raw_state, status, before, locked)
                 which implies
                 ptmr == p && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) && tmr_start_prefix(critical, sg, context, pooled, p, i, ty, raw_state, 0, 141, before, lock_entry, locked, locked) && tmr_start_owned(external, platform, sg, context, mask, pooled, p, ty, raw_state, before, locked)
             */

             /*@ ptmr == p && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) &&
                 tmr_start_prefix(critical, sg, context, pooled, p, i, ty, raw_state, 0, 141, before, lock_entry, locked, locked) && tmr_start_owned(external, platform, sg, context, mask, pooled, p, ty, raw_state, before, locked)
                 which implies
                 ptmr == p && tmr_start_pre_facts(external, critical, sg, context, pooled, p, i, ty, raw_state, before, X) && tmr_start_prefix(critical, sg, context, pooled, p, i, ty, raw_state, 0, 141, before, lock_entry, locked, locked) &&
                 os_sched_unlock_pre(external, platform, critical, sg, context, mask, locked) *
                 tmr_start_raw_rep(pooled, p, ty, raw_state, before)
             */
             OSSchedUnlock() /*@ where external=external, platform=platform, critical=critical,
               sg=sg, context=context, mask=mask, before=locked */;
             /*@ ptmr == p && os_sched_unlock_post(external, platform, critical, sg, context, mask, locked)
                 which implies
                 exists (returned : OsSchedCallContext) (final : UCOS2_Verify_State),
                 ptmr == p && tmr_start_unlock_return(external, critical, sg, context, locked, returned, final) &&
                 tmr_start_return_resources(external, platform, critical, sg, context, returned, mask, final)
             */
             /*@ Given returned final */
             *perr = OS_ERR_TMR_INVALID_STATE;
             OS_TRACE_TMR_START_EXIT(*perr);
             return (OS_FALSE);
    }
}
