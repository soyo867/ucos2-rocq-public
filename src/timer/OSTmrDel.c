/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with the original-header environment and annotation_carrier.py.
 */

BOOLEAN  OSTmrDel (OS_TMR  *ptmr,
                   INT8U   *perr)
/*@ With (external : OsSchedExternalResources)
         (platform : InterruptPlatformResources)
         (critical : CriticalRegionResources) (sg : StableGlobVars)
         (context : OsSchedCallContext) (mask : Z)
         (before : UCOS2_Verify_State) X
         (ptmr0 : addr) (perr0 : addr) (perr_in : Z)
         (i : Z) (image : TimerImage)
         (type_byte : Z) (nesting : Z) (LitMap : String -> Z)
    Require ptmr0 == ptmr && perr0 == perr && perr0 != 0 &&
            data_at(perr, unsigned char, perr_in) &&
            tmr_del_pre(platform, critical, sg,
              os_sched_call_invocation(context), os_sched_call_origin(context),
              mask, before, ptmr0, perr0, perr_in) &&
            tmr_del_scheduler_acquire_safety(external, critical, sg,
              context, before, ptmr0, LitMap("?")) &&
            os_sched_context_resources(external, context) *
            unmap_table_rep(sg) *
            GlobalStrings(LitMap) &&
            tmr_del_observation_case(sg, before, ptmr0, i, image) &&
            safeExec(tmr_del_at_state(before),
              tmr_del_call_program(external, critical, sg, context, ptmr0, LitMap("?")), X)
    Ensure tmr_del_api_post(external, platform, critical, sg, context, mask,
              before, ptmr0, LitMap("?"), perr0, __return, X) *
            GlobalStrings(LitMap)
*/
{
#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return (OS_FALSE);
    }
#endif

#ifdef OS_SAFETY_CRITICAL_IEC61508
    if (OSSafetyCriticalStartFlag == OS_TRUE) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        *perr = OS_ERR_ILLEGAL_DEL_RUN_TIME;
        return (OS_FALSE);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (ptmr == (OS_TMR *)0) {
        *perr = OS_ERR_TMR_INVALID;
        return (OS_FALSE);
    }
#endif

    OS_TRACE_TMR_DEL_ENTER(ptmr);

    /*@ tmr_del_pre(platform, critical, sg,
          os_sched_call_invocation(context), os_sched_call_origin(context),
          mask, before, ptmr0, perr0, perr_in)
        && ptmr0 != 0 &&
           tmr_del_scheduler_acquire_safety(external, critical, sg,
             context, before, ptmr0, LitMap("?")) &&
           os_sched_context_resources(external, context) *
           unmap_table_rep(sg) *
           GlobalStrings(LitMap) &&
           tmr_del_observation_case(sg, before, ptmr0, i, image)
        which implies
          tmr_del_observation_binding(sg, before, ptmr0, i, image) &&
          valid_stable_glob_vars(sg) &&
          tmr_del_c_bindings(sg, ptmr0) &&
          UCOS2_state_inv(sg, before) &&
          interrupt_platform_running(platform,
            os_sched_call_invocation(context), os_sched_call_origin(context), mask) *
          data_at(&(((OS_TMR *)ptmr0)->OSTmrType), unsigned char,
                  tmr_del_image_type(image)) *
          data_at(&OSIntNesting, unsigned char, tmr_del_int_nesting(before)) *
          tmr_del_scheduler_acquire_safety(external, critical, sg,
            context, before, ptmr0, LitMap("?")) &&
          os_sched_context_resources(external, context) *
          unmap_table_rep(sg) *
          tmr_del_observation_residual(sg, before, i, image) *
          GlobalStrings(LitMap)
    */

    if (ptmr->OSTmrType != OS_TMR_TYPE) {
        *perr = OS_ERR_TMR_INVALID_TYPE;
        OS_TRACE_TMR_DEL_EXIT(*perr);
        return (OS_FALSE);
    }
    if (OSIntNesting > 0u) {
        *perr  = OS_ERR_TMR_ISR;
        OS_TRACE_TMR_DEL_EXIT(*perr);
        return (OS_FALSE);
    }
    /*@ tmr_del_observation_binding(sg, before, ptmr0, i, image) &&
        tmr_del_c_bindings(sg, ptmr0) && ptmr0 != 0 &&
        tmr_del_image_type(image) == 100 && tmr_del_int_nesting(before) <= 0 &&
        os_sched_lock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting) &&
        interrupt_platform_running(platform,
          os_sched_call_invocation(context), os_sched_call_origin(context), mask) *
        (UCOS2_state_inv(sg, before) &&
          data_at(&(((OS_TMR *)ptmr0)->OSTmrType), unsigned char,
                  tmr_del_image_type(image)) *
          data_at(&OSIntNesting, unsigned char, tmr_del_int_nesting(before)) *
          tmr_del_observation_residual(sg, before, i, image))
        which implies
        tmr_del_checks_passed(ptmr0, image, before) &&
        os_sched_lock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting) &&
        os_sched_lock_pre(platform, critical, sg,
          os_sched_call_invocation(context), os_sched_call_origin(context), mask, before)
    */
    OSSchedLock();
    /*@ os_sched_lock_post(platform, critical, sg,
              os_sched_call_invocation(context), os_sched_call_origin(context), mask, before) &&
        valid_stable_glob_vars(sg) && tmr_del_c_bindings(sg, ptmr0) &&
        tmr_del_checks_passed(ptmr0, image, before) &&
        tmr_del_observation_binding(sg, before, ptmr0, i, image)
        which implies
        exists (locked : UCOS2_Verify_State)
               (current_image : TimerImage),
          tmr_del_call_history(critical, sg, os_sched_call_invocation(context),
                   before, ptmr0, i, image, locked) &&
          UCOS2_state_inv(sg, locked) &&
          timer_api_initialized(tmr_del_timer_state(locked)) &&
          tmr_del_locked_image(locked, i, current_image) &&
          interrupt_platform_running(platform,
            os_sched_call_invocation(context), os_sched_call_origin(context), mask) *
          data_at(&(((OS_TMR *)ptmr0)->OSTmrType), unsigned char,
                         tmr_del_image_type(current_image)) *
                 data_at(&(((OS_TMR *)ptmr0)->OSTmrState), unsigned char,
                         tmr_del_image_state(current_image)) *
                 tmr_del_locked_observation_residual(sg, locked, i, current_image)
    */
    switch (ptmr->OSTmrState) {
        case OS_TMR_STATE_RUNNING:
             /*@ exists (locked : UCOS2_Verify_State) (current_image : TimerImage),
                 tmr_del_c_bindings(sg, ptmr0) && tmr_del_call_history(critical, sg, os_sched_call_invocation(context),
                   before, ptmr0, i, image, locked) &&
                 UCOS2_state_inv(sg, locked) &&
                 timer_api_initialized(tmr_del_timer_state(locked)) &&
                 tmr_del_locked_image(locked, i, current_image) &&
                 tmr_del_image_state(current_image) == 3 &&
                 data_at(&(((OS_TMR *)ptmr0)->OSTmrType), unsigned char,
                         tmr_del_image_type(current_image)) *
                 data_at(&(((OS_TMR *)ptmr0)->OSTmrState), unsigned char,
                         tmr_del_image_state(current_image)) *
                 tmr_del_locked_observation_residual(sg, locked, i, current_image)
                 which implies
                 tmr_unlink_layout && tmr_unlink_profile(sg) &&
                 timer_api_initialized(tmr_del_timer_state(locked)) &&
                 tmr_unlink_running(tmr_del_timer_state(locked), i) &&
                 ptmr0 == timer_pool_addr(sg, i) &&
                 OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
                 timer_inv(sg, tmr_del_timer_state(locked)) *
                 UCOS2_raw_rep_missing_timer(sg, locked)
             */
             /*@ data_at(&ptmr, struct os_tmr *, ptmr) &&
                 ptmr0 == ptmr && ptmr0 == timer_pool_addr(sg, i)
                 which implies
                 data_at(&ptmr, struct os_tmr *, timer_pool_addr(sg, i))
             */
             OSTmr_Unlink(ptmr) /*@ where sg = sg, s = tmr_del_timer_state(locked), i = i,
                 R = UCOS2_raw_rep_missing_timer(sg, locked) */;
             /*@ exists (locked : UCOS2_Verify_State),
                 tmr_del_c_bindings(sg, ptmr0) &&
                 ptmr0 == timer_pool_addr(sg, i) &&
                 timer_api_initialized(tmr_del_timer_state(locked)) &&
                 UCOS2_state_inv(sg, locked) &&
                 tmr_unlink_running(tmr_del_timer_state(locked), i) &&
                 tmr_unlink_configured_post(sg, tmr_del_timer_state(locked), i) *
                 GlobalStrings(LitMap)
                 which implies
                 exists (s : GlobTimerState) (old : TimerImage),
                   tmr_del_free_input(sg, s, i, old, timer_pool_addr(sg, i)) &&
                   tmr_del_release_step(sg, locked, s, i, old, LitMap("?")) &&
                   timer_inv(sg, s) * GlobalStrings(LitMap)
             */
             OSTmr_Free(ptmr) /*@ where sg = sg, i = i, LitMap = LitMap */;
             /*@ exists (locked : UCOS2_Verify_State) (s : GlobTimerState) (old : TimerImage),
                 tmr_del_c_bindings(sg, ptmr0) && tmr_del_call_history(critical, sg, os_sched_call_invocation(context),
                   before, ptmr0, i, image, locked) &&
                 UCOS2_state_inv(sg, locked) &&
                 timer_api_initialized(tmr_del_timer_state(locked)) &&
                 tmr_del_release_step(sg, locked, s, i, old, LitMap("?")) &&
                 tmr_del_scheduler_acquire_safety(external, critical, sg,
                   context, before, ptmr0, LitMap("?")) &&
                 tmr_free_valid_post(sg, s, i, old, LitMap("?")) *
                 UCOS2_raw_rep_missing_timer(sg, locked) *
                 interrupt_platform_running(platform,
                   os_sched_call_invocation(context), os_sched_call_origin(context), mask) *
                 os_sched_context_resources(external, context) * unmap_table_rep(sg)
                 which implies
                 tmr_del_result_prop(critical, sg, os_sched_call_invocation(context),
                   ptmr0, LitMap("?"), before, tmr_del_release_state(sg, locked, s, i, old, LitMap("?")), tmr_del_success_result) &&
                 os_sched_unlock_global_addresses(sg, &OSRunning,
                   &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
                   &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl,
                   &OSRdyGrp, OSRdyTbl) &&
                 os_sched_unlock_pre(external, platform, critical, sg, context, mask,
                   tmr_del_release_state(sg, locked, s, i, old, LitMap("?")))
             */
             OSSchedUnlock() /*@ where external = external, platform = platform,
                 critical = critical, sg = sg, context = context, mask = mask,
                 before = tmr_del_release_state(sg, locked, s, i, old, LitMap("?")) */;
             *perr = OS_ERR_NONE;
             OS_TRACE_TMR_DEL_EXIT(*perr);
             return (OS_TRUE);

        case OS_TMR_STATE_STOPPED:
        case OS_TMR_STATE_COMPLETED:
             /*@ exists (locked : UCOS2_Verify_State) (current_image : TimerImage),
                 tmr_del_c_bindings(sg, ptmr0) && tmr_del_call_history(critical, sg, os_sched_call_invocation(context),
                   before, ptmr0, i, image, locked) &&
                 UCOS2_state_inv(sg, locked) &&
                 timer_api_initialized(tmr_del_timer_state(locked)) &&
                 tmr_del_locked_image(locked, i, current_image) &&
                 tmr_del_image_stopped(current_image) &&
                 data_at(&(((OS_TMR *)ptmr0)->OSTmrType), unsigned char,
                         tmr_del_image_type(current_image)) *
                 data_at(&(((OS_TMR *)ptmr0)->OSTmrState), unsigned char,
                         tmr_del_image_state(current_image)) *
                 tmr_del_locked_observation_residual(sg, locked, i, current_image) * GlobalStrings(LitMap)
                 which implies
                 tmr_del_free_input(sg, tmr_del_timer_state(locked), i, current_image, ptmr0) &&
                 tmr_del_release_step(sg, locked, tmr_del_timer_state(locked),
                   i, current_image, LitMap("?")) &&
                 timer_inv(sg, tmr_del_timer_state(locked)) *
                 UCOS2_raw_rep_missing_timer(sg, locked) * GlobalStrings(LitMap)
             */
             OSTmr_Free(ptmr) /*@ where sg = sg, s = tmr_del_timer_state(locked),
                 i = i, old = current_image, LitMap = LitMap */;
             /*@ exists (locked : UCOS2_Verify_State) (current_image : TimerImage),
                 tmr_del_c_bindings(sg, ptmr0) && tmr_del_call_history(critical, sg, os_sched_call_invocation(context),
                   before, ptmr0, i, image, locked) &&
                 UCOS2_state_inv(sg, locked) &&
                 timer_api_initialized(tmr_del_timer_state(locked)) &&
                 tmr_del_release_step(sg, locked, tmr_del_timer_state(locked), i, current_image, LitMap("?")) &&
                 tmr_del_scheduler_acquire_safety(external, critical, sg,
                   context, before, ptmr0, LitMap("?")) &&
                 tmr_free_valid_post(sg, tmr_del_timer_state(locked), i, current_image, LitMap("?")) *
                 UCOS2_raw_rep_missing_timer(sg, locked) *
                 interrupt_platform_running(platform,
                   os_sched_call_invocation(context), os_sched_call_origin(context), mask) *
                 os_sched_context_resources(external, context) * unmap_table_rep(sg)
                 which implies
                 tmr_del_result_prop(critical, sg, os_sched_call_invocation(context),
                   ptmr0, LitMap("?"), before, tmr_del_release_state(sg, locked, tmr_del_timer_state(locked), i, current_image, LitMap("?")), tmr_del_success_result) &&
                 os_sched_unlock_global_addresses(sg, &OSRunning,
                   &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
                   &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl,
                   &OSRdyGrp, OSRdyTbl) &&
                 os_sched_unlock_pre(external, platform, critical, sg, context, mask,
                   tmr_del_release_state(sg, locked, tmr_del_timer_state(locked), i, current_image, LitMap("?")))
             */
             OSSchedUnlock() /*@ where external = external, platform = platform,
                 critical = critical, sg = sg, context = context, mask = mask,
                 before = tmr_del_release_state(sg, locked, tmr_del_timer_state(locked), i, current_image, LitMap("?")) */;
             *perr = OS_ERR_NONE;
             OS_TRACE_TMR_DEL_EXIT(*perr);
             return (OS_TRUE);

        case OS_TMR_STATE_UNUSED:
             /*@ exists (locked : UCOS2_Verify_State) (current_image : TimerImage),
                 tmr_del_c_bindings(sg, ptmr0) && tmr_del_call_history(critical, sg, os_sched_call_invocation(context),
                   before, ptmr0, i, image, locked) &&
                 UCOS2_state_inv(sg, locked) &&
                 timer_api_initialized(tmr_del_timer_state(locked)) &&
                 tmr_del_locked_image(locked, i, current_image) &&
                 tmr_del_image_state(current_image) == 0 &&
                 tmr_del_scheduler_acquire_safety(external, critical, sg,
                   context, before, ptmr0, LitMap("?")) &&
                 data_at(&(((OS_TMR *)ptmr0)->OSTmrType), unsigned char,
                         tmr_del_image_type(current_image)) *
                 data_at(&(((OS_TMR *)ptmr0)->OSTmrState), unsigned char,
                         tmr_del_image_state(current_image)) *
                 tmr_del_locked_observation_residual(sg, locked, i, current_image) *
                 interrupt_platform_running(platform,
                   os_sched_call_invocation(context), os_sched_call_origin(context), mask) *
                 os_sched_context_resources(external, context) * unmap_table_rep(sg)
                 which implies
                 tmr_del_result_prop(critical, sg, os_sched_call_invocation(context),
                   ptmr0, LitMap("?"), before, locked, tmr_del_inactive_result) &&
                 os_sched_unlock_global_addresses(sg, &OSRunning,
                   &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
                   &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl,
                   &OSRdyGrp, OSRdyTbl) &&
                 os_sched_unlock_pre(external, platform, critical, sg, context, mask, locked)
             */
             OSSchedUnlock() /*@ where external = external, platform = platform,
                 critical = critical, sg = sg, context = context,
                 mask = mask, before = locked */;
             *perr = OS_ERR_TMR_INACTIVE;
             OS_TRACE_TMR_DEL_EXIT(*perr);
             return (OS_FALSE);

        default:
             /*@ exists (locked : UCOS2_Verify_State) (current_image : TimerImage),
                 tmr_del_c_bindings(sg, ptmr0) && tmr_del_call_history(critical, sg, os_sched_call_invocation(context),
                   before, ptmr0, i, image, locked) &&
                 UCOS2_state_inv(sg, locked) &&
                 timer_api_initialized(tmr_del_timer_state(locked)) &&
                 tmr_del_locked_image(locked, i, current_image) &&
                 tmr_del_image_state(current_image) != 0 &&
                 tmr_del_image_state(current_image) != 1 &&
                 tmr_del_image_state(current_image) != 2 &&
                 tmr_del_image_state(current_image) != 3 &&
                 tmr_del_scheduler_acquire_safety(external, critical, sg,
                   context, before, ptmr0, LitMap("?")) &&
                 data_at(&(((OS_TMR *)ptmr0)->OSTmrType), unsigned char,
                         tmr_del_image_type(current_image)) *
                 data_at(&(((OS_TMR *)ptmr0)->OSTmrState), unsigned char,
                         tmr_del_image_state(current_image)) *
                 tmr_del_locked_observation_residual(sg, locked, i, current_image) *
                 interrupt_platform_running(platform,
                   os_sched_call_invocation(context), os_sched_call_origin(context), mask) *
                 os_sched_context_resources(external, context) * unmap_table_rep(sg)
                 which implies
                 tmr_del_result_prop(critical, sg, os_sched_call_invocation(context),
                   ptmr0, LitMap("?"), before, locked, tmr_del_invalid_state_result) &&
                 os_sched_unlock_global_addresses(sg, &OSRunning,
                   &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
                   &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl,
                   &OSRdyGrp, OSRdyTbl) &&
                 os_sched_unlock_pre(external, platform, critical, sg, context, mask, locked)
             */
             OSSchedUnlock() /*@ where external = external, platform = platform,
                 critical = critical, sg = sg, context = context,
                 mask = mask, before = locked */;
             *perr = OS_ERR_TMR_INVALID_STATE;
             OS_TRACE_TMR_DEL_EXIT(*perr);
             return (OS_FALSE);
    }
}
