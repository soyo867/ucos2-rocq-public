/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT32U  OSTmrRemainGet (OS_TMR  *ptmr,
                        INT8U   *perr)
/*@ With (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
         (critical : CriticalRegionResources) (sg : StableGlobVars)
         (context : OsSchedCallContext) (mask : Z) (raw : bool)
         (p ty : Z) (original : TimerImage) (i : Z) (before : UCOS2_Verify_State)
         (error_addr : Z) (F : Assertion) (X : TmrRemainGetOutput -> UCOS2_Verify_State -> Prop)
    Require ptmr == p && perr == error_addr &&
      tmr_remain_get_layout(p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrState),
        field_addr(ptmr, OS_TMR, OSTmrOpt), field_addr(ptmr, OS_TMR, OSTmrDly),
        field_addr(ptmr, OS_TMR, OSTmrPeriod), field_addr(ptmr, OS_TMR, OSTmrMatch)) &&
      &OSIntNesting == tmr_remain_get_int_address(sg) && &OSTmrTime == tmr_remain_get_time_address(sg) &&
      os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
        &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr,
        OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
      tmr_remain_get_safe(external, critical, sg, context, raw, p, ty, original, i, before, X) &&
      tmr_remain_get_input(external, platform, critical, sg, context, mask, raw, p, ty, original, i, before) *
      undef_data_at(perr, INT8U) * F
    Ensure tmr_remain_get_post(external, platform, critical, sg, context, mask, raw, p, ty,
      original, i, before, error_addr, __return, F, X)
*/
{
    INT32U  remain;


#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return (0u);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (ptmr == (OS_TMR *)0) {
        *perr = OS_ERR_TMR_INVALID;
        return (0u);
    }
#endif
    /*@ ptmr == p && p != 0 &&
        tmr_remain_get_layout(p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrState),
          field_addr(ptmr, OS_TMR, OSTmrOpt), field_addr(ptmr, OS_TMR, OSTmrDly),
          field_addr(ptmr, OS_TMR, OSTmrPeriod), field_addr(ptmr, OS_TMR, OSTmrMatch)) &&
        &OSIntNesting == tmr_remain_get_int_address(sg) &&
        tmr_remain_get_input(external, platform, critical, sg, context, mask, raw, p, ty, original, i, before)
        which implies
        ptmr == p && p != 0 && 0 <= ty && ty <= 255 &&
        0 <= tmr_remain_get_ints(before) && tmr_remain_get_ints(before) <= 255 &&
        tmr_remain_get_layout(p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrState),
          field_addr(ptmr, OS_TMR, OSTmrOpt), field_addr(ptmr, OS_TMR, OSTmrDly),
          field_addr(ptmr, OS_TMR, OSTmrPeriod), field_addr(ptmr, OS_TMR, OSTmrMatch)) &&
        tmr_remain_get_entry_facts(external, critical, sg, context, raw, p, ty, original, i, before) &&
        data_at(field_addr(ptmr, OS_TMR, OSTmrType), INT8U, ty) *
        data_at(&OSIntNesting, INT8U, tmr_remain_get_ints(before)) *
        tmr_remain_get_observation_rest(sg, raw, p, ty, original, i, before) *
        tmr_remain_get_call_resources(external, platform, sg, context, mask, p, ty, tmr_remain_get_ints(before))
    */
    if (ptmr->OSTmrType != OS_TMR_TYPE) {              /* Validate timer structure                                    */
        *perr = OS_ERR_TMR_INVALID_TYPE;
        return (0u);
    }
    if (OSIntNesting > 0u) {                           /* See if trying to call from an ISR                           */
        *perr = OS_ERR_TMR_ISR;
        return (0u);
    }
    /*@ ptmr == p && p != 0 && ty == 100 && tmr_remain_get_ints(before) == 0 &&
        &OSIntNesting == tmr_remain_get_int_address(sg) &&
        tmr_remain_get_layout(p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrState),
          field_addr(ptmr, OS_TMR, OSTmrOpt), field_addr(ptmr, OS_TMR, OSTmrDly),
          field_addr(ptmr, OS_TMR, OSTmrPeriod), field_addr(ptmr, OS_TMR, OSTmrMatch)) &&
        tmr_remain_get_entry_facts(external, critical, sg, context, raw, p, ty, original, i, before) &&
        data_at(field_addr(ptmr, OS_TMR, OSTmrType), INT8U, ty) *
        data_at(&OSIntNesting, INT8U, tmr_remain_get_ints(before)) *
        tmr_remain_get_observation_rest(sg, raw, p, ty, original, i, before) *
        tmr_remain_get_call_resources(external, platform, sg, context, mask, p, ty, tmr_remain_get_ints(before))
        which implies
        ptmr == p && p != 0 && ty == 100 && tmr_remain_get_ints(before) == 0 &&
        tmr_remain_get_layout(p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrState),
          field_addr(ptmr, OS_TMR, OSTmrOpt), field_addr(ptmr, OS_TMR, OSTmrDly),
          field_addr(ptmr, OS_TMR, OSTmrPeriod), field_addr(ptmr, OS_TMR, OSTmrMatch)) &&
        tmr_remain_get_entry_facts(external, critical, sg, context, raw, p, ty, original, i, before) &&
        os_sched_lock_pre(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, before) *
        tmr_remain_get_private(raw, p, ty, tmr_remain_get_ints(before), original) *
        os_sched_context_resources(external, context) * unmap_table_rep(sg)
    */
    OSSchedLock()/*@ where platform=platform, critical=critical, sg=sg,
      invocation=os_sched_call_invocation(context), origin=os_sched_call_origin(context), mask=mask, before=before */;
    /*@ ptmr == p && p != 0 && ty == 100 && tmr_remain_get_ints(before) == 0 &&
        tmr_remain_get_layout(p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrState),
          field_addr(ptmr, OS_TMR, OSTmrOpt), field_addr(ptmr, OS_TMR, OSTmrDly),
          field_addr(ptmr, OS_TMR, OSTmrPeriod), field_addr(ptmr, OS_TMR, OSTmrMatch)) &&
        tmr_remain_get_entry_facts(external, critical, sg, context, raw, p, ty, original, i, before) &&
        os_sched_lock_post(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, before) *
        tmr_remain_get_private(raw, p, ty, tmr_remain_get_ints(before), original) *
        os_sched_context_resources(external, context) * unmap_table_rep(sg)
        which implies exists acquired locked current,
        ptmr == p &&
        tmr_remain_get_layout(p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrState),
          field_addr(ptmr, OS_TMR, OSTmrOpt), field_addr(ptmr, OS_TMR, OSTmrDly),
          field_addr(ptmr, OS_TMR, OSTmrPeriod), field_addr(ptmr, OS_TMR, OSTmrMatch)) &&
        tmr_remain_get_locked_facts(external, critical, sg, context, raw, p, ty, original, i, before, acquired, locked, current) &&
        data_at(field_addr(ptmr, OS_TMR, OSTmrState), INT8U, tmr_remain_get_state(current)) *
        tmr_remain_get_payload(sg, p, current, locked) * tmr_remain_get_locked_rest(sg, raw, p, ty, i, current, locked) *
        interrupt_platform_running(platform, os_sched_call_invocation(context), os_sched_call_origin(context), mask) *
        os_sched_context_resources(external, context) * unmap_table_rep(sg)
    */
    /*@ Given acquired locked current */
    switch (ptmr->OSTmrState) {
        case OS_TMR_STATE_RUNNING:
             /*@ ptmr == p && tmr_remain_get_layout(p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrState),
          field_addr(ptmr, OS_TMR, OSTmrOpt), field_addr(ptmr, OS_TMR, OSTmrDly),
          field_addr(ptmr, OS_TMR, OSTmrPeriod), field_addr(ptmr, OS_TMR, OSTmrMatch)) &&
                 &OSTmrTime == tmr_remain_get_time_address(sg) && tmr_remain_get_state(current) == 3 &&
                 tmr_remain_get_payload(sg, p, current, locked)
                 which implies
                 ptmr == p && tmr_remain_get_layout(p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrState),
          field_addr(ptmr, OS_TMR, OSTmrOpt), field_addr(ptmr, OS_TMR, OSTmrDly),
          field_addr(ptmr, OS_TMR, OSTmrPeriod), field_addr(ptmr, OS_TMR, OSTmrMatch)) && tmr_remain_get_state(current) == 3 &&
                 data_at(field_addr(ptmr, OS_TMR, OSTmrMatch), INT32U, tmr_remain_get_match(current)) *
                 data_at(&OSTmrTime, INT32U, tmr_remain_get_time(locked))
             */
             remain = ptmr->OSTmrMatch - OSTmrTime;    /* Determine how much time is left to timeout                  */
             /*@ Assert ptmr == p && perr == error_addr &&
                 os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr,
          OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                 tmr_remain_get_safe(external, critical, sg, context, raw, p, ty, original, i, before, X) &&
                 tmr_remain_get_ready(external, platform, critical, sg, context, mask, raw, p, ty,
                   original, i, before, acquired, locked, current, remain, 0) *
                 undef_data_at(perr, INT8U) * F
             */
             /*@ ptmr == p && perr == error_addr &&
                 tmr_remain_get_ready(external, platform, critical, sg, context, mask, raw, p, ty,
                   original, i, before, acquired, locked, current, remain, 0)
                 which implies
                 ptmr == p && perr == error_addr &&
                 tmr_remain_get_observed(critical, sg, context, raw, p, ty, original, i, before, locked, remain, 0) &&
                 os_sched_unlock_pre(external, platform, critical, sg, context, mask, locked) *
                 tmr_remain_get_private(raw, p, ty, tmr_remain_get_ints(before), original)
             */
             OSSchedUnlock()/*@ where external=external, platform=platform, critical=critical,
               sg=sg, context=context, mask=mask, before=locked */;
             *perr  = OS_ERR_NONE;
             return (remain);

        case OS_TMR_STATE_STOPPED:                     /* It's assumed that the timer has not started yet             */
             /*@ ptmr == p && tmr_remain_get_layout(p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrState),
          field_addr(ptmr, OS_TMR, OSTmrOpt), field_addr(ptmr, OS_TMR, OSTmrDly),
          field_addr(ptmr, OS_TMR, OSTmrPeriod), field_addr(ptmr, OS_TMR, OSTmrMatch)) && tmr_remain_get_state(current) == 1 &&
                 tmr_remain_get_payload(sg, p, current, locked)
                 which implies
                 ptmr == p && tmr_remain_get_layout(p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrState),
          field_addr(ptmr, OS_TMR, OSTmrOpt), field_addr(ptmr, OS_TMR, OSTmrDly),
          field_addr(ptmr, OS_TMR, OSTmrPeriod), field_addr(ptmr, OS_TMR, OSTmrMatch)) && tmr_remain_get_state(current) == 1 &&
                 data_at(field_addr(ptmr, OS_TMR, OSTmrOpt), INT8U, tmr_remain_get_option(current)) *
                 data_at(field_addr(ptmr, OS_TMR, OSTmrDly), INT32U, tmr_remain_get_delay(current)) *
                 tmr_remain_get_period_storage(p, current)
             */
             switch (ptmr->OSTmrOpt) {
                 case OS_TMR_OPT_PERIODIC:
                      if (ptmr->OSTmrDly == 0u) {
                          /*@ ptmr == p && tmr_remain_get_layout(p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrState),
          field_addr(ptmr, OS_TMR, OSTmrOpt), field_addr(ptmr, OS_TMR, OSTmrDly),
          field_addr(ptmr, OS_TMR, OSTmrPeriod), field_addr(ptmr, OS_TMR, OSTmrMatch)) &&
                              tmr_remain_get_option(current) == 2 && tmr_remain_get_delay(current) == 0 &&
                              tmr_remain_get_period_storage(p, current)
                              which implies
                              ptmr == p && tmr_remain_get_layout(p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrState),
          field_addr(ptmr, OS_TMR, OSTmrOpt), field_addr(ptmr, OS_TMR, OSTmrDly),
          field_addr(ptmr, OS_TMR, OSTmrPeriod), field_addr(ptmr, OS_TMR, OSTmrMatch)) &&
                              tmr_remain_get_option(current) == 2 && tmr_remain_get_delay(current) == 0 &&
                              data_at(field_addr(ptmr, OS_TMR, OSTmrPeriod), INT32U, tmr_remain_get_period(current))
                          */
                          remain = ptmr->OSTmrPeriod;
                      } else {
                          remain = ptmr->OSTmrDly;
                      }
             /*@ Assert ptmr == p && perr == error_addr &&
                 os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr,
          OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                 tmr_remain_get_safe(external, critical, sg, context, raw, p, ty, original, i, before, X) &&
                 tmr_remain_get_ready(external, platform, critical, sg, context, mask, raw, p, ty,
                   original, i, before, acquired, locked, current, remain, 0) *
                 undef_data_at(perr, INT8U) * F
             */
             /*@ ptmr == p && perr == error_addr &&
                 tmr_remain_get_ready(external, platform, critical, sg, context, mask, raw, p, ty,
                   original, i, before, acquired, locked, current, remain, 0)
                 which implies
                 ptmr == p && perr == error_addr &&
                 tmr_remain_get_observed(critical, sg, context, raw, p, ty, original, i, before, locked, remain, 0) &&
                 os_sched_unlock_pre(external, platform, critical, sg, context, mask, locked) *
                 tmr_remain_get_private(raw, p, ty, tmr_remain_get_ints(before), original)
             */
                      OSSchedUnlock()/*@ where external=external, platform=platform, critical=critical,
               sg=sg, context=context, mask=mask, before=locked */;
                      *perr  = OS_ERR_NONE;
                      break;

                 case OS_TMR_OPT_ONE_SHOT:
                 default:
                      remain = ptmr->OSTmrDly;
             /*@ Assert ptmr == p && perr == error_addr &&
                 os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr,
          OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                 tmr_remain_get_safe(external, critical, sg, context, raw, p, ty, original, i, before, X) &&
                 tmr_remain_get_ready(external, platform, critical, sg, context, mask, raw, p, ty,
                   original, i, before, acquired, locked, current, remain, 0) *
                 undef_data_at(perr, INT8U) * F
             */
             /*@ ptmr == p && perr == error_addr &&
                 tmr_remain_get_ready(external, platform, critical, sg, context, mask, raw, p, ty,
                   original, i, before, acquired, locked, current, remain, 0)
                 which implies
                 ptmr == p && perr == error_addr &&
                 tmr_remain_get_observed(critical, sg, context, raw, p, ty, original, i, before, locked, remain, 0) &&
                 os_sched_unlock_pre(external, platform, critical, sg, context, mask, locked) *
                 tmr_remain_get_private(raw, p, ty, tmr_remain_get_ints(before), original)
             */
                      OSSchedUnlock()/*@ where external=external, platform=platform, critical=critical,
               sg=sg, context=context, mask=mask, before=locked */;
                      *perr  = OS_ERR_NONE;
                      break;
             }
             /*@ Assert ptmr == p && perr == error_addr &&
                 tmr_remain_get_post(external, platform, critical, sg, context, mask, raw, p, ty,
                   original, i, before, error_addr, remain, F, X)
             */
             return (remain);

        case OS_TMR_STATE_COMPLETED:                   /* Only ONE-SHOT that timed out can be in this state           */
             /*@ Assert ptmr == p && perr == error_addr &&
                 os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr,
          OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                 tmr_remain_get_safe(external, critical, sg, context, raw, p, ty, original, i, before, X) &&
                 tmr_remain_get_ready(external, platform, critical, sg, context, mask, raw, p, ty,
                   original, i, before, acquired, locked, current, 0, 0) *
                 undef_data_at(perr, INT8U) * F * undef_data_at(&remain, INT32U)
             */
             /*@ ptmr == p && perr == error_addr &&
                 tmr_remain_get_ready(external, platform, critical, sg, context, mask, raw, p, ty,
                   original, i, before, acquired, locked, current, 0, 0)
                 which implies
                 ptmr == p && perr == error_addr &&
                 tmr_remain_get_observed(critical, sg, context, raw, p, ty, original, i, before, locked, 0, 0) &&
                 os_sched_unlock_pre(external, platform, critical, sg, context, mask, locked) *
                 tmr_remain_get_private(raw, p, ty, tmr_remain_get_ints(before), original)
             */
             OSSchedUnlock()/*@ where external=external, platform=platform, critical=critical,
               sg=sg, context=context, mask=mask, before=locked */;
             *perr = OS_ERR_NONE;
             return (0u);

        case OS_TMR_STATE_UNUSED:
             /*@ Assert ptmr == p && perr == error_addr &&
                 os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr,
          OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                 tmr_remain_get_safe(external, critical, sg, context, raw, p, ty, original, i, before, X) &&
                 tmr_remain_get_ready(external, platform, critical, sg, context, mask, raw, p, ty,
                   original, i, before, acquired, locked, current, 0, 135) *
                 undef_data_at(perr, INT8U) * F * undef_data_at(&remain, INT32U)
             */
             /*@ ptmr == p && perr == error_addr &&
                 tmr_remain_get_ready(external, platform, critical, sg, context, mask, raw, p, ty,
                   original, i, before, acquired, locked, current, 0, 135)
                 which implies
                 ptmr == p && perr == error_addr &&
                 tmr_remain_get_observed(critical, sg, context, raw, p, ty, original, i, before, locked, 0, 135) &&
                 os_sched_unlock_pre(external, platform, critical, sg, context, mask, locked) *
                 tmr_remain_get_private(raw, p, ty, tmr_remain_get_ints(before), original)
             */
             OSSchedUnlock()/*@ where external=external, platform=platform, critical=critical,
               sg=sg, context=context, mask=mask, before=locked */;
             *perr = OS_ERR_TMR_INACTIVE;
             return (0u);

        default:
             /*@ Assert ptmr == p && perr == error_addr &&
                 os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr,
          OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                 tmr_remain_get_safe(external, critical, sg, context, raw, p, ty, original, i, before, X) &&
                 tmr_remain_get_ready(external, platform, critical, sg, context, mask, raw, p, ty,
                   original, i, before, acquired, locked, current, 0, 141) *
                 undef_data_at(perr, INT8U) * F * undef_data_at(&remain, INT32U)
             */
             /*@ ptmr == p && perr == error_addr &&
                 tmr_remain_get_ready(external, platform, critical, sg, context, mask, raw, p, ty,
                   original, i, before, acquired, locked, current, 0, 141)
                 which implies
                 ptmr == p && perr == error_addr &&
                 tmr_remain_get_observed(critical, sg, context, raw, p, ty, original, i, before, locked, 0, 141) &&
                 os_sched_unlock_pre(external, platform, critical, sg, context, mask, locked) *
                 tmr_remain_get_private(raw, p, ty, tmr_remain_get_ints(before), original)
             */
             OSSchedUnlock()/*@ where external=external, platform=platform, critical=critical,
               sg=sg, context=context, mask=mask, before=locked */;
             *perr = OS_ERR_TMR_INVALID_STATE;
             return (0u);
    }
}
