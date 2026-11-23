/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSTmrStateGet (OS_TMR  *ptmr,
                      INT8U   *perr)
/*@ With (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
         (critical : CriticalRegionResources) (sg : StableGlobVars)
         (context : OsSchedCallContext) (mask : Z) (before : UCOS2_Verify_State)
         (raw : bool) (p error_addr i ty raw_state : Z)
         (X : tmr_state_get_result -> UCOS2_Verify_State -> Prop) (F : Assertion)
    Require ptmr == p && perr == error_addr &&
      tmr_state_get_layout(sg, ptmr, field_addr(ptmr, OS_TMR, OSTmrType),
      field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) &&
      os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
      tmr_state_get_pre(external, platform, critical, sg, context, mask, before,
        ptmr, raw, i, ty, raw_state, X) * undef_data_at(perr, unsigned char) * F
    Ensure tmr_state_get_post(external, platform, critical, sg, context, mask, before,
        p, raw, i, ty, raw_state, error_addr, __return, X) * F
*/
{
    INT8U  state;


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
    /*@ ptmr != 0 &&
      tmr_state_get_layout(sg, ptmr, field_addr(ptmr, OS_TMR, OSTmrType),
        field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) &&
      tmr_state_get_pre(external, platform, critical, sg, context, mask, before,
        ptmr, raw, i, ty, raw_state, X)
      which implies
      ptmr != 0 && 0 <= ty && ty <= 255 &&
      0 <= os_sched_ints(before) && os_sched_ints(before) <= 255 &&
      tmr_state_get_layout(sg, ptmr, field_addr(ptmr, OS_TMR, OSTmrType),
        field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) &&
      tmr_state_get_entry_facts(external, critical, sg, context, before,
        ptmr, raw, i, ty, raw_state, X) &&
      data_at(&(ptmr->OSTmrType), unsigned char, ty) *
      data_at(&OSIntNesting, unsigned char, os_sched_ints(before)) *
      tmr_state_get_observation_frame(external, platform, sg, context, mask, before,
        ptmr, raw, i, ty, raw_state)
    */
    if (ptmr->OSTmrType != OS_TMR_TYPE) {              /* Validate timer structure                                    */
        *perr = OS_ERR_TMR_INVALID_TYPE;
        return (0u);
    }
    if (OSIntNesting > 0u) {                           /* See if trying to call from an ISR                           */
        *perr = OS_ERR_TMR_ISR;
        return (0u);
    }
    /*@ ptmr != 0 && ty == 100 && os_sched_ints(before) == 0 &&
      tmr_state_get_layout(sg, ptmr, field_addr(ptmr, OS_TMR, OSTmrType),
        field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) &&
      tmr_state_get_entry_facts(external, critical, sg, context, before,
        ptmr, raw, i, ty, raw_state, X) &&
      data_at(&(ptmr->OSTmrType), unsigned char, ty) *
      data_at(&OSIntNesting, unsigned char, os_sched_ints(before)) *
      tmr_state_get_observation_frame(external, platform, sg, context, mask, before,
        ptmr, raw, i, ty, raw_state)
      which implies
      ptmr != 0 && ty == 100 && os_sched_ints(before) == 0 &&
      tmr_state_get_layout(sg, ptmr, field_addr(ptmr, OS_TMR, OSTmrType),
        field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) &&
      tmr_state_get_entry_facts(external, critical, sg, context, before,
        ptmr, raw, i, ty, raw_state, X) &&
      os_sched_lock_pre(platform, critical, sg, os_sched_call_invocation(context),
        os_sched_call_origin(context), mask, before) *
      os_sched_context_resources(external, context) * unmap_table_rep(sg) *
      tmr_state_get_raw_storage(ptmr, raw, ty, raw_state, before)
    */
    OSSchedLock()/*@ where platform=platform, critical=critical, sg=sg,
      invocation=os_sched_call_invocation(context), origin=os_sched_call_origin(context),
      mask=mask, before=before */;
    /*@ ptmr != 0 && ty == 100 && os_sched_ints(before) == 0 &&
      tmr_state_get_layout(sg, ptmr, field_addr(ptmr, OS_TMR, OSTmrType),
        field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) &&
      tmr_state_get_entry_facts(external, critical, sg, context, before,
        ptmr, raw, i, ty, raw_state, X) &&
      os_sched_lock_post(platform, critical, sg, os_sched_call_invocation(context),
        os_sched_call_origin(context), mask, before) *
      os_sched_context_resources(external, context) * unmap_table_rep(sg) *
      tmr_state_get_raw_storage(ptmr, raw, ty, raw_state, before)
      which implies
      exists entry locked observed,
      ptmr != 0 && ty == 100 && os_sched_ints(before) == 0 &&
      0 <= observed && observed <= 255 &&
      tmr_state_get_layout(sg, ptmr, field_addr(ptmr, OS_TMR, OSTmrType),
        field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) &&
      tmr_state_get_entry_facts(external, critical, sg, context, before,
        ptmr, raw, i, ty, raw_state, X) &&
      os_sched_lock_call_relation(critical, sg, os_sched_call_invocation(context),
        before, entry, locked) && UCOS2_state_inv(sg, locked) &&
      tmr_state_get_observation(raw, i, raw_state, locked, observed) &&
      data_at(&(ptmr->OSTmrState), unsigned char, observed) *
      tmr_state_get_state_frame(external, platform, critical, sg, context, mask, locked,
        ptmr, raw, i, ty, observed)
    */
    /*@ Given entry locked observed */
    state = ptmr->OSTmrState;
    switch (state) {
        case OS_TMR_STATE_UNUSED:
        case OS_TMR_STATE_STOPPED:
        case OS_TMR_STATE_COMPLETED:
        case OS_TMR_STATE_RUNNING:
             *perr = OS_ERR_NONE;
             break;

        default:
             *perr = OS_ERR_TMR_INVALID_STATE;
             break;
    }
    /*@ Assert exists error,
      ptmr == p && perr == error_addr &&
      ptmr != 0 && ty == 100 && os_sched_ints(before) == 0 &&
      0 <= observed && observed <= 255 &&
      tmr_state_get_layout(sg, ptmr, field_addr(ptmr, OS_TMR, OSTmrType),
        field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) &&
      error == tmr_state_get_state_error(observed) && state == observed &&
      tmr_state_get_entry_facts(external, critical, sg, context, before,
        ptmr, raw, i, ty, raw_state, X) &&
      os_sched_lock_call_relation(critical, sg, os_sched_call_invocation(context),
        before, entry, locked) && UCOS2_state_inv(sg, locked) &&
      tmr_state_get_observation(raw, i, raw_state, locked, observed) &&
      os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
        &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
        &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
      data_at(&(ptmr->OSTmrState), unsigned char, observed) *
      tmr_state_get_state_frame(external, platform, critical, sg, context, mask, locked,
        ptmr, raw, i, ty, observed) * data_at(perr, unsigned char, error) * F
    */
    /*@ Given error */
    /*@ ptmr != 0 && ty == 100 && os_sched_ints(before) == 0 &&
      tmr_state_get_layout(sg, ptmr, field_addr(ptmr, OS_TMR, OSTmrType),
        field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) &&
      tmr_state_get_entry_facts(external, critical, sg, context, before,
        ptmr, raw, i, ty, raw_state, X) &&
      os_sched_lock_call_relation(critical, sg, os_sched_call_invocation(context),
        before, entry, locked) && UCOS2_state_inv(sg, locked) &&
      tmr_state_get_observation(raw, i, raw_state, locked, observed) &&
      data_at(&(ptmr->OSTmrState), unsigned char, observed) *
      tmr_state_get_state_frame(external, platform, critical, sg, context, mask, locked,
        ptmr, raw, i, ty, observed)
      which implies
      ptmr != 0 && ty == 100 && os_sched_ints(before) == 0 &&
      tmr_state_get_layout(sg, ptmr, field_addr(ptmr, OS_TMR, OSTmrType),
        field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) &&
      tmr_state_get_entry_facts(external, critical, sg, context, before,
        ptmr, raw, i, ty, raw_state, X) &&
      os_sched_lock_call_relation(critical, sg, os_sched_call_invocation(context),
        before, entry, locked) &&
      tmr_state_get_observation(raw, i, raw_state, locked, observed) &&
      os_sched_unlock_pre(external, platform, critical, sg, context, mask, locked) *
      tmr_state_get_raw_storage(ptmr, raw, ty, raw_state, before)
    */
    OSSchedUnlock()/*@ where external=external, platform=platform, critical=critical,
      sg=sg, context=context, mask=mask, before=locked */;
    return (state);
}
