/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSTmrNameGet (OS_TMR   *ptmr,
                     INT8U   **pdest,
                     INT8U    *perr)
/*@ With (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
         (critical : CriticalRegionResources) (sg : StableGlobVars)
         (context : OsSchedCallContext) (mask : Z) (view : TmrNameGetView)
         (before : UCOS2_Verify_State) (p dest error_addr : Z)
         (old : option Z) (X : TmrNameGetPost)
    Require ptmr == p && pdest == dest && perr == error_addr &&
      tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) &&
      os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
      os_sched_lock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting) &&
      tmr_name_get_pre(external, platform, critical, sg, context, mask, view, p, dest, before, old, X) * task_name_get_output_cell(pdest, old) *
      undef_data_at(perr, INT8U)
    Ensure tmr_name_get_post(external, platform, critical, sg, context, mask, view, p, dest, error_addr, before, old, __return, X)
*/
{
    INT8U  len;


#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return (0u);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pdest == (INT8U **)0) {
        *perr = OS_ERR_TMR_INVALID_DEST;
        return (0u);
    }
    if (ptmr == (OS_TMR *)0) {
        *perr = OS_ERR_TMR_INVALID;
        return (0u);
    }
#endif
    /*@ p != 0 && dest != 0 && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && tmr_name_get_pre(external, platform, critical, sg, context, mask, view, p, dest, before, old, X)
        which implies
        p != 0 && dest != 0 && tmr_name_get_entry_facts(external, critical, sg, context, view, p, dest, before, old, X) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && data_at(field_addr(ptmr, OS_TMR, OSTmrType), INT8U, tmr_name_get_type(view, before)) * tmr_name_get_type_rest(external, platform, critical, sg, context, mask, view, p, dest, before)
    */
    if (ptmr->OSTmrType != OS_TMR_TYPE) {              /* Validate timer structure                                    */
        /*@ p != 0 && dest != 0 && tmr_name_get_type(view, before) != 100 && tmr_name_get_entry_facts(external, critical, sg, context, view, p, dest, before, old, X) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && data_at(field_addr(ptmr, OS_TMR, OSTmrType), INT8U, tmr_name_get_type(view, before)) * tmr_name_get_type_rest(external, platform, critical, sg, context, mask, view, p, dest, before)
        which implies
        p != 0 && dest != 0 && tmr_name_get_type(view, before) != 100 && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && tmr_name_get_pre(external, platform, critical, sg, context, mask, view, p, dest, before, old, X)
    */
        *perr = OS_ERR_TMR_INVALID_TYPE;
        return (0u);
    }
    /*@ p != 0 && dest != 0 && tmr_name_get_type(view, before) == 100 && tmr_name_get_entry_facts(external, critical, sg, context, view, p, dest, before, old, X) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && data_at(field_addr(ptmr, OS_TMR, OSTmrType), INT8U, tmr_name_get_type(view, before)) * tmr_name_get_type_rest(external, platform, critical, sg, context, mask, view, p, dest, before)
        which implies
        p != 0 && dest != 0 && tmr_name_get_type(view, before) == 100 && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && tmr_name_get_pre(external, platform, critical, sg, context, mask, view, p, dest, before, old, X)
    */
    /*@ tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && tmr_name_get_pre(external, platform, critical, sg, context, mask, view, p, dest, before, old, X)
        which implies
        tmr_name_get_entry_facts(external, critical, sg, context, view, p, dest, before, old, X) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && data_at(&OSIntNesting, INT8U, task_name_get_nesting(before)) * tmr_name_get_int_rest(external, platform, sg, context, mask, view, p, dest, before)
    */
    if (OSIntNesting > 0u) {                           /* See if trying to call from an ISR                           */
        /*@ task_name_get_nesting(before) > 0 && tmr_name_get_entry_facts(external, critical, sg, context, view, p, dest, before, old, X) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && data_at(&OSIntNesting, INT8U, task_name_get_nesting(before)) * tmr_name_get_int_rest(external, platform, sg, context, mask, view, p, dest, before)
        which implies
        task_name_get_nesting(before) > 0 && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && tmr_name_get_pre(external, platform, critical, sg, context, mask, view, p, dest, before, old, X)
    */
        *perr = OS_ERR_NAME_GET_ISR;
        return (0u);
    }
    /*@ task_name_get_nesting(before) == 0 && tmr_name_get_entry_facts(external, critical, sg, context, view, p, dest, before, old, X) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && data_at(&OSIntNesting, INT8U, task_name_get_nesting(before)) * tmr_name_get_int_rest(external, platform, sg, context, mask, view, p, dest, before)
        which implies
        task_name_get_nesting(before) == 0 && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && tmr_name_get_pre(external, platform, critical, sg, context, mask, view, p, dest, before, old, X)
    */
    /*@ p != 0 && dest != 0 && tmr_name_get_type(view, before) == 100 && task_name_get_nesting(before) == 0 && tmr_name_get_pre(external, platform, critical, sg, context, mask, view, p, dest, before, old, X)
        which implies
        task_name_get_nesting(before) == 0 && tmr_name_get_entry_facts(external, critical, sg, context, view, p, dest, before, old, X) && tmr_name_get_early_error(view, p, dest, before) == None &&
      os_sched_lock_pre(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, before) *
      tmr_name_get_continuation(external, sg, context) * tmr_name_get_private(view, p, dest, before)
    */
    OSSchedLock()/*@ where platform=platform, critical=critical, sg=sg, invocation=os_sched_call_invocation(context), origin=os_sched_call_origin(context), mask=mask, before=before */;
    /*@ task_name_get_nesting(before) == 0 && tmr_name_get_entry_facts(external, critical, sg, context, view, p, dest, before, old, X) && tmr_name_get_early_error(view, p, dest, before) == None &&
      os_sched_lock_post(platform, critical, sg, os_sched_call_invocation(context), os_sched_call_origin(context), mask, before) *
      tmr_name_get_continuation(external, sg, context) * tmr_name_get_private(view, p, dest, before)
        which implies
        exists locked, tmr_name_get_lock_facts(external, critical, sg, context, view, p, dest, before, old, X, locked) && tmr_name_get_locked(external, platform, critical, sg, context, mask, view, p, dest, before, locked)
    */
    /*@ Given locked */
    /*@ tmr_name_get_lock_facts(external, critical, sg, context, view, p, dest, before, old, X, locked) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && tmr_name_get_locked(external, platform, critical, sg, context, mask, view, p, dest, before, locked)
        which implies
        tmr_name_get_lock_facts(external, critical, sg, context, view, p, dest, before, old, X, locked) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && data_at(field_addr(ptmr, OS_TMR, OSTmrState), INT8U, tmr_name_get_state(view, locked)) * tmr_name_get_state_rest(external, platform, critical, sg, context, mask, view, p, dest, before, locked)
    */
    switch (ptmr->OSTmrState) {
        case OS_TMR_STATE_RUNNING:
        case OS_TMR_STATE_STOPPED:
        case OS_TMR_STATE_COMPLETED:
             /*@ tmr_name_get_successful(tmr_name_get_state(view, locked)) == true && tmr_name_get_lock_facts(external, critical, sg, context, view, p, dest, before, old, X, locked) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) &&
               data_at(field_addr(ptmr, OS_TMR, OSTmrState), INT8U, tmr_name_get_state(view, locked)) * tmr_name_get_state_rest(external, platform, critical, sg, context, mask, view, p, dest, before, locked) * task_name_get_output_cell(pdest, old)
        which implies
        exists chars previous,
               tmr_name_get_successful(tmr_name_get_state(view, locked)) == true && tmr_name_get_lock_facts(external, critical, sg, context, view, p, dest, before, old, X, locked) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) &&
               old == Some(previous) && tmr_name_get_name_readable(view, locked, chars) &&
               (tmr_name_get_name(view, locked) != 0 => readable_name(tmr_name_get_names(view, locked), tmr_name_get_name(view, locked), chars)) &&
               data_at(field_addr(ptmr, OS_TMR, OSTmrName), INT8U *, tmr_name_get_name(view, locked)) * tmr_name_get_name_rest(external, platform, critical, sg, context, mask, view, p, dest, before, locked) * data_at(pdest, INT8U *, previous)
    */
             /*@ Given chars previous */
             *pdest = ptmr->OSTmrName;
             /*@ tmr_name_get_lock_facts(external, critical, sg, context, view, p, dest, before, old, X, locked) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && tmr_name_get_successful(tmr_name_get_state(view, locked)) == true &&
               tmr_name_get_name_readable(view, locked, chars) && data_at(field_addr(ptmr, OS_TMR, OSTmrName), INT8U *, tmr_name_get_name(view, locked)) * tmr_name_get_name_rest(external, platform, critical, sg, context, mask, view, p, dest, before, locked)
        which implies
        tmr_name_get_lock_facts(external, critical, sg, context, view, p, dest, before, old, X, locked) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && tmr_name_get_successful(tmr_name_get_state(view, locked)) == true &&
               tmr_name_get_name_readable(view, locked, chars) &&
               tmr_name_get_strlen_pre(tmr_name_get_name(view, locked), tmr_name_get_name(view, locked), tmr_name_get_name(view, locked), tmr_name_get_names(view, locked), chars, tmr_name_get_strlen_frame(external, platform, critical, sg, context, mask, view, p, locked, chars))
    */
             len    = OS_StrLen(*pdest)/*@ where (source_spec) entry=tmr_name_get_name(view, locked), base=tmr_name_get_name(view, locked), names=tmr_name_get_names(view, locked), chars=chars, frame=tmr_name_get_strlen_frame(external, platform, critical, sg, context, mask, view, p, locked, chars) */;
             /*@ Assert tmr_name_get_lock_facts(external, critical, sg, context, view, p, dest, before, old, X, locked) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
               tmr_name_get_successful(tmr_name_get_state(view, locked)) == true &&
               tmr_name_get_name_readable(view, locked, chars) &&
               len == task_name_get_length(tmr_name_get_name(view, locked), chars) &&
               ptmr == p && pdest == dest && perr == error_addr &&
               task_name_get_name_bytes(tmr_name_get_name(view, locked), chars) * tmr_name_get_strlen_frame(external, platform, critical, sg, context, mask, view, p, locked, chars) *
               data_at(pdest, INT8U *, tmr_name_get_name(view, locked)) * undef_data_at(perr, INT8U)
             */
             /*@ tmr_name_get_lock_facts(external, critical, sg, context, view, p, dest, before, old, X, locked) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && tmr_name_get_successful(tmr_name_get_state(view, locked)) == true &&
               tmr_name_get_name_readable(view, locked, chars) &&
               task_name_get_name_bytes(tmr_name_get_name(view, locked), chars) * tmr_name_get_strlen_frame(external, platform, critical, sg, context, mask, view, p, locked, chars)
        which implies
        tmr_name_get_lock_facts(external, critical, sg, context, view, p, dest, before, old, X, locked) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && tmr_name_get_successful(tmr_name_get_state(view, locked)) == true &&
               tmr_name_get_name_readable(view, locked, chars) &&
               os_sched_unlock_pre(external, platform, critical, sg, context, mask, locked) * tmr_name_get_private(view, p, dest, before)
    */
             OSSchedUnlock()/*@ where external=external, platform=platform, critical=critical, sg=sg, context=context, mask=mask, before=locked */;
             *perr = OS_ERR_NONE;
             return (len);

        case OS_TMR_STATE_UNUSED:                      /* Timer is not allocated                                      */
             /*@ tmr_name_get_state(view, locked) == 0 && tmr_name_get_lock_facts(external, critical, sg, context, view, p, dest, before, old, X, locked) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && data_at(field_addr(ptmr, OS_TMR, OSTmrState), INT8U, tmr_name_get_state(view, locked)) * tmr_name_get_state_rest(external, platform, critical, sg, context, mask, view, p, dest, before, locked)
        which implies
        tmr_name_get_state(view, locked) == 0 && tmr_name_get_lock_facts(external, critical, sg, context, view, p, dest, before, old, X, locked) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && os_sched_unlock_pre(external, platform, critical, sg, context, mask, locked) * tmr_name_get_private(view, p, dest, before)
    */
             OSSchedUnlock()/*@ where external=external, platform=platform, critical=critical, sg=sg, context=context, mask=mask, before=locked */;
             *perr = OS_ERR_TMR_INACTIVE;
             return (0u);

        default:
             /*@ tmr_name_get_state(view, locked) != 0 && tmr_name_get_state(view, locked) != 1 && tmr_name_get_state(view, locked) != 2 && tmr_name_get_state(view, locked) != 3 && tmr_name_get_lock_facts(external, critical, sg, context, view, p, dest, before, old, X, locked) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && data_at(field_addr(ptmr, OS_TMR, OSTmrState), INT8U, tmr_name_get_state(view, locked)) * tmr_name_get_state_rest(external, platform, critical, sg, context, mask, view, p, dest, before, locked)
        which implies
        tmr_name_get_state(view, locked) != 0 && tmr_name_get_state(view, locked) != 1 && tmr_name_get_state(view, locked) != 2 && tmr_name_get_state(view, locked) != 3 && tmr_name_get_lock_facts(external, critical, sg, context, view, p, dest, before, old, X, locked) && tmr_name_get_layout(sg, p, field_addr(ptmr, OS_TMR, OSTmrType), field_addr(ptmr, OS_TMR, OSTmrName), field_addr(ptmr, OS_TMR, OSTmrState), &OSIntNesting) && os_sched_unlock_pre(external, platform, critical, sg, context, mask, locked) * tmr_name_get_private(view, p, dest, before)
    */
             OSSchedUnlock()/*@ where external=external, platform=platform, critical=critical, sg=sg, context=context, mask=mask, before=locked */;
             *perr = OS_ERR_TMR_INVALID_STATE;
             return (0u);
    }
}
