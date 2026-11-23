/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSTimeTickHook (void)
/*@ With (environment: TaskStackCallEnvironment) saved_local (critical: CriticalRegionResources)
    (sg: StableGlobVars) (caller: TaskResumeCaller) (mask: Z) (before: UCOS2_Verify_State)
    (eid: EventID) (observed: OSEventAbstractState) (counter: Z) X
    Require 0 <= counter && counter <= 65535 &&
      time_tick_hook_call_inputs(environment, critical, sg, caller, mask, counter, before, eid, observed) &&
      time_tick_hook_safe(environment, critical, sg, caller, mask, eid, counter, before, X) &&
      &OSTmrSemSignal == g_OSTmrSemSignal(sg) &&
      os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
        &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
      time_tick_hook_frame(environment, critical, saved_local, sg, caller, mask, &OSTmrCtr, counter, before)
    Ensure time_tick_hook_post(environment, critical, saved_local, sg, caller, mask, eid,
      &OSTmrCtr, counter, before, X)
*/
{
#if OS_APP_HOOKS_EN > 0u
    App_TimeTickHook() /*@ where sg=sg, state=before, frame=time_tick_hook_frame(environment, critical, saved_local, sg, caller, mask, &OSTmrCtr, counter, before) */;
#endif

#if OS_TMR_EN > 0u
    /*@ time_tick_hook_frame(environment, critical, saved_local, sg, caller, mask, &OSTmrCtr, counter, before)
        which implies
        q_post_closed(environment, critical, saved_local, sg, caller, mask, before) *
        data_at(&OSTmrCtr, unsigned short, counter) */
    OSTmrCtr++;

    if (OSTmrCtr >= (OS_TICKS_PER_SEC / OS_TMR_CFG_TICKS_PER_SEC)) {
        OSTmrCtr = 0u;
        /*@ 10 <= time_tick_hook_advanced(counter) &&
            time_tick_hook_call_inputs(environment, critical, sg, caller, mask, counter, before, eid, observed) &&
            time_tick_hook_safe(environment, critical, sg, caller, mask, eid, counter, before, X) &&
            q_post_closed(environment, critical, saved_local, sg, caller, mask, before) *
            data_at(&OSTmrCtr, unsigned short, 0)
            which implies
            tmr_signal_profile(sg) && UCOS2_state_inv(sg, before) &&
            sem_post_api_call_input(critical, sg, caller, tmr_signal_pointer(before), before, eid, observed) &&
            tmr_signal_optional_event_layout(sg, tmr_signal_pointer(before), eid) &&
            sem_post_api_schedule_protocol(environment, critical, sg, caller, mask, tmr_signal_pointer(before), eid, before) &&
            tmr_signal_safe(environment, critical, sg, caller, mask, eid, before, time_tick_hook_signal_continuation(X)) &&
            q_post_closed(environment, critical, saved_local, sg, caller, mask, before) *
            data_at(&OSTmrCtr, unsigned short, 0) */
        OSTmrSignal() /*@ where (tmr_signal_api) environment=environment, saved_local=saved_local, critical=critical, sg=sg, caller=caller, mask=mask, before=before, eid=eid, observed=observed, X=time_tick_hook_signal_continuation(X) */;
        /*@ 10 <= time_tick_hook_advanced(counter) &&
            (exists (error: Z),
              data_at(&OSTmrCtr, unsigned short, 0) *
              tmr_signal_post(environment, critical, saved_local, sg, caller, mask, eid,
                before, error, time_tick_hook_signal_continuation(X)))
            which implies
            time_tick_hook_post(environment, critical, saved_local, sg, caller, mask, eid,
              &OSTmrCtr, counter, before, X) */

    }
#endif
}
