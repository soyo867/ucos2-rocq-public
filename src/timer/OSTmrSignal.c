/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSTmrSignal (void)
/*@ With (environment: TaskStackCallEnvironment) saved_local (critical: CriticalRegionResources)
    (sg: StableGlobVars) (caller: TaskResumeCaller) (mask: Z) (before: UCOS2_Verify_State)
    (eid: EventID) (observed: OSEventAbstractState) X
    Require tmr_signal_profile(sg) && UCOS2_state_inv(sg, before) &&
      &OSTmrSemSignal == g_OSTmrSemSignal(sg) &&
      sem_post_api_call_input(critical, sg, caller, tmr_signal_pointer(before), before, eid, observed) &&
      tmr_signal_optional_event_layout(sg, tmr_signal_pointer(before), eid) &&
      sem_post_api_schedule_protocol(environment, critical, sg, caller, mask, tmr_signal_pointer(before), eid, before) &&
      tmr_signal_safe(environment, critical, sg, caller, mask, eid, before, X) &&
      os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
        &OSPrioCur, &OSTCBHighRdy, &OSTCBPrioTbl, &OSCtxSwCtr, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
      q_post_closed(environment, critical, saved_local, sg, caller, mask, before)
    Ensure tmr_signal_post(environment, critical, saved_local, sg, caller, mask, eid, before, __return, X)
*/
{
    INT8U  err;

    /*@ tmr_signal_profile(sg) && UCOS2_state_inv(sg, before) &&
        &OSTmrSemSignal == g_OSTmrSemSignal(sg) &&
        tmr_signal_safe(environment, critical, sg, caller, mask, eid, before, X) &&
        q_post_closed(environment, critical, saved_local, sg, caller, mask, before)
        which implies
        sem_post_profile(sg) && UCOS2_state_inv(sg, before) &&
        sem_post_api_safe(environment, critical, sg, caller, mask, tmr_signal_pointer(before), eid, before, X) &&
        data_at(&OSTmrSemSignal, OS_EVENT *, tmr_signal_pointer(before)) *
        tmr_signal_read_frame(environment, saved_local, sg, caller, mask, before) */
    err = OSSemPost(OSTmrSemSignal) /*@ where (tmr_signal_sem_post)
        environment = environment, saved_local = saved_local, critical = critical,
        sg = sg, caller = caller, mask = mask, before = before, eid = eid,
        observed = observed, X = X */;
    return (err);
}
