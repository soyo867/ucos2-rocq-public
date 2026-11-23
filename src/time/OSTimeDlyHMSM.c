/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSTimeDlyHMSM (INT8U   hours,
                      INT8U   minutes,
                      INT8U   seconds,
                      INT16U  ms)
/*@ With (X : Z -> UCOS2_Verify_State -> Prop)
         (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
         saved_local (sg : StableGlobVars) (caller : TaskSuspendCaller)
         (mask h m s millis : Z) (before : UCOS2_Verify_State) (frame : Assertion)
    Require hours == h && minutes == m && seconds == s && ms == millis &&
            task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            time_dly_hmsm_safe(environment, critical, sg, caller, mask, h, m, s, millis, before, X) &&
            time_dly_hmsm_call_pre(environment, critical, saved_local, sg, caller, mask, h, m, s, millis, before, frame)
    Ensure time_dly_hmsm_call_post(environment, critical, saved_local, sg, caller, mask, h, m, s, millis, before, __return, frame, X)
*/
{
    INT32U ticks;

    /*@ task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        time_dly_hmsm_call_pre(environment, critical, saved_local, sg, caller, mask, h, m, s, millis, before, frame)
        which implies
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        time_dly_hmsm_entry_facts(environment, critical, sg, caller, mask, h, m, s, millis, before) &&
        0 <= os_sched_ints(before) && os_sched_ints(before) <= 255 &&
        0 <= os_sched_locks(before) && os_sched_locks(before) <= 255 &&
        data_at(&OSIntNesting, unsigned char, os_sched_ints(before)) *
        data_at(&OSLockNesting, unsigned char, os_sched_locks(before)) *
        time_dly_prefix_frame(environment, saved_local, sg, caller, mask, before) * frame
    */
    if (OSIntNesting > 0u) {                     /* See if trying to call from an ISR                  */
        return (OS_ERR_TIME_DLY_ISR);
    }
    if (OSLockNesting > 0u) {                    /* See if called with scheduler locked                */
        return (OS_ERR_SCHED_LOCKED);
    }
    /*@ task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        data_at(&OSIntNesting, unsigned char, os_sched_ints(before)) *
        data_at(&OSLockNesting, unsigned char, os_sched_locks(before)) *
        time_dly_prefix_frame(environment, saved_local, sg, caller, mask, before)
        which implies
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        task_suspend_closed(environment, critical, saved_local, sg, caller, mask, before)
    */
#if OS_ARG_CHK_EN > 0u
    if (hours == 0u) {
        if (minutes == 0u) {
            if (seconds == 0u) {
                if (ms == 0u) {
                    return (OS_ERR_TIME_ZERO_DLY);
                }
            }
        }
    }
    if (minutes > 59u) {
        return (OS_ERR_TIME_INVALID_MINUTES);    /* Validate arguments to be within range              */
    }
    if (seconds > 59u) {
        return (OS_ERR_TIME_INVALID_SECONDS);
    }
    if (ms > 999u) {
        return (OS_ERR_TIME_INVALID_MS);
    }
#endif
                                                 /* Compute the total number of clock ticks required.. */
                                                 /* .. (rounded to the nearest tick)                   */
    /*@ Assert hours == h && minutes == m && seconds == s && ms == millis &&
        0 <= h && h <= 255 && 0 <= m && m <= 59 &&
        0 <= s && s <= 59 && 0 <= millis && millis <= 999 &&
        time_dly_hmsm_error(h, m, s, millis, before) == 0 &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        time_dly_hmsm_safe(environment, critical, sg, caller, mask, h, m, s, millis, before, X) &&
        time_dly_hmsm_entry_facts(environment, critical, sg, caller, mask, h, m, s, millis, before) &&
        task_suspend_closed(environment, critical, saved_local, sg, caller, mask, before) * frame *
        undef_data_at(&ticks, INT32U)
    */
    ticks = ((INT32U)hours * 3600uL + (INT32U)minutes * 60uL + (INT32U)seconds) * OS_TICKS_PER_SEC
          + OS_TICKS_PER_SEC * ((INT32U)ms + 500uL / OS_TICKS_PER_SEC) / 1000uL;
    /*@ Assert hours == h && minutes == m && seconds == s && ms == millis &&
        ticks == time_dly_hmsm_ticks(h, m, s, millis) &&
        time_dly_hmsm_error(h, m, s, millis, before) == 0 &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        time_dly_safe(environment, critical, sg, caller, mask, time_dly_hmsm_ticks(h, m, s, millis), before, time_dly_hmsm_delay_post(X)) &&
        time_dly_call_pre(environment, critical, saved_local, sg, caller, mask, time_dly_hmsm_ticks(h, m, s, millis), before, frame)
    */
    OSTimeDly(ticks) /*@ where X = time_dly_hmsm_delay_post(X),
        environment = environment, critical = critical, saved_local = saved_local,
        sg = sg, caller = caller, mask = mask, request = time_dly_hmsm_ticks(h, m, s, millis),
        before = before, frame = frame */;
    return (OS_ERR_NONE);
}
