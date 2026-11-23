/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSStatInit (void)
/*@ With (X : unit -> UCOS2_Verify_State -> Prop)
         (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
         saved_local (sg : StableGlobVars) (original : TaskSuspendCaller)
         (mask : Z) (initial : UCOS2_Verify_State) (frame : Assertion)
    Require stat_init_config(sg) &&
        stat_init_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSStatRdy) &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        stat_init_phase_facts(environment, critical, sg, original, mask, initial, false, original, initial, X) &&
        task_suspend_closed(environment, critical, saved_local, sg, original, mask, initial) * frame
    Ensure stat_init_call_post(environment, critical, saved_local, sg, original, mask, initial, frame, X)
*/
{
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif



    /*@ stat_init_phase_facts(environment, critical, sg, original, mask, initial, false, original, initial, X) &&
        task_suspend_closed(environment, critical, saved_local, sg, original, mask, initial) * frame
        which implies
        stat_init_phase_facts(environment, critical, sg, original, mask, initial, false, original, initial, X) &&
        time_dly_safe(environment, critical, sg, original, mask, 2, initial, stat_init_delay_continuation(environment, critical, sg, original, mask, false, initial, X)) &&
        time_dly_call_pre(environment, critical, saved_local, sg, original, mask, 2, initial, frame)
    */
    OSTimeDly(2u) /*@ where X = stat_init_delay_continuation(environment, critical, sg, original, mask, false, initial, X) */;
    /*@ Assert exists (delayed1 : TaskSuspendCaller) (after_delay1 : UCOS2_Verify_State),
        stat_init_config(sg) &&
        stat_init_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSStatRdy) &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        stat_init_delayed_facts(environment, critical, sg, original, mask, initial, false, original, initial, delayed1, after_delay1, X) &&
        cpu_sr == 0 &&
        task_suspend_closed(environment, critical, saved_local, sg, delayed1, mask, after_delay1) * frame
        
    */
    /*@ Given delayed1 after_delay1 */
                               /* Synchronize with clock tick                        */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (active1 : TaskSuspendCaller) (acquired1 : UCOS2_Verify_State),
        stat_init_config(sg) &&
        stat_init_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSStatRdy) &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        stat_init_acquired_facts(environment, critical, sg, original, mask, initial, false, original, initial, delayed1, after_delay1, active1, cpu_sr, acquired1, X) &&
        data_at(&OSIdleCtr, unsigned int, idleCtr(StatsState(acquired1))) *
        stat_init_reset_residual(sg, StatsState(acquired1)) * stat_init_statistics_frame(environment, critical, saved_local, sg, active1, cpu_sr, acquired1) * frame
    */
    /*@ Given active1 acquired1 */

    OSIdleCtr    = 0uL;                          /* Clear idle counter                                 */
    /*@ Assert stat_init_config(sg) &&
        stat_init_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSStatRdy) &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        stat_init_acquired_facts(environment, critical, sg, original, mask, initial, false, original, initial, delayed1, after_delay1, active1, cpu_sr, acquired1, X) &&
        task_suspend_masked(environment, critical, saved_local, sg, active1, cpu_sr, acquired1,
          stat_init_update(false, acquired1)) * frame
    */
    OS_EXIT_CRITICAL();
    /*@ Assert exists (caller2 : TaskSuspendCaller) (before2 : UCOS2_Verify_State),
        stat_init_config(sg) &&
        stat_init_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSStatRdy) &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        stat_init_phase_facts(environment, critical, sg, original, mask, initial, true, caller2, before2, X) &&
        task_suspend_closed(environment, critical, saved_local, sg, caller2, mask, before2) * frame * undef_data_at(&cpu_sr, OS_CPU_SR)
    */
    /*@ Given caller2 before2 */

    /*@ stat_init_phase_facts(environment, critical, sg, original, mask, initial, true, caller2, before2, X) &&
        task_suspend_closed(environment, critical, saved_local, sg, caller2, mask, before2) * frame
        which implies
        stat_init_phase_facts(environment, critical, sg, original, mask, initial, true, caller2, before2, X) &&
        time_dly_safe(environment, critical, sg, caller2, mask, 10, before2, stat_init_delay_continuation(environment, critical, sg, caller2, mask, true, before2, X)) &&
        time_dly_call_pre(environment, critical, saved_local, sg, caller2, mask, 10, before2, frame)
    */
    OSTimeDly(OS_TICKS_PER_SEC / 10u) /*@ where X = stat_init_delay_continuation(environment, critical, sg, caller2, mask, true, before2, X), request = 10 */;
    /*@ Assert exists (delayed2 : TaskSuspendCaller) (after_delay2 : UCOS2_Verify_State),
        stat_init_config(sg) &&
        stat_init_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSStatRdy) &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        stat_init_delayed_facts(environment, critical, sg, original, mask, initial, true, caller2, before2, delayed2, after_delay2, X) &&
        
        task_suspend_closed(environment, critical, saved_local, sg, delayed2, mask, after_delay2) * frame
        * undef_data_at(&cpu_sr, OS_CPU_SR)
    */
    /*@ Given delayed2 after_delay2 */
           /* Determine MAX. idle counter value for 1/10 second  */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (active2 : TaskSuspendCaller) (acquired2 : UCOS2_Verify_State),
        stat_init_config(sg) &&
        stat_init_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSStatRdy) &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        stat_init_acquired_facts(environment, critical, sg, original, mask, initial, true, caller2, before2, delayed2, after_delay2, active2, cpu_sr, acquired2, X) &&
        data_at(&OSIdleCtr, unsigned int, idleCtr(StatsState(acquired2))) *
        data_at(&OSIdleCtrMax, unsigned int, idleCtrMax(StatsState(acquired2))) *
        data_at(&OSStatRdy, unsigned char, stat_init_ready_byte(StatsState(acquired2))) *
        stat_init_calibration_residual(sg, StatsState(acquired2)) * stat_init_statistics_frame(environment, critical, saved_local, sg, active2, cpu_sr, acquired2) * frame
    */
    /*@ Given active2 acquired2 */

    OSIdleCtrMax = OSIdleCtr;                    /* Store maximum idle counter count in 1/10 second    */
    OSStatRdy    = OS_TRUE;
    /*@ Assert stat_init_config(sg) &&
        stat_init_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSStatRdy) &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        stat_init_acquired_facts(environment, critical, sg, original, mask, initial, true, caller2, before2, delayed2, after_delay2, active2, cpu_sr, acquired2, X) &&
        task_suspend_masked(environment, critical, saved_local, sg, active2, cpu_sr, acquired2,
          stat_init_update(true, acquired2)) * frame
    */
    OS_EXIT_CRITICAL();
    /*@ Assert stat_init_call_post(environment, critical, saved_local, sg, original, mask, initial, frame, X) *
        undef_data_at(&cpu_sr, OS_CPU_SR)
    */

}
