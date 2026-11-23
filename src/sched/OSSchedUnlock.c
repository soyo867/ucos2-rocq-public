/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void OSSchedUnlock (void)
/*@ With (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
         (critical : CriticalRegionResources) (sg : StableGlobVars)
         (context : OsSchedCallContext) (mask : Z) (before : UCOS2_Verify_State)
         (X : UCOS2_Verify_State -> Prop)
    Require os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            os_sched_unlock_program_pre(external, platform, critical, sg, context, mask, before, X)
    Ensure os_sched_unlock_program_post(external, platform, critical, sg, context, mask, before, X)
*/
{
#if OS_CRITICAL_METHOD == 3u
    OS_CPU_SR cpu_sr = 0u;
#endif

    /*@ os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        os_sched_unlock_program_pre(external, platform, critical, sg, context, mask, before, X)
        which implies
        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        os_sched_unlock_continuation(external, critical, sg, context, before, X) &&
        UCOS2_state_inv(sg, before) &&
        os_sched_unlock_acquire_safety(external, critical, sg, context, before) &&
        data_at(&OSRunning, unsigned char, os_sched_unlock_running(before)) *
        os_sched_unlock_observation_frame(external, platform, critical, sg, context, mask, before)
    */
    if (OSRunning == OS_TRUE) {
        OS_ENTER_CRITICAL();
        /*@ Assert exists (entry : UCOS2_Verify_State),
            os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            os_sched_unlock_continuation(external, critical, sg, context, before, X) &&
            os_sched_unlock_body_facts(external, critical, sg, context, mask, cpu_sr, before, entry) &&
            0 <= os_sched_ints(entry) && os_sched_ints(entry) <= 255 &&
            0 <= os_sched_locks(entry) && os_sched_locks(entry) <= 255 &&
            os_sched_unlock_inside_frame(external, platform, critical, sg, context, cpu_sr, entry) *
            data_at(&OSIntNesting, INT8U, os_sched_ints(entry)) *
            data_at(&OSLockNesting, INT8U, os_sched_locks(entry)) *
            UCOS2_raw_rep_missing_interrupt(sg, entry)
        */
        if (OSIntNesting == 0u) {
            if (OSLockNesting > 0u) {
                OSLockNesting--;
                /*@ Assert exists (entry : UCOS2_Verify_State),
                    os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
                      &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                      &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                    os_sched_unlock_continuation(external, critical, sg, context, before, X) &&
            os_sched_unlock_body_facts(external, critical, sg, context, mask, cpu_sr, before, entry) &&
                    os_sched_ints(entry) == 0 &&
                    0 < os_sched_locks(entry) && os_sched_locks(entry) <= 255 &&
                    os_sched_unlock_inside_frame(external, platform, critical, sg, context, cpu_sr, entry) *
                    data_at(&OSIntNesting, INT8U, os_sched_ints(entry)) *
                    data_at(&OSLockNesting, INT8U, os_sched_unlock_counted_locks(entry)) *
                    UCOS2_raw_rep_missing_interrupt(sg, entry)
                */
                if (OSLockNesting == 0u) {
                    /*@ Assert exists (entry : UCOS2_Verify_State),
                        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
                          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                        os_sched_unlock_continuation(external, critical, sg, context, before, X) &&
            os_sched_unlock_body_facts(external, critical, sg, context, mask, cpu_sr, before, entry) &&
                        os_sched_unlock_requests(entry) == true &&
                        os_sched_unlock_inside_frame(external, platform, critical, sg, context, cpu_sr, entry) *
                        UCOS2_inv(sg, os_sched_unlock_checkpoint(true, entry))
                    */
                    OS_EXIT_CRITICAL();
                    /*@ Assert exists (entry : UCOS2_Verify_State),
                        os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
                          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                        os_sched_unlock_continuation(external, critical, sg, context, before, X) &&
            os_sched_unlock_body_facts(external, critical, sg, context, mask, cpu_sr, before, entry) &&
                        os_sched_unlock_requests(entry) == true &&
                        os_sched_pre(external, platform, critical, sg, context, mask,
                          os_sched_unlock_checkpoint(true, entry))
                    */
                    OS_Sched();
                } else {
                    /*@ Assert exists (entry : UCOS2_Verify_State),
                        os_sched_unlock_continuation(external, critical, sg, context, before, X) &&
            os_sched_unlock_body_facts(external, critical, sg, context, mask, cpu_sr, before, entry) &&
                        os_sched_unlock_requests(entry) == false &&
                        os_sched_unlock_inside_frame(external, platform, critical, sg, context, cpu_sr, entry) *
                        UCOS2_inv(sg, os_sched_unlock_checkpoint(true, entry))
                    */
                    OS_EXIT_CRITICAL();
                }
            } else {
                /*@ Assert exists (entry : UCOS2_Verify_State),
                    os_sched_unlock_continuation(external, critical, sg, context, before, X) &&
            os_sched_unlock_body_facts(external, critical, sg, context, mask, cpu_sr, before, entry) &&
                    os_sched_unlock_requests(entry) == false &&
                    os_sched_unlock_inside_frame(external, platform, critical, sg, context, cpu_sr, entry) *
                    UCOS2_inv(sg, os_sched_unlock_checkpoint(true, entry))
                */
                OS_EXIT_CRITICAL();
            }
        } else {
            /*@ Assert exists (entry : UCOS2_Verify_State),
                os_sched_unlock_continuation(external, critical, sg, context, before, X) &&
            os_sched_unlock_body_facts(external, critical, sg, context, mask, cpu_sr, before, entry) &&
                os_sched_unlock_requests(entry) == false &&
                os_sched_unlock_inside_frame(external, platform, critical, sg, context, cpu_sr, entry) *
                UCOS2_inv(sg, os_sched_unlock_checkpoint(true, entry))
            */
            OS_EXIT_CRITICAL();
        }
    }
}
