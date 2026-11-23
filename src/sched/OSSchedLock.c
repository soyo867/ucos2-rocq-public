/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void OSSchedLock (void)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
         (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
         (mask : Z) (before : UCOS2_Verify_State)
         (X : UCOS2_Verify_State -> Prop)
    Require os_sched_lock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting) &&
      os_sched_lock_program_pre(platform, critical, sg, invocation, origin, mask, before, X)
    Ensure os_sched_lock_program_post(platform, critical, sg, invocation, origin, mask, before, X)
*/
{
#if OS_CRITICAL_METHOD == 3u
    OS_CPU_SR cpu_sr = 0u;
#endif

    /*@ os_sched_lock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting) &&
      os_sched_lock_program_pre(platform, critical, sg, invocation, origin, mask, before, X)
      which implies
      os_sched_lock_continuation(critical, sg, invocation, before, X) &&
      UCOS2_state_inv(sg, before) &&
      os_sched_lock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting) &&
      data_at(&OSRunning, unsigned char, os_sched_lock_running(before)) *
      os_sched_lock_outside_frame(platform, critical, sg, invocation, origin, mask, before)
    */
    if (OSRunning == OS_TRUE) {
        OS_ENTER_CRITICAL();
        /*@ exists entry,
          os_sched_lock_continuation(critical, sg, invocation, before, X) &&
          os_sched_lock_body_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          os_sched_lock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting) &&
          os_sched_lock_inside_frame(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          UCOS2_inv(sg, entry)
          which implies
          exists entry,
          os_sched_lock_continuation(critical, sg, invocation, before, X) &&
          os_sched_lock_body_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          0 <= os_sched_lock_locks(entry) && os_sched_lock_locks(entry) <= 255 &&
          os_sched_lock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting) &&
          os_sched_lock_inside_frame(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          data_at(&OSIntNesting, unsigned char, os_sched_lock_ints(entry)) *
          data_at(&OSLockNesting, unsigned char, os_sched_lock_locks(entry)) *
          UCOS2_raw_rep_missing_interrupt(sg, entry)
        */
        if (OSIntNesting == 0u) {
            if (OSLockNesting < 255u) {
                OSLockNesting++;
            }
        }
        /*@ Assert exists entry,
          os_sched_lock_continuation(critical, sg, invocation, before, X) &&
          os_sched_lock_body_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          os_sched_lock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting) &&
          os_sched_lock_inside_frame(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          data_at(&OSIntNesting, unsigned char, os_sched_lock_ints(entry)) *
          data_at(&OSLockNesting, unsigned char, os_sched_lock_updated_locks(entry)) *
          UCOS2_raw_rep_missing_interrupt(sg, entry)
        */
        /*@ exists entry,
          os_sched_lock_continuation(critical, sg, invocation, before, X) &&
          os_sched_lock_body_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          os_sched_lock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting) &&
          os_sched_lock_inside_frame(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          data_at(&OSIntNesting, unsigned char, os_sched_lock_ints(entry)) *
          data_at(&OSLockNesting, unsigned char, os_sched_lock_updated_locks(entry)) *
          UCOS2_raw_rep_missing_interrupt(sg, entry)
          which implies
          exists entry,
          os_sched_lock_continuation(critical, sg, invocation, before, X) &&
          os_sched_lock_body_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
          os_sched_lock_inside_frame(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          UCOS2_inv(sg, os_sched_lock_checkpoint(true, entry))
        */
        OS_EXIT_CRITICAL();
    }
}
