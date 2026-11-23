/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSTimeSet (INT32U ticks)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
    (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
    (mask: Z) (before: UCOS2_Verify_State) (requested: Z)
    (X: unit -> UCOS2_Verify_State -> Prop)
    Require ticks == requested && &OSTime == g_OSTime(sg) &&
      time_set_safe(critical, sg, invocation, before, requested, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
    Ensure exists (after: UCOS2_Verify_State),
      time_set_post(critical, sg, invocation, before, requested, after) &&
      time_set_return_safe(after, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, after)
*/
{
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif



    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State),
        ticks == requested && &OSTime == g_OSTime(sg) &&
        critical_region_interval(critical, sg, invocation, before, entry) &&
        UCOS2_state_inv(sg, entry) && interrupt_saved_value(mask, cpu_sr) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry)
        which implies exists (entry: UCOS2_Verify_State),
        ticks == requested && &OSTime == g_OSTime(sg) &&
        time_set_store_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry) *
        data_at(&OSTime, unsigned int, time_get(entry)) */
    /*@ 0 <= ticks && ticks <= 4294967295 by local */
    OSTime = ticks;
    /*@ exists (entry: UCOS2_Verify_State),
        ticks == requested && &OSTime == g_OSTime(sg) && 0 <= ticks && ticks <= 4294967295 &&
        time_set_store_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry) *
        data_at(&OSTime, unsigned int, ticks)
        which implies exists (entry checkpoint: UCOS2_Verify_State),
        ticks == requested && time_set_written(critical, sg, invocation, before, entry, checkpoint, requested) &&
        mbox_accept_cpu_restore_pre(platform, critical, sg, invocation, origin, mask, cpu_sr, entry, checkpoint) */
    OS_EXIT_CRITICAL();
}
