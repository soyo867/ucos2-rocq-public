/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT32U  OSTimeGet (void)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
    (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
    (mask: Z) (before: UCOS2_Verify_State) (caller_frame: Assertion)
    (X: Z -> UCOS2_Verify_State -> Prop)
    Require &OSTime == g_OSTime(sg) && time_get_safe(critical, sg, invocation, before, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) * caller_frame
    Ensure time_get_api_post(platform, critical, sg, invocation, origin, mask, before, __return, X) * caller_frame
*/
{
    INT32U     ticks;
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif



    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State),
        &OSTime == g_OSTime(sg) &&
        time_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry)
        which implies
        exists (entry: UCOS2_Verify_State),
        &OSTime == g_OSTime(sg) &&
        time_get_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
        0 <= time_get(entry) && time_get(entry) <= 4294967295 &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        data_at(&OSTime, unsigned int, time_get(entry)) * time_get_read_frame(sg, entry)
    */
    /*@ Given entry */
    ticks = OSTime;
    /*@ &OSTime == g_OSTime(sg) &&
        data_at(&OSTime, unsigned int, time_get(entry)) * time_get_read_frame(sg, entry)
        which implies UCOS2_inv(sg, entry)
    */
    OS_EXIT_CRITICAL();
    return (ticks);
}
