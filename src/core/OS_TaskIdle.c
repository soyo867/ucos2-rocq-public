/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OS_TaskIdle (void *p_arg)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
    (hook: TaskIdleHookRelation) (sg: StableGlobVars)
    (invocation: nat) (origin: TaskInvocationOrigin)
    (initial_mask: Z) (initial: UCOS2_Verify_State)
    Require &OSIdleCtr == g_OSIdleCtr(sg) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, initial_mask, initial)
    Ensure 0 == 1
*/
{
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif

    (void)p_arg;                                 /* Prevent compiler warning for not using 'p_arg'     */
    /*@ Inv Assert exists (history: list TaskIdleIteration) (mask: Z) (before: UCOS2_Verify_State) (last_saved: Z),
        p_arg == p_arg@pre && cpu_sr == last_saved && &OSIdleCtr == g_OSIdleCtr(sg) &&
        task_idle_prefix(critical, hook, sg, invocation, origin, initial_mask, initial, history, mask, before) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) */
    for (; 1;) {
        /*@ Given history mask before last_saved */
        OS_ENTER_CRITICAL();
        /*@ exists (acquired: UCOS2_Verify_State),
            &OSIdleCtr == g_OSIdleCtr(sg) &&
            task_idle_prefix(critical, hook, sg, invocation, origin, initial_mask, initial, history, mask, before) &&
            critical_region_interval(critical, sg, invocation, before, acquired) &&
            UCOS2_state_inv(sg, acquired) && interrupt_saved_value(mask, cpu_sr) &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) * UCOS2_inv(sg, acquired)
            which implies exists (acquired: UCOS2_Verify_State),
            &OSIdleCtr == g_OSIdleCtr(sg) &&
            task_idle_store_frame(platform, critical, hook, sg, invocation, origin, initial_mask, initial, history, mask, cpu_sr, before, acquired) *
            data_at(&OSIdleCtr, unsigned int, task_idle_counter(acquired)) */
        /*@ Given acquired */
        OSIdleCtr++;
        /*@ &OSIdleCtr == g_OSIdleCtr(sg) &&
            task_idle_store_frame(platform, critical, hook, sg, invocation, origin, initial_mask, initial, history, mask, cpu_sr, before, acquired) *
            data_at(&OSIdleCtr, unsigned int, task_idle_counter_after(acquired))
            which implies exists (checkpoint: UCOS2_Verify_State),
            task_idle_written(critical, hook, sg, invocation, origin, initial_mask, initial, history, mask, cpu_sr, before, acquired, checkpoint) &&
            mbox_accept_cpu_restore_pre(platform, critical, sg, invocation, origin, mask, cpu_sr, acquired, checkpoint) */
        /*@ Given checkpoint */
        OS_EXIT_CRITICAL();
        /*@ Assert exists (saved: Z) (restored: UCOS2_Verify_State),
            p_arg == p_arg@pre && cpu_sr == saved && &OSIdleCtr == g_OSIdleCtr(sg) &&
            task_idle_written(critical, hook, sg, invocation, origin, initial_mask, initial, history, mask, saved, before, acquired, checkpoint) &&
            critical_region_interval(critical, sg, invocation, checkpoint, restored) &&
            mutex_query_closed(platform, critical, sg, invocation, origin, mask, restored) */
        /*@ Given saved restored */
        OSTaskIdleHook() /*@ where hook=hook */;  /* Call user definable HOOK                           */
        /*@ exists (next_mask: Z) (after: UCOS2_Verify_State),
            cpu_sr == saved &&
            task_idle_written(critical, hook, sg, invocation, origin, initial_mask, initial, history, mask, saved, before, acquired, checkpoint) &&
            critical_region_interval(critical, sg, invocation, checkpoint, restored) &&
            task_idle_hook_returns(hook, sg, invocation, origin, mask, restored, next_mask, after) &&
            mutex_query_closed(platform, critical, sg, invocation, origin, next_mask, after)
            which implies exists (extended: list TaskIdleIteration) (next_mask: Z) (after: UCOS2_Verify_State),
            cpu_sr == saved &&
            task_idle_prefix(critical, hook, sg, invocation, origin, initial_mask, initial, extended, next_mask, after) &&
            mutex_query_closed(platform, critical, sg, invocation, origin, next_mask, after) */
    }
}
