/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSTmrSignal (void)

/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
    (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
    (region_entry before : UCOS2_Verify_State)
    Require time_tick_signal_entry(sg, before) && event_table_layout_prop(sg) &&
      &OSTmrSemSignal == g_OSTmrSemSignal(sg) &&
      time_tick_internal_addresses(sg, &OSIntNesting, &OSTCBPrioTbl, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
      time_tick_sched_owned(platform, critical, sg, invocation, origin, region_entry, before)
    Ensure exists (after : UCOS2_Verify_State),
      time_tick_sem_result(sg, time_tick_signal_pointer(before), before, __return, after) &&
      time_tick_sched_owned(platform, critical, sg, invocation, origin, region_entry, after)
*/
{
    INT8U  err;

    
    /*@ time_tick_signal_entry(sg, before) &&
      &OSTmrSemSignal == g_OSTmrSemSignal(sg) &&
      time_tick_sched_owned(platform, critical, sg, invocation, origin, region_entry, before)
      which implies time_tick_signal_entry(sg, before) &&
      &OSTmrSemSignal == g_OSTmrSemSignal(sg) &&
      interrupt_platform_running(platform, invocation, origin, 192) *
      critical_region_inside(critical, sg, invocation, region_entry) * unmap_table_rep(sg) *
      data_at(&OSTmrSemSignal, OS_EVENT *, time_tick_signal_pointer(before)) *
      time_tick_signal_read_frame(sg, before) */
    err = OSSemPost(OSTmrSemSignal) /*@ where (tick_signal_read) platform=platform, critical=critical, sg=sg, invocation=invocation, origin=origin, region_entry=region_entry, before=before */ ;
    return (err);
}
