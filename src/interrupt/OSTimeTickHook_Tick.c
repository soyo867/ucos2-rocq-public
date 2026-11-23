/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSTimeTickHook (void)

/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
    (application : TimeTickApplicationResources) (sg : StableGlobVars)
    (invocation : nat) (origin : TaskInvocationOrigin)
    (region_entry before : UCOS2_Verify_State) (app_value counter : Z)
    Require time_tick_entry(sg, invocation, origin, before) && 0 <= counter && counter <= 65535 &&
      &OSTmrSemSignal == g_OSTmrSemSignal(sg) &&
      time_tick_internal_addresses(sg, &OSIntNesting, &OSTCBPrioTbl, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
      time_tick_owned(platform, critical, time_tick_fixed_application(sg, application), sg,
        invocation, origin, region_entry, app_value, &OSTmrCtr, counter, before)
    Ensure time_tick_hook_isr_post(platform, critical, application, sg, invocation, origin,
      region_entry, before, app_value, &OSTmrCtr, counter)
*/
{
#if OS_APP_HOOKS_EN > 0u
    App_TimeTickHook() /*@ where sg=sg, state=before, frame=time_tick_owned(platform, critical, time_tick_fixed_application(sg, application), sg, invocation, origin, region_entry, app_value, &OSTmrCtr, counter, before) */ ;
#endif

#if OS_TMR_EN > 0u
    
    /*@ time_tick_entry(sg, invocation, origin, before) &&
      time_tick_owned(platform, critical, time_tick_fixed_application(sg, application), sg,
        invocation, origin, region_entry, app_value, &OSTmrCtr, counter, before)
      which implies time_tick_signal_entry(sg, before) && event_table_layout_prop(sg) &&
      time_tick_sched_owned(platform, critical, sg, invocation, origin, region_entry, before) *
      time_tick_application_own(application, app_value) * data_at(&OSTmrCtr, INT16U, counter) */
    OSTmrCtr++;

    /*@ data_at(&OSTmrCtr, INT16U, unsigned_last_nbits(counter + 1, 16))
      which implies data_at(&OSTmrCtr, INT16U, time_tick_hook_advanced(counter)) */
    if (OSTmrCtr >= (OS_TICKS_PER_SEC / OS_TMR_CFG_TICKS_PER_SEC)) {
        OSTmrCtr = 0u;
        
        /*@ Assert 10 <= time_tick_hook_advanced(counter) && time_tick_signal_entry(sg, before) &&
          event_table_layout_prop(sg) && &OSTmrSemSignal == g_OSTmrSemSignal(sg) &&
          time_tick_internal_addresses(sg, &OSIntNesting, &OSTCBPrioTbl, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
          time_tick_sched_owned(platform, critical, sg, invocation, origin, region_entry, before) *
          time_tick_application_own(application, app_value) * data_at(&OSTmrCtr, INT16U, 0) */
        OSTmrSignal() /*@ where platform=platform, critical=critical, sg=sg, invocation=invocation, origin=origin, region_entry=region_entry, before=before */ ;
        

        /*@ exists (error : Z) (after : UCOS2_Verify_State),
          10 <= time_tick_hook_advanced(counter) && event_table_layout_prop(sg) &&
          time_tick_sem_result(sg, time_tick_signal_pointer(before), before, error, after) &&
          time_tick_sched_owned(platform, critical, sg, invocation, origin, region_entry, after) *
          time_tick_application_own(application, app_value) * data_at(&OSTmrCtr, INT16U, 0)
          which implies time_tick_hook_isr_post(platform, critical, application, sg, invocation, origin,
            region_entry, before, app_value, &OSTmrCtr, counter) */

    }
#endif
}
