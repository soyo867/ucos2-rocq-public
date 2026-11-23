/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  *OSMboxAccept (OS_EVENT *pevent)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
    (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
    (mask: Z) (before: UCOS2_Verify_State) (eid: EventID) (pe: Z)
    (X: Z -> UCOS2_Verify_State -> Prop)
    Require pevent == pe && mbox_accept_profile(sg) &&
      mbox_accept_call_input(critical, sg, invocation, pe, before, eid) &&
      mbox_accept_safe(critical, sg, invocation, pe, before, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
    Ensure exists (after: UCOS2_Verify_State),
      mbox_accept_post(critical, sg, invocation, pe, before, __return, after) &&
      mbox_accept_return_safe(after, __return, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, after)
*/
{
    void      *pmsg;
#if OS_CRITICAL_METHOD == 3u                              /* Allocate storage for CPU status register  */
    OS_CPU_SR  cpu_sr = 0u;
#endif



#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {                        /* Validate 'pevent'                         */
        return ((void *)0);
    }
#endif
    /*@ pevent == pe && pevent != 0 && mbox_accept_profile(sg) &&
        mbox_accept_call_input(critical, sg, invocation, pe, before, eid) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
        which implies
        pevent == pe && pevent != 0 && pevent == event_addr(sg, eid) &&
        valid_event_id(sg, eid) && mbox_accept_profile(sg) && UCOS2_state_inv(sg, before) &&
        mbox_accept_call_input(critical, sg, invocation, pe, before, eid) &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        mbox_accept_type_frame(sg, before, eid) */
    /*@ 0 <= event_slot_type_value(EventState(before), eid) &&
        event_slot_type_value(EventState(before), eid) <= 255 by local */
    if (pevent->OSEventType != OS_EVENT_TYPE_MBOX) {      /* Validate event block type                 */
        /*@ pevent == pe && UCOS2_state_inv(sg, before) && mbox_accept_profile(sg) &&
            pevent == event_addr(sg, eid) &&
            data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
            mbox_accept_type_frame(sg, before, eid) *
            interrupt_platform_running(platform, invocation, origin, mask)
            which implies pevent == pe && pevent == event_addr(sg, eid) &&
            mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) */
        return ((void *)0);
    }
    /*@ pevent == pe && pevent != 0 && mbox_accept_profile(sg) && UCOS2_state_inv(sg, before) &&
        mbox_accept_call_input(critical, sg, invocation, pe, before, eid) &&
        pevent == event_addr(sg, eid) && event_slot_type_value(EventState(before), eid) == 1 &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&pevent->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        mbox_accept_type_frame(sg, before, eid)
        which implies pevent == pe && mbox_accept_profile(sg) &&
        mbox_accept_success_input(critical, sg, invocation, pe, before, eid) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) */
    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State),
        pevent == pe && mbox_accept_profile(sg) &&
        mbox_accept_success_input(critical, sg, invocation, pe, before, eid) &&
        critical_region_interval(critical, sg, invocation, before, entry) &&
        UCOS2_state_inv(sg, entry) && interrupt_saved_value(mask, cpu_sr) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry)
        which implies exists (entry: UCOS2_Verify_State) (observed current: OSEventAbstractState) (m: MboxFields),
        pevent == pe && pevent == event_addr(sg, eid) && mbox_accept_profile(sg) &&
        mbox_accept_message_frame(platform, critical, sg, invocation, origin, pe, mask, cpu_sr, before, entry, eid, observed, current, m) *
        data_at(&pevent->OSEventPtr, void *, mbox_message_ptr(m)) */
    pmsg               = pevent->OSEventPtr;
    pevent->OSEventPtr = (void *)0;                       /* Clear the mailbox                         */
    /*@ exists (entry: UCOS2_Verify_State) (observed current: OSEventAbstractState) (m: MboxFields),
        pevent == pe && pevent == event_addr(sg, eid) && mbox_accept_profile(sg) && pmsg == mbox_message_ptr(m) &&
        mbox_accept_message_frame(platform, critical, sg, invocation, origin, pe, mask, cpu_sr, before, entry, eid, observed, current, m) *
        data_at(&pevent->OSEventPtr, void *, 0)
        which implies exists (entry checkpoint: UCOS2_Verify_State),
        pevent == pe && mbox_accept_taken(critical, sg, invocation, pe, before, entry, checkpoint, pmsg) &&
        mbox_accept_cpu_restore_pre(platform, critical, sg, invocation, origin, mask, cpu_sr, entry, checkpoint) */
    OS_EXIT_CRITICAL();
    return (pmsg);                                        /* Return the message received (or NULL)     */
}
