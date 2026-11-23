/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSMboxQuery (OS_EVENT      *pevent,
                    OS_MBOX_DATA  *p_mbox_data)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
    (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
    (mask: Z) (before: UCOS2_Verify_State) (eid: EventID)
    (observed: OSEventAbstractState) (pe pd: addr) (caller_frame: Assertion)
    (X: Z -> option MboxQuerySnapshot -> UCOS2_Verify_State -> Prop)
    Require pevent == pe && p_mbox_data == pd &&
      coq_prop(mbox_query_call_input(critical, sg, invocation, pe, pd, before, eid, observed)) &&
      mbox_query_safe(critical, sg, invocation, eid, pe, pd, before, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) * caller_frame &&
      (pevent == 0 || (pevent != 0 && p_mbox_data == 0) ||
       (pevent != 0 && p_mbox_data != 0 && event_slot_type_value(EventState(before), eid) != 1 &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off) ||
       (pevent != 0 && p_mbox_data != 0 && event_slot_type_value(EventState(before), eid) == 1 &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
        coq_prop(mbox_query_layout(sg, eid, pd)) &&
        undef_data_at(&((OS_MBOX_DATA *)pd)->OSMsg, void *) *
        undef_data_at(&((OS_MBOX_DATA *)pd)->OSEventGrp, unsigned char) *
        UCharArray::undef_full(&((OS_MBOX_DATA *)pd)->OSEventTbl[0], 8)))
    Ensure mbox_query_api_post(platform, critical, sg, invocation, origin, mask,
      before, eid, pe, pd, __return, X) * caller_frame
*/
{
    INT8U       i;
    OS_PRIO    *psrc;
    OS_PRIO    *pdest;
#if OS_CRITICAL_METHOD == 3u                               /* Allocate storage for CPU status register */
    OS_CPU_SR   cpu_sr = 0u;
#endif



#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {                         /* Validate 'pevent'                        */
        return (OS_ERR_PEVENT_NULL);
    }
    if (p_mbox_data == (OS_MBOX_DATA *)0) {                /* Validate 'p_mbox_data'                   */
        return (OS_ERR_PDATA_NULL);
    }
#endif
    /*@ coq_prop(mbox_query_call_input(critical, sg, invocation, pe, pd, before, eid, observed)) &&
        pevent == pe && p_mbox_data == pd && pevent != 0 && p_mbox_data != 0 &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
        which implies
        pevent == pe && p_mbox_data == pd && pevent == event_addr(sg, eid) &&
        coq_prop(valid_event_id(sg, eid)) && coq_prop(UCOS2_state_inv(sg, before)) &&
        coq_prop(mbox_query_public_slot(before, eid, observed)) &&
        coq_prop(mbox_query_call_input(critical, sg, invocation, pe, pd, before, eid, observed)) &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        mbox_query_type_frame(sg, before, eid)
    */
    /*@ 0 <= event_slot_type_value(EventState(before), eid) && event_slot_type_value(EventState(before), eid) <= 255 by local */
    if (pevent->OSEventType != OS_EVENT_TYPE_MBOX) {       /* Validate event block type                */
        return (OS_ERR_EVENT_TYPE);
    }
    /*@ coq_prop(UCOS2_state_inv(sg, before)) && coq_prop(mbox_query_public_slot(before, eid, observed)) &&
        coq_prop(mbox_query_call_input(critical, sg, invocation, pe, pd, before, eid, observed)) &&
        pevent != 0 && p_mbox_data != 0 && pevent == pe && p_mbox_data == pd &&
        event_slot_type_value(EventState(before), eid) == 1 &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        mbox_query_type_frame(sg, before, eid)
        which implies
        coq_prop(mutex_query_handle_protocol(critical, sg, invocation, eid)) &&
        coq_prop(mutex_query_lookup(before, eid, observed)) && encode_event_type(eventType(observed)) == 1 &&
        pevent == pe && p_mbox_data == pd && pevent == event_addr(sg, eid) &&
        coq_prop(valid_event_id(sg, eid)) && coq_prop(UCOS2_state_inv(sg, before)) &&
        critical_region_outside(critical, sg, invocation, before)
    */
    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(mbox_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr, before, entry, observed, current)) &&
        coq_prop(mbox_query_layout(sg, eid, pd)) && pevent == pe && p_mbox_data == pd && pe == event_addr(sg, eid) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry) *
        undef_data_at(&((OS_MBOX_DATA *)pd)->OSEventGrp, unsigned char) *
        UCharArray::undef_full(&((OS_MBOX_DATA *)pd)->OSEventTbl[0], 8)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields)
          (pointer grp: Z) (rows: list Z),
        coq_prop(mbox_query_layout(sg, eid, pd)) && pevent == pe && p_mbox_data == pd && pe == event_addr(sg, eid) &&
        Zlength(rows) == 8 &&
        0 <= &((OS_EVENT *)pe)->OSEventTbl[0] && &((OS_EVENT *)pe)->OSEventTbl[0] + 8 <= 4294967295 &&
        0 <= &((OS_MBOX_DATA *)pd)->OSEventTbl[0] && &((OS_MBOX_DATA *)pd)->OSEventTbl[0] + 8 <= 4294967295 &&
        mbox_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, message, pointer, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, pointer) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) *
        store_osprio_array(&((OS_EVENT *)pe)->OSEventTbl[0], rows) *
        undef_data_at(&((OS_MBOX_DATA *)pd)->OSEventGrp, unsigned char) *
        UCharArray::undef_full(&((OS_MBOX_DATA *)pd)->OSEventTbl[0], 8)
    */
    /*@ Given entry current message pointer grp rows */
    p_mbox_data->OSEventGrp = pevent->OSEventGrp;          /* Copy message mailbox wait list           */
    psrc                    = &pevent->OSEventTbl[0];
    pdest                   = &p_mbox_data->OSEventTbl[0];
    /*@ UCharArray::undef_full(&p_mbox_data->OSEventTbl[0], 8)
        which implies mbox_query_output_table(&p_mbox_data->OSEventTbl[0], rows, 0) */
    /*@ Inv
        0 <= i && i <= 8 && Zlength(rows) == 8 &&
        coq_prop(mbox_query_layout(sg, eid, pd)) && pevent == pe && p_mbox_data == pd && pe == event_addr(sg, eid) &&
        0 <= &((OS_EVENT *)pe)->OSEventTbl[0] && &((OS_EVENT *)pe)->OSEventTbl[0] + 8 <= 4294967295 &&
        0 <= &((OS_MBOX_DATA *)pd)->OSEventTbl[0] && &((OS_MBOX_DATA *)pd)->OSEventTbl[0] + 8 <= 4294967295 &&
        psrc == &pevent->OSEventTbl[0] + i && pdest == &p_mbox_data->OSEventTbl[0] + i &&
        mbox_query_safe(critical, sg, invocation, eid, pe, pd, before, X) &&
        mbox_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, message, pointer, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, pointer) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) *
        store_osprio_array(&((OS_EVENT *)pe)->OSEventTbl[0], rows) *
        undef_data_at(&((OS_MBOX_DATA *)pd)->OSMsg, void *) *
        data_at(&((OS_MBOX_DATA *)pd)->OSEventGrp, unsigned char, grp) *
        mbox_query_output_table(&((OS_MBOX_DATA *)pd)->OSEventTbl[0], rows, i) * caller_frame
    */
    for (i = 0u; i < OS_EVENT_TBL_SIZE; i++) {
        /*@ 0 <= i && i < 8 && Zlength(rows) == 8 &&
            psrc == &pevent->OSEventTbl[0] + i && pdest == &p_mbox_data->OSEventTbl[0] + i &&
            store_osprio_array(&pevent->OSEventTbl[0], rows) *
            mbox_query_output_table(&p_mbox_data->OSEventTbl[0], rows, i)
            which implies Zlength(rows) == 8 &&
            psrc == &pevent->OSEventTbl[0] + i && pdest == &p_mbox_data->OSEventTbl[0] + i &&
            data_at(psrc, unsigned char, Znth(i, rows, 0)) *
            store_osprio_array_missing_i(&pevent->OSEventTbl[0], rows, i) *
            undef_data_at(pdest, unsigned char) *
            mbox_query_output_table_missing_i(&p_mbox_data->OSEventTbl[0], rows, i)
        */
        *pdest++ = *psrc++;
        /*@ 0 <= i && i < 8 && Zlength(rows) == 8 &&
            data_at(&pevent->OSEventTbl[i], unsigned char, Znth(i, rows, 0)) *
            store_osprio_array_missing_i(&pevent->OSEventTbl[0], rows, i) *
            data_at(&p_mbox_data->OSEventTbl[i], unsigned char, Znth(i, rows, 0)) *
            mbox_query_output_table_missing_i(&p_mbox_data->OSEventTbl[0], rows, i)
            which implies Zlength(rows) == 8 &&
            store_osprio_array(&pevent->OSEventTbl[0], rows) *
            mbox_query_output_table(&p_mbox_data->OSEventTbl[0], rows, i + 1)
        */
    }
    /*@ i >= 8 && i <= 8 && Zlength(rows) == 8 &&
        mbox_query_output_table(&p_mbox_data->OSEventTbl[0], rows, i)
        which implies i >= 8 && i <= 8 && Zlength(rows) == 8 &&
        store_osprio_array(&p_mbox_data->OSEventTbl[0], rows) */
    p_mbox_data->OSMsg = pevent->OSEventPtr;               /* Get message from mailbox                 */
    /*@
        pevent == pe && p_mbox_data == pd && pe == event_addr(sg, eid) && coq_prop(mbox_query_layout(sg, eid, pd)) &&
        mbox_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, message, pointer, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, pointer) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_EVENT *)pe)->OSEventTbl[0], rows) *
        data_at(&((OS_MBOX_DATA *)pd)->OSMsg, void *, pointer) *
        data_at(&((OS_MBOX_DATA *)pd)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_MBOX_DATA *)pd)->OSEventTbl[0], rows)
        which implies exists (snapshot: MboxQuerySnapshot),
        pevent == pe && p_mbox_data == pd &&
        coq_prop(mbox_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr, before, entry, observed, current)) &&
        coq_prop(mbox_query_critical(eid, entry, snapshot, entry)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry) *
        mbox_query_output_fields_rep(pd, snapshot)
    */
    OS_EXIT_CRITICAL();
    return (OS_ERR_NONE);
}
