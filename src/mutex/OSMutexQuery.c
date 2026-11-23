/* Single-function annotation carrier; compose before canonical QCP.
 * The environment retains the pinned headers, configuration and callees.
 * Formatting and documented frontend form match the checked C input.
 */

INT8U  OSMutexQuery (OS_EVENT       *pevent,
                     OS_MUTEX_DATA  *p_mutex_data)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
         (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
         (mask: Z) (before: UCOS2_Verify_State) (eid: EventID)
         (observed: OSEventAbstractState) (pe pd: addr) (isr: Z)
         (pcp_in prio_in val_in grp_pd_in: Z) (outL_in: list Z) X
    Require pevent == pe && p_mutex_data == pd &&
      isr == intNesting(before.IntrState) && isr >= 0 &&
      coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
      coq_prop(valid_stable_glob_vars(sg)) &&
      coq_prop(mutex_query_call_input(critical, sg, invocation, pe, pd, before, eid, observed)) &&
      safeExec(LastSeen(before), bind(atomic_cmd(mutex_query_return_program(critical, sg, invocation, pe, pd)),
                                    mutex_query_observe_error), X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) &&
      (isr > 0 ||
       (isr <= 0 && pevent == 0) ||
       (isr <= 0 && pevent != 0 && p_mutex_data == 0) ||
       (isr <= 0 && pevent != 0 && p_mutex_data != 0 &&
        encode_event_type(eventType(observed)) != 4 && coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0]))) ||
       (isr <= 0 && pevent != 0 && p_mutex_data != 0 &&
        encode_event_type(eventType(observed)) == 4 && coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
        data_at(&((OS_MUTEX_DATA *)pd)->OSMutexPCP, pcp_in) *
        data_at(&((OS_MUTEX_DATA *)pd)->OSOwnerPrio, prio_in) *
        data_at(&((OS_MUTEX_DATA *)pd)->OSValue, val_in) *
        data_at(&((OS_MUTEX_DATA *)pd)->OSEventGrp, grp_pd_in) *
        store_osprio_array(&((OS_MUTEX_DATA *)pd)->OSEventTbl[0], outL_in)))
    Ensure exists (after: UCOS2_Verify_State),
      coq_prop(mutex_query_return_post_prop(critical, sg, invocation, pe, pd, before, __return, after)) &&
      safeExec(LastSeen(after), return(__return), X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, after) &&
      (__return != 0 ||
       (__return == 0 && exists (current: OSEventAbstractState) (cnt grp: Z) (evtL: list Z),
        coq_prop(mutex_query_return_snapshot(critical, sg, invocation, pe, pd, before, after,
          eid, current, cnt, grp, evtL)) &&
        encode_event_type(eventType(current)) == 4 &&
        mutex_query_output_fields(pd, cnt, grp) *
        store_osprio_array(&((OS_MUTEX_DATA *)pd)->OSEventTbl[0], evtL)))
*/
{
    INT8U       i;
    OS_PRIO    *psrc;
    OS_PRIO    *pdest;
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR   cpu_sr = 0u;
#endif



    /*@ isr == intNesting(before.IntrState) &&
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
        which implies
        isr == intNesting(before.IntrState) &&
        coq_prop(UCOS2_state_inv(sg, before)) &&
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&OSIntNesting, unsigned char, isr) *
        interrupt_inv_no_int_nesting(sg, before.IntrState) *
        mutex_query_whole_frame(sg, before)
    */
    /*@ 0 <= isr && isr <= 255 by local */
    if (OSIntNesting > 0u) {                               /* See if called from ISR ...               */
        return (OS_ERR_QUERY_ISR);                         /* ... can't QUERY mutex from an ISR        */
    }
#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {                         /* Validate 'pevent'                        */
        return (OS_ERR_PEVENT_NULL);
    }
    if (p_mutex_data == (OS_MUTEX_DATA *)0) {              /* Validate 'p_mutex_data'                  */
        return (OS_ERR_PDATA_NULL);
    }
#endif
    /*@ isr == intNesting(before.IntrState) &&
        coq_prop(UCOS2_state_inv(sg, before)) &&
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
        data_at(&OSIntNesting, unsigned char, isr) *
        interrupt_inv_no_int_nesting(sg, before.IntrState) *
        mutex_query_whole_frame(sg, before)
        which implies
        isr == intNesting(before.IntrState) &&
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) && UCOS2_inv(sg, before)
    */
    /*@ coq_prop(mutex_query_call_input(critical, sg, invocation, pe, pd, before, eid, observed)) &&
        isr == intNesting(before.IntrState) && isr <= 0 &&
        pevent == pe && p_mutex_data == pd && pevent != 0 && p_mutex_data != 0 &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) && UCOS2_inv(sg, before)
        which implies
        isr == intNesting(before.IntrState) && isr <= 0 &&
        pevent == pe && p_mutex_data == pd && pevent == event_addr(sg, eid) &&
        coq_prop(valid_event_id(sg, eid)) &&
        coq_prop(UCOS2_state_inv(sg, before)) &&
        coq_prop(mutex_query_lookup(before, eid, observed)) &&
        coq_prop(mutex_query_call_input(critical, sg, invocation, pe, pd, before, eid, observed)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, encode_event_type(eventType(observed))) *
        mutex_query_type_frame(sg, before, eid, observed)
    */
    /*@ 0 <= encode_event_type(eventType(observed)) && encode_event_type(eventType(observed)) <= 255 by local */
    if (pevent->OSEventType != OS_EVENT_TYPE_MUTEX) {      /* Validate event block type                */
        return (OS_ERR_EVENT_TYPE);
    }
    /*@ coq_prop(UCOS2_state_inv(sg, before)) &&
        coq_prop(mutex_query_lookup(before, eid, observed)) &&
        coq_prop(mutex_query_call_input(critical, sg, invocation, pe, pd, before, eid, observed)) &&
        isr == intNesting(before.IntrState) && isr <= 0 &&
        pevent != 0 && p_mutex_data != 0 && pevent == pe && p_mutex_data == pd &&
        encode_event_type(eventType(observed)) == 4 &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, encode_event_type(eventType(observed))) *
        mutex_query_type_frame(sg, before, eid, observed)
        which implies
        coq_prop(mutex_query_handle_protocol(critical, sg, invocation, eid)) &&
        coq_prop(mutex_query_lookup(before, eid, observed)) &&
        encode_event_type(eventType(observed)) == 4 &&
        pevent == pe && p_mutex_data == pd && pevent == event_addr(sg, eid) &&
        coq_prop(valid_event_id(sg, eid)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) && UCOS2_inv(sg, before)
    */
    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(mutex_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) && coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
        pevent == pe && p_mutex_data == pd && pe == event_addr(sg, eid) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        coq_prop(mutex_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) &&
        coq_prop(mutex_query_copy_snapshot(entry, eid, current, cnt, grp, evtL)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
        pevent == pe && p_mutex_data == pd && pe == event_addr(sg, eid) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        interrupt_inv(sg, entry.IntrState) *
        mutex_query_raw_frame(sg, entry, eid) *
        mutex_query_event_unread(sg, entry.TskState, eid, current) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, 4) *
        data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * used_event_rest_no_type_cnt_ptr(sg, entry.TskState, pe, eid, current)
    */
    p_mutex_data->OSMutexPCP  = (INT8U)(pevent->OSEventCnt >> 8u);
    p_mutex_data->OSOwnerPrio = (INT8U)(pevent->OSEventCnt & OS_MUTEX_KEEP_LOWER_8);
    if (p_mutex_data->OSOwnerPrio == 0xFFu) {
        p_mutex_data->OSValue = OS_TRUE;
    } else {
        p_mutex_data->OSValue = OS_FALSE;
    }
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        coq_prop(mutex_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) &&
        coq_prop(mutex_query_copy_snapshot(entry, eid, current, cnt, grp, evtL)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
        pevent == pe && p_mutex_data == pd && pe == event_addr(sg, eid) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        interrupt_inv(sg, entry.IntrState) *
        mutex_query_raw_frame(sg, entry, eid) *
        mutex_query_event_unread(sg, entry.TskState, eid, current) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, 4) *
        data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * used_event_rest_no_type_cnt_ptr(sg, entry.TskState, pe, eid, current) *
        data_at(&((OS_MUTEX_DATA *)pd)->OSMutexPCP, unsigned char, decode_PCP_from_cnt(cnt)) *
        data_at(&((OS_MUTEX_DATA *)pd)->OSOwnerPrio, unsigned char, decode_OwnerPrio_from_cnt(cnt)) *
        data_at(&((OS_MUTEX_DATA *)pd)->OSValue, unsigned char, decode_OSValue_from_cnt(cnt))
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        coq_prop(mutex_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) &&
        coq_prop(mutex_query_copy_snapshot(entry, eid, current, cnt, grp, evtL)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
        pevent == pe && p_mutex_data == pd && pe == event_addr(sg, eid) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        interrupt_inv(sg, entry.IntrState) *
        mutex_query_raw_frame(sg, entry, eid) *
        mutex_query_event_unread(sg, entry.TskState, eid, current) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, 4) *
        data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * store_oseventtbl(sg, pe, evtL) *
        data_at(&((OS_MUTEX_DATA *)pd)->OSMutexPCP, unsigned char, decode_PCP_from_cnt(cnt)) *
        data_at(&((OS_MUTEX_DATA *)pd)->OSOwnerPrio, unsigned char, decode_OwnerPrio_from_cnt(cnt)) *
        data_at(&((OS_MUTEX_DATA *)pd)->OSValue, unsigned char, decode_OSValue_from_cnt(cnt))
    */
    p_mutex_data->OSEventGrp  = pevent->OSEventGrp;        /* Copy wait list                           */
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        coq_prop(mutex_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) &&
        coq_prop(mutex_query_copy_snapshot(entry, eid, current, cnt, grp, evtL)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
        pevent == pe && p_mutex_data == pd && pe == event_addr(sg, eid) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        interrupt_inv(sg, entry.IntrState) *
        mutex_query_raw_frame(sg, entry, eid) *
        mutex_query_event_unread(sg, entry.TskState, eid, current) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, 4) *
        data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * store_oseventtbl(sg, pe, evtL) *
        data_at(&((OS_MUTEX_DATA *)pd)->OSMutexPCP, unsigned char, decode_PCP_from_cnt(cnt)) *
        data_at(&((OS_MUTEX_DATA *)pd)->OSOwnerPrio, unsigned char, decode_OwnerPrio_from_cnt(cnt)) *
        data_at(&((OS_MUTEX_DATA *)pd)->OSValue, unsigned char, decode_OSValue_from_cnt(cnt)) * data_at(&((OS_MUTEX_DATA *)pd)->OSEventGrp, unsigned char, grp)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        pevent == pe && p_mutex_data == pd && pe == event_addr(sg, eid) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) && mutex_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * store_oseventtbl(sg, pe, evtL)
    */
    psrc                      = &pevent->OSEventTbl[0];
    pdest                     = &p_mutex_data->OSEventTbl[0];
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        mutex_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * store_oseventtbl(sg, pe, evtL) *
        store_osprio_array(&((OS_MUTEX_DATA *)pd)->OSEventTbl[0], outL_in)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        mutex_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * store_oseventtbl(sg, pe, evtL) *
        store_osprio_array(&((OS_MUTEX_DATA *)pd)->OSEventTbl[0], copy_prefix_list(evtL, outL_in, 0))
    */
    /*@ Inv exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        0 <= i && i <= 8 &&
        pevent == pe && p_mutex_data == pd && pe == event_addr(sg, eid) &&
        psrc == &pevent->OSEventTbl[0] + i &&
        pdest == &p_mutex_data->OSEventTbl[0] + i &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
        mutex_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * store_oseventtbl(sg, pe, evtL) * store_osprio_array(&((OS_MUTEX_DATA *)pd)->OSEventTbl[0], copy_prefix_list(evtL, outL_in, i))
    */
    for (i = 0u; i < OS_EVENT_TBL_SIZE; i++) {
        /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z) (psrc_v pdest_v: Z),
            0 <= i && i < 8 && pevent == pe && p_mutex_data == pd && pe == event_addr(sg, eid) &&
            psrc_v == &pevent->OSEventTbl[i] && pdest_v == &p_mutex_data->OSEventTbl[i] &&
            coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
            data_at(&psrc, unsigned char *, psrc_v) *
            data_at(&pdest, unsigned char *, pdest_v) *
            mutex_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * store_oseventtbl(sg, pe, evtL) * store_osprio_array(&((OS_MUTEX_DATA *)pd)->OSEventTbl[0], copy_prefix_list(evtL, outL_in, i))
            which implies
            exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z) (psrc_v pdest_v: Z),
            pevent == pe && p_mutex_data == pd && pe == event_addr(sg, eid) &&
            psrc_v == &pevent->OSEventTbl[i] && pdest_v == &p_mutex_data->OSEventTbl[i] && coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
            data_at(&psrc, unsigned char *, psrc_v) *
            data_at(&pdest, unsigned char *, pdest_v) *
            mutex_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * data_at(psrc_v, unsigned char, Znth(i, evtL, 0)) *
            store_oseventtbl_missing_i(sg, pe, evtL, i) *
            data_at(pdest_v, unsigned char, Znth(i, copy_prefix_list(evtL, outL_in, i), 0)) *
            store_osprio_array_missing_i(&((OS_MUTEX_DATA *)pd)->OSEventTbl[0], copy_prefix_list(evtL, outL_in, i), i)
        */
        *pdest = *psrc;
        pdest++;
        psrc++;
        /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z) (psrc_v pdest_v: Z),
            pevent == pe && p_mutex_data == pd && pe == event_addr(sg, eid) &&
            psrc_v == &pevent->OSEventTbl[i] && pdest_v == &p_mutex_data->OSEventTbl[i] && coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
            data_at(&psrc, unsigned char *, psrc_v + 1) *
            data_at(&pdest, unsigned char *, pdest_v + 1) *
            mutex_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * data_at(psrc_v, unsigned char, Znth(i, evtL, 0)) *
            store_oseventtbl_missing_i(sg, pe, evtL, i) *
            data_at(pdest_v, unsigned char, Znth(i, evtL, 0)) *
            store_osprio_array_missing_i(&((OS_MUTEX_DATA *)pd)->OSEventTbl[0], copy_prefix_list(evtL, outL_in, i), i)
            which implies
            exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z) (psrc_v pdest_v: Z),
            pevent == pe && p_mutex_data == pd && pe == event_addr(sg, eid) &&
            psrc_v == &pevent->OSEventTbl[i] && pdest_v == &p_mutex_data->OSEventTbl[i] && coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(mutex_query_event_wait_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
            data_at(&psrc, unsigned char *, psrc_v + 1) *
            data_at(&pdest, unsigned char *, pdest_v + 1) *
            mutex_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * store_oseventtbl(sg, pe, evtL) *
            store_osprio_array(&((OS_MUTEX_DATA *)pd)->OSEventTbl[0], copy_prefix_list(evtL, outL_in, i + 1))
        */
    }
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        pevent == pe && p_mutex_data == pd && pe == event_addr(sg, eid) &&
        mutex_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * store_oseventtbl(sg, pe, evtL) * store_osprio_array(&((OS_MUTEX_DATA *)pd)->OSEventTbl[0], copy_prefix_list(evtL, outL_in, i))
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        coq_prop(mutex_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) && coq_prop(mutex_query_copy_snapshot(entry, eid, current, cnt, grp, evtL)) &&
        pevent == pe && p_mutex_data == pd && pe == event_addr(sg, eid) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry) *
        mutex_query_output_fields(pd, cnt, grp) * store_osprio_array(&((OS_MUTEX_DATA *)pd)->OSEventTbl[0], copy_prefix_list(evtL, outL_in, i))
    */
    OS_EXIT_CRITICAL();
    return (OS_ERR_NONE);
}
