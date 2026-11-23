/* Annotation-only carrier of pinned V2.93.01 Source/os_sem.c.
 * Original headers/configuration and explicit overlays are the actual input.
 */
INT8U OSSemQuery(OS_EVENT *pevent, OS_SEM_DATA *p_sem_data)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
         (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
         (mask: Z) (before: UCOS2_Verify_State) (eid: EventID)
         (observed: OSEventAbstractState) (pe pd: addr)
         (X: Z -> option SemQuerySnapshot -> UCOS2_Verify_State -> Prop)
    Require pevent == pe && p_sem_data == pd &&
      coq_prop(sem_query_call_input(critical, sg, invocation, pe, pd, before, eid, observed)) &&
      sem_query_source_api_safe(critical, sg, invocation, eid, pe, pd, before, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) &&
      (pevent == 0 ||
       (pevent != 0 && p_sem_data == 0) ||
       (pevent != 0 && p_sem_data != 0 &&
        event_slot_type_value(before.EventState, eid) != 3 &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off) ||
       (pevent != 0 && p_sem_data != 0 &&
        event_slot_type_value(before.EventState, eid) == 3 &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(event_wait_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
        undef_data_at(&((OS_SEM_DATA *)pd)->OSCnt, unsigned short) *
        undef_data_at(&((OS_SEM_DATA *)pd)->OSEventGrp, unsigned char) *
        UCharArray::undef_full(&((OS_SEM_DATA *)pd)->OSEventTbl[0], 8)))
    Ensure sem_query_source_api_post(platform, critical, sg, invocation, origin, mask,
      before, eid, pe, pd, __return, X)
*/
{
    INT8U       i;
    OS_PRIO    *psrc;
    OS_PRIO    *pdest;
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR   cpu_sr = 0u;
#endif



#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {                         /* Validate 'pevent'                        */
        return (OS_ERR_PEVENT_NULL);
    }
    if (p_sem_data == (OS_SEM_DATA *)0) {              /* Validate 'p_sem_data'                  */
        return (OS_ERR_PDATA_NULL);
    }
#endif
    /*@ coq_prop(sem_query_call_input(critical, sg, invocation, pe, pd, before, eid, observed)) &&
        pevent == pe && p_sem_data == pd && pevent != 0 && p_sem_data != 0 &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
        which implies
        pevent == pe && p_sem_data == pd && pevent == event_addr(sg, eid) &&
        coq_prop(valid_event_id(sg, eid)) &&
        coq_prop(UCOS2_state_inv(sg, before)) &&
        coq_prop(sem_query_public_slot(before, eid, observed)) &&
        coq_prop(sem_query_call_input(critical, sg, invocation, pe, pd, before, eid, observed)) &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(before.EventState, eid)) *
        sem_query_type_frame(sg, before, eid)
    */
    /*@ 0 <= event_slot_type_value(before.EventState, eid) && event_slot_type_value(before.EventState, eid) <= 255 by local */
    if (pevent->OSEventType != OS_EVENT_TYPE_SEM) {      /* Validate event block type                */
        return (OS_ERR_EVENT_TYPE);
    }
    /*@ coq_prop(UCOS2_state_inv(sg, before)) &&
        coq_prop(sem_query_public_slot(before, eid, observed)) &&
        coq_prop(sem_query_call_input(critical, sg, invocation, pe, pd, before, eid, observed)) &&
        pevent != 0 && p_sem_data != 0 && pevent == pe && p_sem_data == pd &&
        event_slot_type_value(before.EventState, eid) == 3 &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(before.EventState, eid)) *
        sem_query_type_frame(sg, before, eid)
        which implies
        coq_prop(mutex_query_handle_protocol(critical, sg, invocation, eid)) &&
        coq_prop(mutex_query_lookup(before, eid, observed)) &&
        encode_event_type(eventType(observed)) == 3 &&
        pevent == pe && p_sem_data == pd && pevent == event_addr(sg, eid) &&
        coq_prop(valid_event_id(sg, eid)) &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off && UCOS2_inv(sg, before)
    */
    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(sem_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) && coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(event_wait_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
        pevent == pe && p_sem_data == pd && pe == event_addr(sg, eid) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        coq_prop(sem_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) &&
        coq_prop(mutex_query_copy_snapshot(entry, eid, current, cnt, grp, evtL)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(event_wait_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
        pevent == pe && p_sem_data == pd && pe == event_addr(sg, eid) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        interrupt_inv(sg, entry.IntrState) *
        mutex_query_raw_frame(sg, entry, eid) *
        mutex_query_event_unread(sg, entry.TskState, eid, current) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, 3) *
        data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * used_event_rest_no_type_cnt_ptr(sg, entry.TskState, pe, eid, current)
    */
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        coq_prop(sem_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) &&
        coq_prop(mutex_query_copy_snapshot(entry, eid, current, cnt, grp, evtL)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(event_wait_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
        pevent == pe && p_sem_data == pd && pe == event_addr(sg, eid) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        interrupt_inv(sg, entry.IntrState) *
        mutex_query_raw_frame(sg, entry, eid) *
        mutex_query_event_unread(sg, entry.TskState, eid, current) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, 3) *
        data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * used_event_rest_no_type_cnt_ptr(sg, entry.TskState, pe, eid, current) *
        undef_data_at(&((OS_SEM_DATA *)pd)->OSCnt, unsigned short)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        coq_prop(sem_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) &&
        coq_prop(mutex_query_copy_snapshot(entry, eid, current, cnt, grp, evtL)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(event_wait_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
        pevent == pe && p_sem_data == pd && pe == event_addr(sg, eid) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        interrupt_inv(sg, entry.IntrState) *
        mutex_query_raw_frame(sg, entry, eid) *
        mutex_query_event_unread(sg, entry.TskState, eid, current) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, 3) *
        data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * store_oseventtbl(sg, pe, evtL) *
        undef_data_at(&((OS_SEM_DATA *)pd)->OSCnt, unsigned short)
    */
    p_sem_data->OSEventGrp  = pevent->OSEventGrp;        /* Copy wait list                           */
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        coq_prop(sem_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) &&
        coq_prop(mutex_query_copy_snapshot(entry, eid, current, cnt, grp, evtL)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(event_wait_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
        pevent == pe && p_sem_data == pd && pe == event_addr(sg, eid) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        interrupt_inv(sg, entry.IntrState) *
        mutex_query_raw_frame(sg, entry, eid) *
        mutex_query_event_unread(sg, entry.TskState, eid, current) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, 3) *
        data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * store_oseventtbl(sg, pe, evtL) *
        undef_data_at(&((OS_SEM_DATA *)pd)->OSCnt, unsigned short) * data_at(&((OS_SEM_DATA *)pd)->OSEventGrp, unsigned char, grp)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        pevent == pe && p_sem_data == pd && pe == event_addr(sg, eid) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(event_wait_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) && sem_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * undef_data_at(&((OS_SEM_DATA *)pd)->OSCnt, unsigned short) * store_oseventtbl(sg, pe, evtL)
    */
    psrc                      = &pevent->OSEventTbl[0];
    pdest                     = &p_sem_data->OSEventTbl[0];
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        sem_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * undef_data_at(&((OS_SEM_DATA *)pd)->OSCnt, unsigned short) * store_oseventtbl(sg, pe, evtL) *
        UCharArray::undef_full(&((OS_SEM_DATA *)pd)->OSEventTbl[0], 8)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        sem_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * undef_data_at(&((OS_SEM_DATA *)pd)->OSCnt, unsigned short) * store_oseventtbl(sg, pe, evtL) *
        sem_query_output_table(&((OS_SEM_DATA *)pd)->OSEventTbl[0], evtL, 0)
    */
    /*@ Inv exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        0 <= i && i <= 8 &&
        pevent == pe && p_sem_data == pd && pe == event_addr(sg, eid) &&
        psrc == &pevent->OSEventTbl[0] + i &&
        pdest == &p_sem_data->OSEventTbl[0] + i &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(event_wait_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
        sem_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * undef_data_at(&((OS_SEM_DATA *)pd)->OSCnt, unsigned short) * store_oseventtbl(sg, pe, evtL) * sem_query_output_table(&((OS_SEM_DATA *)pd)->OSEventTbl[0], evtL, i)
    */
    for (i = 0u; i < OS_EVENT_TBL_SIZE; i++) {
        /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z) (psrc_v pdest_v: Z),
            0 <= i && i < 8 && pevent == pe && p_sem_data == pd && pe == event_addr(sg, eid) &&
            psrc_v == &pevent->OSEventTbl[i] && pdest_v == &p_sem_data->OSEventTbl[i] &&
            coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(event_wait_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
            data_at(&psrc, unsigned char *, psrc_v) *
            data_at(&pdest, unsigned char *, pdest_v) *
            sem_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * undef_data_at(&((OS_SEM_DATA *)pd)->OSCnt, unsigned short) * store_oseventtbl(sg, pe, evtL) * sem_query_output_table(&((OS_SEM_DATA *)pd)->OSEventTbl[0], evtL, i)
            which implies
            exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z) (psrc_v pdest_v: Z),
            pevent == pe && p_sem_data == pd && pe == event_addr(sg, eid) &&
            psrc_v == &pevent->OSEventTbl[i] && pdest_v == &p_sem_data->OSEventTbl[i] && coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(event_wait_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
            data_at(&psrc, unsigned char *, psrc_v) *
            data_at(&pdest, unsigned char *, pdest_v) *
            sem_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * undef_data_at(&((OS_SEM_DATA *)pd)->OSCnt, unsigned short) * data_at(psrc_v, unsigned char, Znth(i, evtL, 0)) *
            store_oseventtbl_missing_i(sg, pe, evtL, i) *
            undef_data_at(pdest_v, unsigned char) *
            sem_query_output_table_missing_i(&((OS_SEM_DATA *)pd)->OSEventTbl[0], evtL, i)
        */
        *pdest++ = *psrc++;
        /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z) (psrc_v pdest_v: Z),
            pevent == pe && p_sem_data == pd && pe == event_addr(sg, eid) &&
            psrc_v == &pevent->OSEventTbl[i] && pdest_v == &p_sem_data->OSEventTbl[i] && coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(event_wait_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
            data_at(&psrc, unsigned char *, psrc_v + 1) *
            data_at(&pdest, unsigned char *, pdest_v + 1) *
            sem_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * undef_data_at(&((OS_SEM_DATA *)pd)->OSCnt, unsigned short) * data_at(psrc_v, unsigned char, Znth(i, evtL, 0)) *
            store_oseventtbl_missing_i(sg, pe, evtL, i) *
            data_at(pdest_v, unsigned char, Znth(i, evtL, 0)) *
            sem_query_output_table_missing_i(&((OS_SEM_DATA *)pd)->OSEventTbl[0], evtL, i)
            which implies
            exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z) (psrc_v pdest_v: Z),
            pevent == pe && p_sem_data == pd && pe == event_addr(sg, eid) &&
            psrc_v == &pevent->OSEventTbl[i] && pdest_v == &p_sem_data->OSEventTbl[i] && coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        coq_prop(event_wait_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventGrp, &((OS_EVENT *)pe)->OSEventTbl[0])) &&
            data_at(&psrc, unsigned char *, psrc_v + 1) *
            data_at(&pdest, unsigned char *, pdest_v + 1) *
            sem_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * undef_data_at(&((OS_SEM_DATA *)pd)->OSCnt, unsigned short) * store_oseventtbl(sg, pe, evtL) *
            sem_query_output_table(&((OS_SEM_DATA *)pd)->OSEventTbl[0], evtL, i + 1)
        */
    }
    p_sem_data->OSCnt = pevent->OSEventCnt;
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        pevent == pe && p_sem_data == pd && pe == event_addr(sg, eid) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        sem_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, eid, observed, current, pd, cnt, grp, evtL) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, cnt) * data_at(&((OS_SEM_DATA *)pd)->OSCnt, unsigned short, cnt) * store_oseventtbl(sg, pe, evtL) * sem_query_output_table(&((OS_SEM_DATA *)pd)->OSEventTbl[0], evtL, i)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState)
        (cnt grp: Z) (evtL: list Z),
        coq_prop(sem_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) && coq_prop(mutex_query_copy_snapshot(entry, eid, current, cnt, grp, evtL)) &&
        pevent == pe && p_sem_data == pd && pe == event_addr(sg, eid) &&
        sem_query_source_api_restore_pre(platform, critical, sg, invocation, origin, mask, cpu_sr, entry) *
        sem_query_output_fields(pd, cnt, grp) * sem_query_output_table(&((OS_SEM_DATA *)pd)->OSEventTbl[0], evtL, i)
    */
    OS_EXIT_CRITICAL();
    return (OS_ERR_NONE);
}
