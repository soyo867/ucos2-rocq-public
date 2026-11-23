/* Annotation-only carrier of pinned Source/os_q.c; original headers/config
 * remain the actual input. The postfix adaptation is a separate overlay. */
INT8U OSQQuery(OS_EVENT *pevent, OS_Q_DATA *p_q_data)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
    (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
    (mask: Z) (before: UCOS2_Verify_State) (eid: EventID)
    (observed: OSEventAbstractState) (pe pd: addr)
    (X: Z -> option QueueQuerySnapshot -> UCOS2_Verify_State -> Prop)
    Require pevent == pe && p_q_data == pd &&
      coq_prop(q_query_call_input(critical, sg, invocation, pe, pd, before, eid, observed)) &&
      q_query_safe(critical, sg, invocation, eid, pe, pd, before, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) &&
      (pevent == 0 || (pevent != 0 && p_q_data == 0) ||
       (pevent != 0 && p_q_data != 0 && event_slot_type_value(EventState(before), eid) != 2 &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off) ||
       (pevent != 0 && p_q_data != 0 && event_slot_type_value(EventState(before), eid) == 2 &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off && coq_prop(q_query_layout(sg, eid)) &&
        undef_data_at(&((OS_Q_DATA *)pd)->OSMsg, void *) *
        undef_data_at(&((OS_Q_DATA *)pd)->OSNMsgs, unsigned short) *
        undef_data_at(&((OS_Q_DATA *)pd)->OSQSize, unsigned short) *
        undef_data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char) *
        UCharArray::undef_full(&((OS_Q_DATA *)pd)->OSEventTbl[0], 8)))
    Ensure q_query_api_post(platform, critical, sg, invocation, origin, mask,
      before, eid, pe, pd, __return, X)
*/
{
    OS_Q       *pq;
    INT8U       i;
    OS_PRIO    *psrc;
    OS_PRIO    *pdest;
#if OS_CRITICAL_METHOD == 3u
    OS_CPU_SR   cpu_sr = 0u;
#endif
#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {
        return (OS_ERR_PEVENT_NULL);
    }
    if (p_q_data == (OS_Q_DATA *)0) {
        return (OS_ERR_PDATA_NULL);
    }
#endif
    /*@ coq_prop(q_query_call_input(critical, sg, invocation, pe, pd, before, eid, observed)) &&
        pevent == pe && p_q_data == pd && pevent != 0 && p_q_data != 0 &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
        which implies
        pevent == pe && p_q_data == pd && pevent == event_addr(sg, eid) &&
        coq_prop(valid_event_id(sg, eid)) && coq_prop(UCOS2_state_inv(sg, before)) &&
        coq_prop(q_query_public_slot(before, eid, observed)) &&
        coq_prop(q_query_call_input(critical, sg, invocation, pe, pd, before, eid, observed)) &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        q_query_type_frame(sg, before, eid)
    */
    /*@ 0 <= event_slot_type_value(EventState(before), eid) && event_slot_type_value(EventState(before), eid) <= 255 by local */
    if (pevent->OSEventType != OS_EVENT_TYPE_Q) {
        return (OS_ERR_EVENT_TYPE);
    }
    /*@ coq_prop(UCOS2_state_inv(sg, before)) && coq_prop(q_query_public_slot(before, eid, observed)) &&
        coq_prop(q_query_call_input(critical, sg, invocation, pe, pd, before, eid, observed)) &&
        pevent != 0 && p_q_data != 0 && pevent == pe && p_q_data == pd &&
        event_slot_type_value(EventState(before), eid) == 2 &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        q_query_type_frame(sg, before, eid)
        which implies
        coq_prop(mutex_query_handle_protocol(critical, sg, invocation, eid)) &&
        coq_prop(mutex_query_lookup(before, eid, observed)) && encode_event_type(eventType(observed)) == 2 &&
        pevent == pe && p_q_data == pd && pevent == event_addr(sg, eid) &&
        coq_prop(valid_event_id(sg, eid)) && coq_prop(UCOS2_state_inv(sg, before)) &&
        critical_region_outside(critical, sg, invocation, before)
    */
    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(q_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr, before, entry, observed, current)) &&
        coq_prop(q_query_layout(sg, eid)) && pevent == pe && p_q_data == pd && pe == event_addr(sg, eid) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields)
          (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z),
        coq_prop(q_query_layout(sg, eid)) && coq_prop(q_query_queue_valid(sg, q)) &&
        pevent == pe && p_q_data == pd && pe == event_addr(sg, eid) && Zlength(rows) == 8 &&
        q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) *
        store_osprio_array(&((OS_EVENT *)pe)->OSEventTbl[0], rows) * used_queue_control_block(sg, q) * queue_buffer_rep(q, slots)
    */
    p_q_data->OSEventGrp = pevent->OSEventGrp;
    psrc                 = &pevent->OSEventTbl[0];
    pdest                = &p_q_data->OSEventTbl[0];
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z), Zlength(rows) == 8 &&
        q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * used_queue_control_block(sg, q) * queue_buffer_rep(q, slots) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * coq_prop(q_query_queue_valid(sg, q)) * store_osprio_array(&pevent->OSEventTbl[0], rows) * UCharArray::undef_full(&p_q_data->OSEventTbl[0], 8)
        which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z), Zlength(rows) == 8 &&
        q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * used_queue_control_block(sg, q) * queue_buffer_rep(q, slots) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * coq_prop(q_query_queue_valid(sg, q)) * store_osprio_array(&pevent->OSEventTbl[0], rows) * q_query_output_table(&p_q_data->OSEventTbl[0], rows, 0) */
    /*@ Inv exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields)
          (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z),
        0 <= i && i <= 8 && Zlength(rows) == 8 && coq_prop(q_query_queue_valid(sg, q)) &&
        coq_prop(q_query_layout(sg, eid)) && pevent == pe && p_q_data == pd && pe == event_addr(sg, eid) &&
        psrc == &pevent->OSEventTbl[0] + i && pdest == &p_q_data->OSEventTbl[0] + i &&
        q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) *
        store_osprio_array(&((OS_EVENT *)pe)->OSEventTbl[0], rows) * used_queue_control_block(sg, q) * queue_buffer_rep(q, slots) *
        undef_data_at(&((OS_Q_DATA *)pd)->OSMsg, void *) *
        undef_data_at(&((OS_Q_DATA *)pd)->OSNMsgs, unsigned short) *
        undef_data_at(&((OS_Q_DATA *)pd)->OSQSize, unsigned short) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * q_query_output_table(&((OS_Q_DATA *)pd)->OSEventTbl[0], rows, i)
    */
    for (i = 0u; i < OS_EVENT_TBL_SIZE; i++) {
        /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z), 0 <= i && i < 8 && Zlength(rows) == 8 &&
            psrc == &pevent->OSEventTbl[0] + i && pdest == &p_q_data->OSEventTbl[0] + i &&
            q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * used_queue_control_block(sg, q) * queue_buffer_rep(q, slots) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * coq_prop(q_query_queue_valid(sg, q)) * store_osprio_array(&pevent->OSEventTbl[0], rows) * q_query_output_table(&p_q_data->OSEventTbl[0], rows, i)
            which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z),
            Zlength(rows) == 8 && psrc == &pevent->OSEventTbl[0] + i && pdest == &p_q_data->OSEventTbl[0] + i &&
            q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * used_queue_control_block(sg, q) * queue_buffer_rep(q, slots) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * coq_prop(q_query_queue_valid(sg, q)) * data_at(psrc, unsigned char, Znth(i, rows, 0)) * store_osprio_array_missing_i(&pevent->OSEventTbl[0], rows, i) *
            undef_data_at(pdest, unsigned char) * q_query_output_table_missing_i(&p_q_data->OSEventTbl[0], rows, i)
        */
        *pdest++ = *psrc++;
        /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z), 0 <= i && i < 8 && Zlength(rows) == 8 &&
            q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * used_queue_control_block(sg, q) * queue_buffer_rep(q, slots) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * coq_prop(q_query_queue_valid(sg, q)) * data_at(&pevent->OSEventTbl[i], unsigned char, Znth(i, rows, 0)) * store_osprio_array_missing_i(&pevent->OSEventTbl[0], rows, i) *
            data_at(&p_q_data->OSEventTbl[i], unsigned char, Znth(i, rows, 0)) * q_query_output_table_missing_i(&p_q_data->OSEventTbl[0], rows, i)
            which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z), Zlength(rows) == 8 &&
            q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * used_queue_control_block(sg, q) * queue_buffer_rep(q, slots) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * coq_prop(q_query_queue_valid(sg, q)) * store_osprio_array(&pevent->OSEventTbl[0], rows) * q_query_output_table(&p_q_data->OSEventTbl[0], rows, i + 1)
        */
    }
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z), i >= 8 && i <= 8 && Zlength(rows) == 8 &&
        q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * used_queue_control_block(sg, q) * queue_buffer_rep(q, slots) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * coq_prop(q_query_queue_valid(sg, q)) * store_osprio_array(&pevent->OSEventTbl[0], rows) * q_query_output_table(&p_q_data->OSEventTbl[0], rows, i)
        which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z), i >= 8 && i <= 8 && Zlength(rows) == 8 &&
        q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * used_queue_control_block(sg, q) * queue_buffer_rep(q, slots) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * coq_prop(q_query_queue_valid(sg, q)) * store_osprio_array(&pevent->OSEventTbl[0], rows) * store_osprio_array(&p_q_data->OSEventTbl[0], rows) */
    pq = (OS_Q *)pevent->OSEventPtr;
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z), pq == qcb_addr(sg, qID(q)) && coq_prop(q_query_layout(sg, eid)) && coq_prop(q_query_queue_valid(sg, q)) &&
        q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_EVENT *)pe)->OSEventTbl[0], rows) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_Q_DATA *)pd)->OSEventTbl[0], rows) * used_queue_control_block(sg, q) * queue_buffer_rep(q, slots)
        which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z), coq_prop(q_query_queue_at(sg, pq, q)) && coq_prop(q_query_layout(sg, eid)) && coq_prop(q_query_queue_valid(sg, q)) &&
        0 <= queue_entries(q) && queue_entries(q) <= 65535 &&
        q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_EVENT *)pe)->OSEventTbl[0], rows) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_Q_DATA *)pd)->OSEventTbl[0], rows) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * q_query_qcb_unread(sg, q) * queue_buffer_rep(q, slots)
    */
    if (pq->OSQEntries > 0u) {
        /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z), coq_prop(q_query_queue_at(sg, pq, q)) && coq_prop(q_query_layout(sg, eid)) && coq_prop(q_query_queue_valid(sg, q)) && queue_entries(q) > 0 &&
        q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_EVENT *)pe)->OSEventTbl[0], rows) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_Q_DATA *)pd)->OSEventTbl[0], rows) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * q_query_qcb_unread(sg, q) * queue_buffer_rep(q, slots)
        which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z) (message: addr), coq_prop(q_query_queue_at(sg, pq, q)) && coq_prop(q_query_layout(sg, eid)) && coq_prop(q_query_queue_valid(sg, q)) &&
        coq_prop(q_query_read_message(q, slots, message)) &&
        q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_EVENT *)pe)->OSEventTbl[0], rows) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_Q_DATA *)pd)->OSEventTbl[0], rows) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * q_query_qcb_unread(sg, q) * data_at(queue_out_addr(q), void *, message) * q_query_head_slot(q, slots)
        */
        p_q_data->OSMsg = *pq->OSQOut;
        /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z) (message: addr), coq_prop(q_query_queue_at(sg, pq, q)) && coq_prop(q_query_layout(sg, eid)) && coq_prop(q_query_queue_valid(sg, q)) &&
        coq_prop(q_query_read_message(q, slots, message)) &&
        q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_EVENT *)pe)->OSEventTbl[0], rows) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_Q_DATA *)pd)->OSEventTbl[0], rows) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * q_query_qcb_unread(sg, q) * data_at(queue_out_addr(q), void *, message) * q_query_head_slot(q, slots) *
        data_at(&((OS_Q_DATA *)pd)->OSMsg, void *, message)
        which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z) (message: addr), coq_prop(q_query_queue_at(sg, pq, q)) && coq_prop(q_query_layout(sg, eid)) && coq_prop(q_query_queue_valid(sg, q)) &&
        coq_prop(q_query_read_message(q, slots, message)) &&
        q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_EVENT *)pe)->OSEventTbl[0], rows) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_Q_DATA *)pd)->OSEventTbl[0], rows) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * q_query_qcb_unread(sg, q) * queue_buffer_rep(q, slots) * data_at(&((OS_Q_DATA *)pd)->OSMsg, void *, message)
        */
    } else {
        p_q_data->OSMsg = (void *)0;
        /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z), coq_prop(q_query_queue_at(sg, pq, q)) && coq_prop(q_query_layout(sg, eid)) && coq_prop(q_query_queue_valid(sg, q)) && queue_entries(q) <= 0 &&
        q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_EVENT *)pe)->OSEventTbl[0], rows) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_Q_DATA *)pd)->OSEventTbl[0], rows) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * q_query_qcb_unread(sg, q) * queue_buffer_rep(q, slots) * data_at(&((OS_Q_DATA *)pd)->OSMsg, void *, 0)
        which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: list QueueID) (slots: list (option addr)) (grp: Z) (rows: list Z), coq_prop(q_query_queue_at(sg, pq, q)) && coq_prop(q_query_layout(sg, eid)) && coq_prop(q_query_queue_valid(sg, q)) && coq_prop(q_query_read_message(q, slots, 0)) &&
        q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_EVENT *)pe)->OSEventTbl[0], rows) *
        data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_Q_DATA *)pd)->OSEventTbl[0], rows) * data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * q_query_qcb_unread(sg, q) * queue_buffer_rep(q, slots) * data_at(&((OS_Q_DATA *)pd)->OSMsg, void *, 0)
        */
    }
    p_q_data->OSNMsgs = pq->OSQEntries;
    p_q_data->OSQSize = pq->OSQSize;
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields)
          (free: list QueueID) (slots: list (option addr)) (grp message: Z) (rows: list Z),
        pevent == pe && p_q_data == pd && pe == event_addr(sg, eid) && coq_prop(q_query_queue_at(sg, pq, q)) &&
        coq_prop(q_query_layout(sg, eid)) && coq_prop(q_query_read_message(q, slots, message)) &&
        q_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr, before, entry, eid, observed, current, q, free, slots, grp, rows) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, qcb_addr(sg, qID(q))) *
        data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, grp) * store_osprio_array(&((OS_EVENT *)pe)->OSEventTbl[0], rows) *
        data_at(&pq->OSQOut, void **, queue_out_addr(q)) * data_at(&pq->OSQEntries, unsigned short, queue_entries(q)) *
        data_at(&pq->OSQSize, unsigned short, qSize(q)) * q_query_qcb_unread(sg, q) * queue_buffer_rep(q, slots) *
        data_at(&((OS_Q_DATA *)pd)->OSMsg, void *, message) * data_at(&((OS_Q_DATA *)pd)->OSNMsgs, unsigned short, queue_entries(q)) *
        data_at(&((OS_Q_DATA *)pd)->OSQSize, unsigned short, qSize(q)) * data_at(&((OS_Q_DATA *)pd)->OSEventGrp, unsigned char, grp) *
        store_osprio_array(&((OS_Q_DATA *)pd)->OSEventTbl[0], rows)
        which implies exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (snapshot: QueueQuerySnapshot),
        pevent == pe && p_q_data == pd && pq == pq &&
        coq_prop(q_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr, before, entry, observed, current)) &&
        coq_prop(q_query_critical(sg, eid, entry, snapshot, entry)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry) * q_query_output_fields_rep(pd, snapshot)
    */
    OS_EXIT_CRITICAL();
    return (OS_ERR_NONE);
}
