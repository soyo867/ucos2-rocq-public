/* Annotation-only carrier of pinned V2.93.01 Source/os_sem.c; original headers are the actual input. */
void  OSSemSet (OS_EVENT  *pevent,
                INT16U     cnt,
                INT8U     *perr)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
         (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
         (mask: Z) (before: UCOS2_Verify_State) (eid: EventID)
         (observed: OSEventAbstractState) (pe pd: addr) (requested: Z)
         (X: Z -> UCOS2_Verify_State -> Prop)
    Require pevent == pe && perr == pd && cnt == requested &&
      0 <= requested && requested <= 65535 &&
      coq_prop(sem_set_call_input(critical, sg, invocation, pe, before, eid, observed)) &&
      coq_prop(sem_set_source_api_safe(critical, sg, invocation, pe, requested, before, X)) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) *
      sem_set_error_cell(pd) &&
      (pevent == 0 ||
       (pevent != 0 &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
        (event_slot_type_value(EventState(before), eid) != 3 ||
         (event_slot_type_value(EventState(before), eid) == 3 &&
          &((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
          coq_prop(sem_set_group_read_layout(critical, sg, invocation, before, eid,
            &((OS_EVENT *)pe)->OSEventGrp))))))
    Ensure sem_set_source_api_post(platform, critical, sg, invocation, origin,
                                  mask, before, pe, requested, pd, X)
*/
{
#if OS_CRITICAL_METHOD == 3u                          /* Allocate storage for CPU status register      */
    OS_CPU_SR  cpu_sr = 0u;
#endif



    /*@ perr == pd && sem_set_error_cell(pd)
        which implies perr == pd && undef_data_at(perr, unsigned char) */
#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return;
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {                    /* Validate 'pevent'                             */
        *perr = OS_ERR_PEVENT_NULL;
        return;
    }
#endif
    /*@ coq_prop(sem_set_call_input(critical, sg, invocation, pe, before, eid, observed)) &&
        pevent == pe && pevent != 0 &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
        which implies
        pevent == pe && pe == event_addr(sg, eid) && coq_prop(valid_event_id(sg, eid)) &&
        coq_prop(UCOS2_state_inv(sg, before)) &&
        coq_prop(sem_query_public_slot(before, eid, observed)) &&
        coq_prop(sem_set_call_input(critical, sg, invocation, pe, before, eid, observed)) &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        sem_query_type_frame(sg, before, eid)
    */
    /*@ 0 <= event_slot_type_value(EventState(before), eid) && event_slot_type_value(EventState(before), eid) <= 255 by local */
    if (pevent->OSEventType != OS_EVENT_TYPE_SEM) {   /* Validate event block type                     */
        *perr = OS_ERR_EVENT_TYPE;
        return;
    }
    /*@ coq_prop(UCOS2_state_inv(sg, before)) &&
        coq_prop(sem_query_public_slot(before, eid, observed)) &&
        coq_prop(sem_set_call_input(critical, sg, invocation, pe, before, eid, observed)) &&
        pevent == pe && pevent != 0 && event_slot_type_value(EventState(before), eid) == 3 &&
        &((OS_EVENT *)pe)->OSEventType == event_addr(sg, eid) + OSEventType_off &&
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, event_slot_type_value(EventState(before), eid)) *
        sem_query_type_frame(sg, before, eid)
        which implies
        pevent == pe && pe == event_addr(sg, eid) && coq_prop(valid_event_id(sg, eid)) &&
        coq_prop(mutex_query_handle_protocol(critical, sg, invocation, eid)) &&
        coq_prop(mutex_query_lookup(before, eid, observed)) &&
        encode_event_type(eventType(observed)) == 3 && UCOS2_inv(sg, before)
    */
    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(sem_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) && pevent == pe && perr == pd && cnt == requested &&
        pe == event_addr(sg, eid) && 0 <= requested && requested <= 65535 &&
        &((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(sem_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) && pevent == pe && perr == pd && cnt == requested &&
        pe == event_addr(sg, eid) && 0 <= requested && requested <= 65535 &&
        &((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
        0 <= encode_event_cnt_value(current) && encode_event_cnt_value(current) <= 65535 &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, encode_event_cnt_value(current)) * sem_set_count_frame(sg, entry, eid, current)
    */

    *perr = OS_ERR_NONE;
    if (pevent->OSEventCnt > 0u) {                    /* See if semaphore already has a count          */
        pevent->OSEventCnt = cnt;                     /* Yes, set it to the new value specified.       */
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(sem_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) && pevent == pe && perr == pd && cnt == requested &&
        pe == event_addr(sg, eid) && 0 <= requested && requested <= 65535 &&
        &((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
        encode_event_cnt_value(current) > 0 && critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, requested) * sem_set_count_frame(sg, entry, eid, current) * data_at(perr, unsigned char, 0)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(sem_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) && pevent == pe && perr == pd && cnt == requested &&
        pe == event_addr(sg, eid) && 0 <= requested && requested <= 65535 &&
        &((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
        sem_set_source_api_restore_pre(platform, critical, sg, invocation, origin, mask,
          cpu_sr, entry, sem_set_checkpoint(entry, eid, current, requested)) *
        data_at(perr, unsigned char, sem_set_error(entry, current))
    */
    } else {                                          /* No                                            */
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(sem_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) && pevent == pe && perr == pd && cnt == requested &&
        pe == event_addr(sg, eid) && 0 <= requested && requested <= 65535 &&
        &((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
        encode_event_cnt_value(current) <= 0 &&
        coq_prop(sem_set_group_read_layout(critical, sg, invocation, before, eid,
          &((OS_EVENT *)pe)->OSEventGrp)) && critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, encode_event_cnt_value(current)) * sem_set_count_frame(sg, entry, eid, current)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(sem_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) && pevent == pe && perr == pd && cnt == requested &&
        pe == event_addr(sg, eid) && 0 <= requested && requested <= 65535 &&
        &((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
        encode_event_cnt_value(current) <= 0 &&
        &((OS_EVENT *)pe)->OSEventGrp == event_addr(sg, eid) + OSEventGrp_off &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, encode_event_cnt_value(current)) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, encode_event_wait_grp(waitList(current), TskState(entry))) * sem_set_group_frame(sg, entry, eid, current)
    */

        if (pevent->OSEventGrp == 0u) {               /*      See if task(s) waiting?                  */
            pevent->OSEventCnt = cnt;                 /*      No, OK to set the value                  */
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(sem_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) && pevent == pe && perr == pd && cnt == requested &&
        pe == event_addr(sg, eid) && 0 <= requested && requested <= 65535 &&
        &((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
        encode_event_cnt_value(current) <= 0 && encode_event_wait_grp(waitList(current), TskState(entry)) == 0 && &((OS_EVENT *)pe)->OSEventGrp == event_addr(sg, eid) + OSEventGrp_off &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, requested) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, encode_event_wait_grp(waitList(current), TskState(entry))) * sem_set_group_frame(sg, entry, eid, current) * data_at(perr, unsigned char, 0)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(sem_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) && pevent == pe && perr == pd && cnt == requested &&
        pe == event_addr(sg, eid) && 0 <= requested && requested <= 65535 &&
        &((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
        sem_set_source_api_restore_pre(platform, critical, sg, invocation, origin, mask,
          cpu_sr, entry, sem_set_checkpoint(entry, eid, current, requested)) *
        data_at(perr, unsigned char, sem_set_error(entry, current))
    */
        } else {
            *perr              = OS_ERR_TASK_WAITING;
    /*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(sem_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) && pevent == pe && perr == pd && cnt == requested &&
        pe == event_addr(sg, eid) && 0 <= requested && requested <= 65535 &&
        &((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
        encode_event_cnt_value(current) <= 0 && encode_event_wait_grp(waitList(current), TskState(entry)) != 0 && &((OS_EVENT *)pe)->OSEventGrp == event_addr(sg, eid) + OSEventGrp_off &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, encode_event_cnt_value(current)) * data_at(&((OS_EVENT *)pe)->OSEventGrp, unsigned char, encode_event_wait_grp(waitList(current), TskState(entry))) * sem_set_group_frame(sg, entry, eid, current) * data_at(perr, unsigned char, 73)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(sem_query_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
          before, entry, observed, current)) && pevent == pe && perr == pd && cnt == requested &&
        pe == event_addr(sg, eid) && 0 <= requested && requested <= 65535 &&
        &((OS_EVENT *)pe)->OSEventCnt == event_addr(sg, eid) + OSEventCnt_off &&
        sem_set_source_api_restore_pre(platform, critical, sg, invocation, origin, mask,
          cpu_sr, entry, sem_set_checkpoint(entry, eid, current, requested)) *
        data_at(perr, unsigned char, sem_set_error(entry, current))
    */

        }
    }
    OS_EXIT_CRITICAL();
}
