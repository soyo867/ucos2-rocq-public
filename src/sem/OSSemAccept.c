/* Annotation carrier from pinned V2.93.01 Source/os_sem.c.
 * Actual QCP input: original-header Source/ucos_ii.c after the overlays in
 * annotated_C/overlays/sem/README-accept.md. This is not a standalone TU.
 */
/*
*********************************************************************************************************
*                                              uC/OS-II
*                                        The Real-Time Kernel
*
*                    Copyright 1992-2021 Silicon Laboratories Inc. www.silabs.com
*
*                                 SPDX-License-Identifier: APACHE-2.0
*
*               This software is subject to an open source license and is distributed by
*                Silicon Laboratories Inc. pursuant to the terms of the Apache License,
*                    Version 2.0 available at www.apache.org/licenses/LICENSE-2.0.
*
*********************************************************************************************************
*/


INT16U  OSSemAccept (OS_EVENT *pevent)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
         (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
         (mask: Z) (before: UCOS2_Verify_State) (eid: EventID)
         (observed: OSEventAbstractState) (pe: addr)
         (X: Z -> UCOS2_Verify_State -> Prop)
    Require pevent == pe && coq_prop(valid_stable_glob_vars(sg)) && coq_prop(sem_accept_profile(sg)) &&
      coq_prop(sem_accept_call_input(critical, sg, invocation, pe, before, eid, observed)) &&
      (pevent == 0 || coq_prop(event_core_fields_layout_prop(sg, eid,
        &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt))) &&
      sem_accept_source_api_safe(critical, sg, invocation, pe, before, X) &&
      sem_accept_closed(platform, critical, sg, invocation, origin, mask, before)
    Ensure exists (after: UCOS2_Verify_State),
      coq_prop(sem_accept_source_api_post(critical, sg, invocation, pe, before, __return, after)) &&
      sem_accept_source_api_return_safe(after, __return, X) &&
      sem_accept_closed(platform, critical, sg, invocation, origin, mask, after)
*/
{
    INT16U     cnt;
#if OS_CRITICAL_METHOD == 3u                          /* Allocate storage for CPU status register      */
    OS_CPU_SR  cpu_sr = 0u;
#endif



#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {                    /* Validate 'pevent'                             */
        return (0u);
    }
#endif
    
/*@ coq_prop(sem_accept_call_input(critical, sg, invocation, pe, before, eid, observed)) &&
        pevent != 0 && pevent == pe &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        sem_accept_closed(platform, critical, sg, invocation, origin, mask, before)
        which implies
        pevent == pe && pevent == event_addr(sg, eid) && coq_prop(valid_event_id(sg, eid)) &&
        coq_prop(UCOS2_state_inv(sg, before)) &&
        coq_prop(sem_accept_call_input(critical, sg, invocation, pe, before, eid, observed)) &&
        coq_prop(sem_accept_lookup(before, eid, observed)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, encode_event_type(eventType(observed))) *
        sem_accept_type_frame(sg, before, eid, observed)
    */
if (pevent->OSEventType != OS_EVENT_TYPE_SEM) {   /* Validate event block type                     */
        return (0u);
    }
    
/*@ coq_prop(UCOS2_state_inv(sg, before)) &&
        coq_prop(sem_accept_lookup(before, eid, observed)) &&
        coq_prop(sem_accept_call_input(critical, sg, invocation, pe, before, eid, observed)) &&
        pevent != 0 && pevent == pe && encode_event_type(eventType(observed)) == 3 &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        data_at(&((OS_EVENT *)pe)->OSEventType, unsigned char, encode_event_type(eventType(observed))) *
        sem_accept_type_frame(sg, before, eid, observed)
        which implies
        coq_prop(sem_accept_handle_protocol(critical, sg, invocation, eid)) &&
        coq_prop(sem_accept_lookup(before, eid, observed)) &&
        encode_event_type(eventType(observed)) == 3 &&
        pevent == pe && pevent == event_addr(sg, eid) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        UCOS2_inv(sg, before)
    */
OS_ENTER_CRITICAL();
    
/*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(sem_accept_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
                                        before, entry, observed, current)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        UCOS2_inv(sg, entry)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(sem_accept_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
                                        before, entry, observed, current)) &&
        0 <= encode_event_cnt_value(current) && encode_event_cnt_value(current) <= 65535 &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, encode_event_cnt_value(current)) *
        sem_accept_count_frame(sg, entry, eid, current)
    */
cnt = pevent->OSEventCnt;
    if (cnt > 0u) {                                   /* See if resource is available                  */
        pevent->OSEventCnt--;                         /* Yes, decrement semaphore and notify caller    */
    }
    
/*@ Assert exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        pevent != 0 && pevent == pe && pevent == event_addr(sg, eid) && coq_prop(valid_event_id(sg, eid)) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        sem_accept_source_api_safe(critical, sg, invocation, pe, before, X) &&
        coq_prop(sem_accept_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
                                        before, entry, observed, current)) &&
        cnt == encode_event_cnt_value(current) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, sem_accept_stored_count(current)) *
        sem_accept_count_frame(sg, entry, eid, current)
    */

/*@ exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(sem_accept_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
                                        before, entry, observed, current)) &&
        pevent == pe && pevent == event_addr(sg, eid) &&
        coq_prop(event_core_fields_layout_prop(sg, eid,
          &((OS_EVENT *)pe)->OSEventType, &((OS_EVENT *)pe)->OSEventPtr, &((OS_EVENT *)pe)->OSEventCnt)) &&
        cnt == encode_event_cnt_value(current) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        data_at(&((OS_EVENT *)pe)->OSEventCnt, unsigned short, sem_accept_stored_count(current)) *
        sem_accept_count_frame(sg, entry, eid, current)
        which implies
        exists (entry: UCOS2_Verify_State) (current: OSEventAbstractState),
        coq_prop(sem_accept_acquire_facts(critical, sg, invocation, eid, mask, cpu_sr,
                                        before, entry, observed, current)) &&
        cnt == encode_event_cnt_value(current) &&
        pevent == pe && pevent == event_addr(sg, eid) &&
        sem_accept_source_api_restore_pre(platform, critical, sg, invocation, origin, mask, cpu_sr,
                                         entry, sem_accept_checkpoint(entry, eid, current))
    */
OS_EXIT_CRITICAL();
    return (cnt);                                     /* Return semaphore count                        */
}
