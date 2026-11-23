/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

OS_EVENT  *OSSemCreate (INT16U cnt)
/*@ With (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
    (sg : StableGlobVars) (call : OsSchedCallContext) (mask : Z)
    (initial : UCOS2_Verify_State) (X : addr -> UCOS2_Verify_State -> Prop)
    Require sem_create_api_call_pre(environment, critical, sg, call, mask, initial, cnt, X)
    Ensure sem_create_api_call_post(environment, critical, sg, call, mask, __return, X)
*/
{
    OS_EVENT  *pevent;
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif



#ifdef OS_SAFETY_CRITICAL_IEC61508
    if (OSSafetyCriticalStartFlag == OS_TRUE) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return ((OS_EVENT *)0);
    }
#endif

    /*@ cnt == cnt@pre &&
        sem_create_api_call_pre(environment, critical, sg, call, mask, initial, cnt, X)
        which implies
        cnt == cnt@pre &&
        sem_create_api_input_facts(critical, sg, call, initial, cnt, X) &&
        0 <= intNesting(IntrState(initial)) && intNesting(IntrState(initial)) <= 255 &&
        data_at(&OSIntNesting, INT8U, intNesting(IntrState(initial))) *
        q_create_without_nesting(environment, QCreateNoPrivate, mbox_create_call_frame, sg, call, mask, initial)
    */
    if (OSIntNesting > 0u) {                     /* See if called from ISR ...                         */
        /*@ cnt == cnt@pre &&
            sem_create_api_input_facts(critical, sg, call, initial, cnt, X) &&
            data_at(&OSIntNesting, INT8U, intNesting(IntrState(initial))) *
            q_create_without_nesting(environment, QCreateNoPrivate, mbox_create_call_frame, sg, call, mask, initial)
            which implies
            sem_create_api_call_pre(environment, critical, sg, call, mask, initial, cnt, X)
        */
        return ((OS_EVENT *)0);                  /* ... can't CREATE from an ISR                       */
    }
    /*@ cnt == cnt@pre &&
        sem_create_api_input_facts(critical, sg, call, initial, cnt, X) &&
        data_at(&OSIntNesting, INT8U, intNesting(IntrState(initial))) *
        q_create_without_nesting(environment, QCreateNoPrivate, mbox_create_call_frame, sg, call, mask, initial)
        which implies
        cnt == cnt@pre &&
        sem_create_api_input_facts(critical, sg, call, initial, cnt, X) &&
        q_create_save_input(environment, critical, QCreateNoPrivate, mbox_create_call_frame, sg, call, mask, initial)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (first_call : OsSchedCallContext) (entry : UCOS2_Verify_State),
        cnt == cnt@pre &&
        sem_create_api_input_facts(critical, sg, call, initial, cnt, X) &&
        q_create_first_facts(critical, sg, call, initial, mask, cpu_sr, first_call, entry) &&
        q_create_masked_control(environment, critical, sg, first_call, cpu_sr, entry, entry) *
        data_at(&OSEventFreeList, OS_EVENT *, sem_create_pool_head(sg, entry)) *
        sem_create_pool_frame(sg, entry) * undef_data_at(&pevent, OS_EVENT *)
    */
    pevent = OSEventFreeList;                    /* Get next free event control block                  */
    if (OSEventFreeList != (OS_EVENT *)0) {      /* See if pool of free ECB pool was empty             */
        /*@ Assert exists (first_call : OsSchedCallContext) (entry : UCOS2_Verify_State)
            (eid : EventID) (rest : list EventID) (image : EventStorage),
            cnt == cnt@pre &&
            sem_create_api_input_facts(critical, sg, call, initial, cnt, X) &&
            q_create_first_facts(critical, sg, call, initial, mask, cpu_sr, first_call, entry) &&
            sem_create_head_facts(sg, entry, eid, rest, image) && pevent == event_pool_addr(sg, eid) &&
            q_create_masked_control(environment, critical, sg, first_call, cpu_sr, entry, entry) *
            data_at(&OSEventFreeList, OS_EVENT *, pevent) *
            data_at(&pevent->OSEventPtr, void *, event_encode_pool_link(sg, hd_error(rest))) *
            sem_create_node_frame(sg, entry, eid, image)
        */
        OSEventFreeList = (OS_EVENT *)OSEventFreeList->OSEventPtr;
    }
    /*@ Assert cnt == cnt@pre &&
        sem_create_api_input_facts(critical, sg, call, initial, cnt, X) &&
        mbox_create_allocation_cut(environment, critical, sg, call, initial, mask, cpu_sr, pevent)
    */
    /*@ mbox_create_allocation_cut(environment, critical, sg, call, initial, mask, cpu_sr, pevent)
        which implies exists (first_call : OsSchedCallContext) (entry allocated : UCOS2_Verify_State)
          (allocation_result : option (EventID * EventStorage)),
        q_create_first_facts(critical, sg, call, initial, mask, cpu_sr, first_call, entry) &&
        event_create_allocate_critical(entry, allocation_result, allocated) &&
        pevent == event_create_return_ptr(sg, allocation_result) &&
        q_create_restore_input(environment, critical, q_create_allocated_owner(entry, allocation_result),
          mbox_create_call_frame, sg, first_call, cpu_sr, entry, allocated)
    */
    OS_EXIT_CRITICAL();
    /*@ Assert cnt == cnt@pre &&
        sem_create_api_input_facts(critical, sg, call, initial, cnt, X) &&
        interrupt_saved_value(mask, cpu_sr) &&
        mbox_create_allocation_return(environment, critical, sg, call, initial, mask, pevent)
    */
    if (pevent != (OS_EVENT *)0) {
        /*@ cnt == cnt@pre &&
            sem_create_api_input_facts(critical, sg, call, initial, cnt, X) &&
            mbox_create_allocation_return(environment, critical, sg, call, initial, mask, pevent) &&
            pevent != 0
            which implies exists (eid : EventID) (allocation : EventPrivateAllocation)
              (current : UCOS2_Verify_State),
            cnt == cnt@pre && pevent == event_pool_addr(sg, eid) &&
            sem_create_api_input_facts(critical, sg, call, initial, cnt, X) &&
            mbox_create_initialization_context(environment, critical, sg, call, initial, mask,
              eid, allocation, current) *
            undef_data_at(&pevent->OSEventType, INT8U) *
            undef_data_at(&pevent->OSEventCnt, INT16U) *
            undef_data_at(&pevent->OSEventPtr, void *) *
            event_wait_list_init_pre(&pevent->OSEventGrp, pevent->OSEventTbl) *
            mbox_create_initialization_frame(pevent, eventPrivateStorage(allocation))
        */
        pevent->OSEventType    = OS_EVENT_TYPE_SEM;
        pevent->OSEventCnt     = cnt;
        pevent->OSEventPtr     = (void *)0;       /* Unlink from ECB free list                           */
#if OS_EVENT_NAME_EN > 0u
        pevent->OSEventName    = (INT8U *)(void *)"?";
#endif
        OS_EventWaitListInit(pevent);

        OS_TRACE_SEM_CREATE(pevent, pevent->OSEventName);
        /*@ Assert cnt == cnt@pre &&
            sem_create_api_call_post(environment, critical, sg, call, mask, pevent, X) *
            undef_data_at(&cpu_sr, OS_CPU_SR)
        */
    }
    /*@ Assert cnt == cnt@pre &&
        sem_create_api_call_post(environment, critical, sg, call, mask, pevent, X) *
        undef_data_at(&cpu_sr, OS_CPU_SR)
    */
    return (pevent);                             /* Return pointer to event control block              */
}
