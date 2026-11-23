/* OSQCreate, complete single-function annotation carrier.
 * Fixed upstream: uC/OS-II V2.93.01, Source/os_q.c,
 * commit bfc6120f20cb27a927a9fc5dd667f9e455495777.
 * Executable statements are unchanged. Original headers, configuration and
 * callee contracts are reconstructed by overlays/queue/README-q-create.md.
 */
OS_EVENT  *OSQCreate (void    **start,
                      INT16U    size)
/*@ With (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
    (sg : StableGlobVars) (call : OsSchedCallContext) (mask : Z)
    (initial : UCOS2_Verify_State) (slots : list (option addr))
    (X : addr -> UCOS2_Verify_State -> Prop)
    Require q_create_call_pre(environment, critical, sg, call, mask, initial, start, size, slots, X)
    Ensure q_create_call_post(environment, critical, sg, call, mask, start@pre, size@pre, slots, __return, X)
*/
{
    OS_EVENT  *pevent;
    OS_Q      *pq;
#if OS_CRITICAL_METHOD == 3u
    OS_CPU_SR  cpu_sr = 0u;
#endif

#ifdef OS_SAFETY_CRITICAL_IEC61508
    if (OSSafetyCriticalStartFlag == OS_TRUE) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return ((OS_EVENT *)0);
    }
#endif

    /*@ start == start@pre && size == size@pre &&
        q_create_call_pre(environment, critical, sg, call, mask, initial, start, size, slots, X)
        which implies
        start == start@pre && size == size@pre &&
        q_create_input_facts(critical, sg, call, initial, start, size, slots, X) &&
        0 <= intNesting(IntrState(initial)) && intNesting(IntrState(initial)) <= 255 &&
        data_at(&OSIntNesting, INT8U, intNesting(IntrState(initial))) *
        q_create_without_nesting(environment, QCreateNoPrivate, q_create_buffer(start, size, slots),
          sg, call, mask, initial)
    */
    if (OSIntNesting > 0u) {
        /*@ start == start@pre && size == size@pre &&
        q_create_input_facts(critical, sg, call, initial, start, size, slots, X) &&
            data_at(&OSIntNesting, INT8U, intNesting(IntrState(initial))) *
            q_create_without_nesting(environment, QCreateNoPrivate, q_create_buffer(start, size, slots),
              sg, call, mask, initial)
            which implies
            q_create_call_pre(environment, critical, sg, call, mask, initial, start, size, slots, X)
        */
        return ((OS_EVENT *)0);
    }
    /*@ start == start@pre && size == size@pre &&
        data_at(&OSIntNesting, INT8U, intNesting(IntrState(initial))) *
        q_create_without_nesting(environment, QCreateNoPrivate, q_create_buffer(start, size, slots),
          sg, call, mask, initial) &&
        q_create_input_facts(critical, sg, call, initial, start, size, slots, X)
        which implies
        start == start@pre && size == size@pre &&
        q_create_input_facts(critical, sg, call, initial, start, size, slots, X) &&
        q_create_save_input(environment, critical, QCreateNoPrivate, q_create_buffer(start, size, slots),
          sg, call, mask, initial)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (first_call : OsSchedCallContext) (entry : UCOS2_Verify_State),
        start == start@pre && size == size@pre &&
        q_create_input_facts(critical, sg, call, initial, start, size, slots, X) &&
        q_create_first_facts(critical, sg, call, initial, mask, cpu_sr, first_call, entry) &&
        q_create_masked_control(environment, critical, sg, first_call, cpu_sr, entry, entry) *
        data_at(&OSEventFreeList, OS_EVENT *, sem_create_pool_head(sg, entry)) *
        sem_create_pool_frame(sg, entry) * q_create_buffer(start, size, slots) *
        undef_data_at(&pevent, OS_EVENT *) * undef_data_at(&pq, OS_Q *)
    */
    pevent = OSEventFreeList;
    if (OSEventFreeList != (OS_EVENT *)0) {
        /*@ Assert exists (first_call : OsSchedCallContext) (entry : UCOS2_Verify_State)
            (eid : EventID) (rest : list EventID) (image : EventStorage),
            start == start@pre && size == size@pre &&
        q_create_input_facts(critical, sg, call, initial, start, size, slots, X) &&
            q_create_first_facts(critical, sg, call, initial, mask, cpu_sr, first_call, entry) &&
            sem_create_head_facts(sg, entry, eid, rest, image) && pevent == event_pool_addr(sg, eid) &&
            q_create_masked_control(environment, critical, sg, first_call, cpu_sr, entry, entry) *
            data_at(&OSEventFreeList, OS_EVENT *, pevent) *
            data_at(&pevent->OSEventPtr, void *, event_encode_pool_link(sg, hd_error(rest))) *
            sem_create_node_frame(sg, entry, eid, image) * q_create_buffer(start, size, slots) *
            undef_data_at(&pq, OS_Q *)
        */
        OSEventFreeList = (OS_EVENT *)OSEventFreeList->OSEventPtr;
    }
    /*@ Assert start == start@pre && size == size@pre &&
        q_create_input_facts(critical, sg, call, initial, start, size, slots, X) &&
        q_create_allocation_cut(environment, critical, sg, call, initial, mask, cpu_sr,
          start, size, slots, pevent) * undef_data_at(&pq, OS_Q *)
    */
    /*@ q_create_allocation_cut(environment, critical, sg, call, initial, mask, cpu_sr,
          start, size, slots, pevent)
        which implies exists (first_call : OsSchedCallContext) (entry allocated : UCOS2_Verify_State)
          (allocation_result : option (EventID * EventStorage)),
        q_create_first_facts(critical, sg, call, initial, mask, cpu_sr, first_call, entry) &&
        event_create_allocate_critical(entry, allocation_result, allocated) &&
        pevent == event_create_return_ptr(sg, allocation_result) &&
        q_create_restore_input(environment, critical, q_create_allocated_owner(entry, allocation_result),
          q_create_buffer(start, size, slots), sg, first_call, cpu_sr, entry, allocated)
    */
    OS_EXIT_CRITICAL();
    /*@ Assert start == start@pre && size == size@pre &&
        q_create_input_facts(critical, sg, call, initial, start, size, slots, X) &&
        interrupt_saved_value(mask, cpu_sr) &&
        q_create_allocation_return(environment, critical, sg, call, initial, mask,
          start, size, slots, pevent) * undef_data_at(&pq, OS_Q *)
    */
    if (pevent != (OS_EVENT *)0) {
        /*@ q_create_allocation_return(environment, critical, sg, call, initial, mask,
              start, size, slots, pevent) && pevent != 0
            which implies exists (resumed_call : OsSchedCallContext) (resumed : UCOS2_Verify_State)
              (eid : EventID) (allocation : EventPrivateAllocation),
            task_tcb_init_stack_same_call(resumed_call, call) && pevent == event_pool_addr(sg, eid) &&
            q_create_event_history(critical, sg, os_sched_call_invocation(call), initial, eid, allocation, resumed) &&
            q_create_save_input(environment, critical, QCreatePrivateEvent(eid, allocation),
              q_create_buffer(start, size, slots), sg, resumed_call, mask, resumed)
        */
        OS_ENTER_CRITICAL();
        /*@ Assert exists (second_call : OsSchedCallContext) (entry : UCOS2_Verify_State)
            (eid : EventID) (allocation : EventPrivateAllocation) (free : list QueueID),
            start == start@pre && size == size@pre &&
        q_create_input_facts(critical, sg, call, initial, start, size, slots, X) &&
            task_tcb_init_stack_same_call(second_call, call) && interrupt_saved_value(mask, cpu_sr) &&
            pevent == event_pool_addr(sg, eid) &&
            q_create_event_history(critical, sg, os_sched_call_invocation(call), initial, eid, allocation, entry) &&
            UCOS2_state_inv(sg, entry) && queue_pool_partition(sg, EventState(entry), free) &&
            q_create_private_lookup(entry, eid, allocation) &&
            q_create_masked_control(environment, critical, sg, second_call, cpu_sr, entry, entry) *
            event_private_storage_rep(sg, eid, allocation) * q_create_queue_pool_frame(sg, entry) *
            data_at(&OSQFreeList, OS_Q *, queue_free_head(sg, free)) *
            store_free_queue_nodes(sg, free) * q_create_buffer(start, size, slots) * undef_data_at(&pq, OS_Q *)
        */
        pq = OSQFreeList;
        if (pq != (OS_Q *)0) {
            /*@ Assert exists (second_call : OsSchedCallContext) (entry : UCOS2_Verify_State)
                (eid : EventID) (allocation : EventPrivateAllocation) (qid : QueueID) (rest : list QueueID),
                start == start@pre && size == size@pre &&
        q_create_input_facts(critical, sg, call, initial, start, size, slots, X) &&
                task_tcb_init_stack_same_call(second_call, call) && interrupt_saved_value(mask, cpu_sr) &&
                pevent == event_pool_addr(sg, eid) && pq == qcb_addr(sg, qid) &&
                q_create_event_history(critical, sg, os_sched_call_invocation(call), initial, eid, allocation, entry) &&
                UCOS2_state_inv(sg, entry) && queue_pool_partition(sg, EventState(entry), cons(qid, rest)) &&
                q_create_private_lookup(entry, eid, allocation) &&
                q_create_masked_control(environment, critical, sg, second_call, cpu_sr, entry, entry) *
                event_private_storage_rep(sg, eid, allocation) * q_create_queue_pool_frame(sg, entry) *
                data_at(&OSQFreeList, OS_Q *, pq) * data_at(&pq->OSQPtr, OS_Q *, queue_free_head(sg, rest)) *
                q_create_free_qcb_without_link(sg, qid, queue_free_head(sg, rest)) *
                store_free_queue_nodes(sg, rest) * q_create_buffer(start, size, slots)
            */
            OSQFreeList            = OSQFreeList->OSQPtr;
            /*@ Assert start == start@pre && size == size@pre &&
        q_create_input_facts(critical, sg, call, initial, start, size, slots, X) &&
                q_create_reservation_cut(environment, critical, sg, call, initial, mask, cpu_sr,
                  start, size, slots, pevent, pq)
            */
            /*@ q_create_reservation_cut(environment, critical, sg, call, initial, mask, cpu_sr,
                  start, size, slots, pevent, pq)
                which implies exists (second_call : OsSchedCallContext) (acquired reserved : UCOS2_Verify_State)
                  (eid : EventID) (allocation : EventPrivateAllocation) (qid : QueueID) (image : QCBStorage),
                task_tcb_init_stack_same_call(second_call, call) && interrupt_saved_value(mask, cpu_sr) &&
                pevent == event_pool_addr(sg, eid) && pq == qcb_addr(sg, qid) &&
                q_create_success_history(critical, sg, os_sched_call_invocation(call), initial, eid, allocation, qid, reserved) &&
                q_create_restore_input(environment, critical, QCreatePrivateQueue(eid, allocation, qid, image),
                  q_create_buffer(start, size, slots), sg, second_call, cpu_sr, acquired, reserved)
            */
            OS_EXIT_CRITICAL();
            /*@ Assert exists (eid : EventID) (allocation : EventPrivateAllocation) (qid : QueueID)
                (reserved : UCOS2_Verify_State) (image : QCBStorage),
                start == start@pre && size == size@pre &&
        q_create_input_facts(critical, sg, call, initial, start, size, slots, X) &&
                pevent == event_pool_addr(sg, eid) && pq == qcb_addr(sg, qid) &&
                interrupt_saved_value(mask, cpu_sr) &&
                q_create_buffer_bounds(start, size) &&
                q_create_initialization_context(environment, critical, sg, call, initial, mask,
                  eid, allocation, qid, reserved, start, size, slots) *
                q_create_qcb_link(sg, qid, image) *
                undef_data_at(&pq->OSQStart, void **) * undef_data_at(&pq->OSQEnd, void **) *
                undef_data_at(&pq->OSQIn, void **) * undef_data_at(&pq->OSQOut, void **) *
                undef_data_at(&pq->OSQSize, INT16U) * undef_data_at(&pq->OSQEntries, INT16U) *
                undef_data_at(&pevent->OSEventType, INT8U) * undef_data_at(&pevent->OSEventCnt, INT16U) *
                undef_data_at(&pevent->OSEventPtr, void *) *
                event_wait_list_init_pre(&pevent->OSEventGrp, pevent->OSEventTbl) *
                sem_create_initialization_frame(pevent, eventPrivateStorage(allocation))
            */
            pq->OSQStart           = start;
            /*@ q_create_buffer_bounds(start, size)
                which implies q_create_buffer_bounds(start, size) &&
                0 <= start + size && start + size <= 4294967295
            */
            pq->OSQEnd             = &start[size];
            pq->OSQIn              = start;
            pq->OSQOut             = start;
            pq->OSQSize            = size;
            pq->OSQEntries         = 0u;
            pevent->OSEventType    = OS_EVENT_TYPE_Q;
            pevent->OSEventCnt     = 0u;
            pevent->OSEventPtr     = pq;
#if OS_EVENT_NAME_EN > 0u
            pevent->OSEventName    = (INT8U *)(void *)"?";
#endif
            OS_EventWaitListInit(pevent);
            OS_TRACE_Q_CREATE(pevent, pevent->OSEventName);
            /*@ Assert start == start@pre && size == size@pre &&
                q_create_call_post(environment, critical, sg, call, mask, start, size, slots, pevent, X) *
                undef_data_at(&pq, OS_Q *) * undef_data_at(&cpu_sr, OS_CPU_SR) */
        } else {
            /*@ Assert exists (second_call : OsSchedCallContext) (entry : UCOS2_Verify_State)
                (eid : EventID) (allocation : EventPrivateAllocation),
                start == start@pre && size == size@pre &&
        q_create_input_facts(critical, sg, call, initial, start, size, slots, X) &&
                task_tcb_init_stack_same_call(second_call, call) && interrupt_saved_value(mask, cpu_sr) &&
                pq == 0 &&
                pevent == event_pool_addr(sg, eid) &&
                q_create_event_history(critical, sg, os_sched_call_invocation(call), initial, eid, allocation, entry) &&
                UCOS2_state_inv(sg, entry) && queue_pool_partition(sg, EventState(entry), nil) &&
                q_create_private_lookup(entry, eid, allocation) &&
                q_create_masked_control(environment, critical, sg, second_call, cpu_sr, entry, entry) *
                data_at(&OSEventFreeList, OS_EVENT *, sem_create_pool_head(sg, entry)) *
                undef_data_at(&pevent->OSEventPtr, void *) * q_create_rollback_frame(sg, entry, eid, allocation) *
                q_create_buffer(start, size, slots)
            */
            pevent->OSEventPtr = (void *)OSEventFreeList;
            OSEventFreeList    = pevent;
            /*@ Assert start == start@pre && size == size@pre &&
        q_create_input_facts(critical, sg, call, initial, start, size, slots, X) &&
                q_create_rollback_cut(environment, critical, sg, call, initial, mask, cpu_sr, start, size, slots) *
                undef_data_at(&pq, OS_Q *) * undef_data_at(&pevent, OS_EVENT *)
            */
            /*@ q_create_rollback_cut(environment, critical, sg, call, initial, mask, cpu_sr, start, size, slots)
                which implies exists (second_call : OsSchedCallContext) (acquired rolled_back : UCOS2_Verify_State),
                task_tcb_init_stack_same_call(second_call, call) && interrupt_saved_value(mask, cpu_sr) &&
                q_create_error_history(critical, sg, os_sched_call_invocation(call), initial, rolled_back) &&
                q_create_restore_input(environment, critical, QCreateNoPrivate, q_create_buffer(start, size, slots),
                  sg, second_call, cpu_sr, acquired, rolled_back)
            */
            OS_EXIT_CRITICAL();
            pevent = (OS_EVENT *)0;
            /*@ Assert start == start@pre && size == size@pre &&
                q_create_call_post(environment, critical, sg, call, mask, start, size, slots, pevent, X) *
                undef_data_at(&pq, OS_Q *) * undef_data_at(&cpu_sr, OS_CPU_SR) */
        }
    }
    /*@ Assert start == start@pre && size == size@pre &&
                q_create_call_post(environment, critical, sg, call, mask, start, size, slots, pevent, X) *
        undef_data_at(&pq, OS_Q *) * undef_data_at(&cpu_sr, OS_CPU_SR) */
    return (pevent);
}
