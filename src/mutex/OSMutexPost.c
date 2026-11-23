/* Single-function annotation carrier; compose before canonical QCP.
 * The environment retains the pinned headers, configuration and callees.
 * Formatting and documented frontend form match the checked C input.
 */

INT8U  OSMutexPost (OS_EVENT *pevent)





/*@ With (source_env: MutexDelCallEnvironment) (saved_local: Armv7aContinuation -> Assertion)
         (external: OsSchedExternalResources) (platform: InterruptPlatformResources)
         (critical: CriticalRegionResources) (sg: StableGlobVars) (call: OsSchedCallContext)
         (invocation: nat) (origin: TaskInvocationOrigin) (mask: Z)
         (before: UCOS2_Verify_State) (eid: Z) (observed: OSEventAbstractState) (pe: Z) X
    Require pevent == pe &&
      mutex_post_api_refinement_pre(source_env, critical, sg, call, pe, eid, observed, before, X) &&
      g_OSIntNesting(sg) == &OSIntNesting && g_OSTCBCur(sg) == &OSTCBCur &&
      g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl && g_OSPrioCur(sg) == &OSPrioCur &&
      g_OSRdyGrp(sg) == &OSRdyGrp && g_OSRdyTbl(sg) == &OSRdyTbl &&
      g_OSUnMapTbl(sg) == &OSUnMapTbl && mutex_post_api_layout(sg) &&
      mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) && mutex_del_continuation_entry(source_env, external, platform, saved_local, sg, call, mask, before)
    Ensure mutex_post_api_return_post(source_env, external, platform, critical, saved_local, sg, call, mask,
      pe, before, eid, observed, __return, X)
*/
{
    INT8U      pcp;                                   /* Priority ceiling priority                     */
    INT8U      prio;
#if OS_CRITICAL_METHOD == 3u                          /* Allocate storage for CPU status register      */
    OS_CPU_SR  cpu_sr = 0u;
#endif


    




















/*@ mutex_del_continuation_entry(source_env, external, platform, saved_local, sg, call, mask, before)
 which implies
 mutex_post_api_entry_frame(source_env, external, platform, saved_local, sg, call, mask, before) * UCOS2_inv(sg, before) */

/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        (UCOS2_inv(sg, before))
        which implies
        UCOS2_state_inv(sg, before) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        data_at(&OSIntNesting, INT8U, intNesting(before.IntrState)) *
        mutex_post_nesting_frame(sg, before) */
if (OSIntNesting > 0u) {                          /* See if called from ISR ...                    */
        




















/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        (data_at(&OSIntNesting, INT8U, intNesting(before.IntrState)) *
            mutex_post_nesting_frame(sg, before))
        which implies UCOS2_inv(sg, before) */

/*@ mutex_post_api_entry_frame(source_env, external, platform, saved_local, sg, call, mask, before) * UCOS2_inv(sg, before)
 which implies
 mutex_del_continuation_entry(source_env, external, platform, saved_local, sg, call, mask, before) */
return (OS_ERR_POST_ISR);                     /* ... can't POST mutex from an ISR              */
    }
#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {                    /* Validate 'pevent'                             */
        




















/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        (data_at(&OSIntNesting, INT8U, intNesting(before.IntrState)) *
            mutex_post_nesting_frame(sg, before))
        which implies UCOS2_inv(sg, before) */

/*@ mutex_post_api_entry_frame(source_env, external, platform, saved_local, sg, call, mask, before) * UCOS2_inv(sg, before)
 which implies
 mutex_del_continuation_entry(source_env, external, platform, saved_local, sg, call, mask, before) */
return (OS_ERR_PEVENT_NULL);
    }
#endif

    OS_TRACE_MUTEX_POST_ENTER(pevent);

    




















/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        (data_at(&OSIntNesting, INT8U, intNesting(before.IntrState)) *
        mutex_post_nesting_frame(sg, before))
        which implies UCOS2_inv(sg, before) */

/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        (UCOS2_inv(sg, before))
        which implies
        sem_query_public_slot(before, eid, observed) && pe == event_addr(sg, eid) &&
        event_object_layout_prop(sg, eid) &&
        data_at(&((OS_EVENT *)pe)->OSEventType, INT8U, event_slot_type_value(before.EventState, eid)) *
        sem_query_type_frame(sg, before, eid) */
if (pevent->OSEventType != OS_EVENT_TYPE_MUTEX) { /* Validate event block type                     */
        




















/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        (data_at(&((OS_EVENT *)pe)->OSEventType, INT8U, event_slot_type_value(before.EventState, eid)) *
            sem_query_type_frame(sg, before, eid))
        which implies UCOS2_inv(sg, before) */

/*@ mutex_post_api_entry_frame(source_env, external, platform, saved_local, sg, call, mask, before) * UCOS2_inv(sg, before)
 which implies
 mutex_del_continuation_entry(source_env, external, platform, saved_local, sg, call, mask, before) */
OS_TRACE_MUTEX_POST_EXIT(OS_ERR_EVENT_TYPE);
        return (OS_ERR_EVENT_TYPE);
    }
    




















/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        (data_at(&((OS_EVENT *)pe)->OSEventType, INT8U, event_slot_type_value(before.EventState, eid)) *
        sem_query_type_frame(sg, before, eid))
        which implies UCOS2_inv(sg, before) */

/*@ mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) && intNesting(before.IntrState) <= 0 && pe != 0 &&
unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
mutex_post_api_entry_frame(source_env, external, platform, saved_local, sg, call, mask, before) * UCOS2_inv(sg, before)
 which implies
 mutex_post_api_save_pre(source_env, external, platform, critical, saved_local, sg, call, mask, before) */
OS_ENTER_CRITICAL();
    




















































/*@ mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) && intNesting(before.IntrState) <= 0 && pe != 0 &&
unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
mutex_post_api_save_post(source_env, external, platform, critical, saved_local, sg, call, mask, cpu_sr, before)
 which implies
 exists (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (mutex: MutexFields),
critical_region_interval(critical, sg, invocation, before, acquired) && interrupt_saved_value(mask, cpu_sr) &&
mutex_query_lookup(acquired, eid, current) && eventType(current) == mutex_post_kind && mutexFields(current) == Some(mutex) &&
eventGeneration(current) == eventGeneration(observed) && mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
UCOS2_state_inv(sg, acquired) && mutex_post_api_stage(sg, call, acquired) &&
critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) * UCOS2_inv(sg, acquired) * unmap_table_rep(sg) * mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, call, acquired) */

/*@ Given acquired current mutex */

/*@ mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) && mutex_post_api_layout(sg) && mutex_post_api_stage(sg, call, acquired) && UCOS2_inv(sg, acquired)
 which implies
 exists (caller: Z) (node: TaskAbstractState),
mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
curTaskID(acquired.SchedState) == Some(caller) && inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
task_slot_addr(sg, caller) != 1 && UCOS2_inv(sg, acquired) */

/*@ Given caller node */

/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        (UCOS2_inv(sg, acquired))
        which implies
        data_at(&((OS_EVENT *)pe)->OSEventCnt, INT16U, encode_event_cnt_value(current)) *
        mutex_post_commit_field_frame(sg, acquired, eid, event_image(sg, acquired.TskState, current), EventCntField) */
pcp  = (INT8U)(pevent->OSEventCnt >> 8u);         /* Get priority ceiling priority of mutex        */
    prio = (INT8U)(pevent->OSEventCnt & OS_MUTEX_KEEP_LOWER_8);  /* Get owner's original priority      */
    










/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        pcp == unsigned_last_nbits(encode_event_cnt_value(current) >> 8, 8) &&
        prio == (encode_event_cnt_value(current) & 255) &&
        (0 <= pcp && pcp <= 255 && 0 <= prio && prio <= 255 && data_at(&((OS_EVENT *)pe)->OSEventCnt, INT16U, encode_event_cnt_value(current)) *
        mutex_post_commit_field_frame(sg, acquired, eid, event_image(sg, acquired.TskState, current), EventCntField))
        which implies pcp == mfPCP(mutex) && prio == mutex_post_snapshot_byte(mutex) &&
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, caller)) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, encode_event_ptr_value(sg, current)) *
        mutex_post_comparison_frame(sg, acquired, eid, event_image(sg, acquired.TskState, current)) */
if (OSTCBCur != (OS_TCB *)pevent->OSEventPtr) {   /* See if posting task owns the MUTEX            */
        


















/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        task_slot_addr(sg, caller) != encode_event_ptr_value(sg, current) &&
        (data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, caller)) *
            data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, encode_event_ptr_value(sg, current)) *
            mutex_post_comparison_frame(sg, acquired, eid, event_image(sg, acquired.TskState, current)))
        which implies mutex_post_critical(sg, eid, caller, acquired, mutex_post_not_owner_error, false, acquired) &&
            UCOS2_inv(sg, acquired) */

/*@ exists saved_value, mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) && intNesting(before.IntrState) <= 0 && pe != 0 &&
unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 && mutex_post_api_stage(sg, call, acquired) && UCOS2_state_inv(sg, acquired) &&
mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) && task_slot_addr(sg, caller) != 1 &&
interrupt_saved_value(mask, saved_value) &&
mutex_post_critical(sg, eid, caller, acquired, mutex_post_not_owner_error, false, acquired) &&
critical_region_masked(platform, critical, sg, invocation, origin, saved_value, acquired) * UCOS2_inv(sg, acquired) * unmap_table_rep(sg) * mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, call, acquired) * data_at(&cpu_sr, OS_CPU_SR, saved_value)
 which implies
 mutex_post_api_restore_pre(source_env, external, platform, critical, saved_local, sg, call, mask, saved_value, acquired, acquired) * data_at(&cpu_sr, OS_CPU_SR, saved_value) */
OS_EXIT_CRITICAL();
        










/*@ exists (checkpoint: UCOS2_Verify_State),
 mutex_post_api_restore_source_post(source_env, external, platform, critical, saved_local, sg, call, mask, checkpoint)
 which implies
 mutex_api_tail_post(source_env, external, platform, critical, saved_local, sg, call, mask, checkpoint, 0) */
OS_TRACE_MUTEX_POST_EXIT(OS_ERR_NOT_MUTEX_OWNER);
        return (OS_ERR_NOT_MUTEX_OWNER);
    }
    










/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        task_slot_addr(sg, caller) == encode_event_ptr_value(sg, current) &&
        (data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, caller)) *
        data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, encode_event_ptr_value(sg, current)) *
        mutex_post_comparison_frame(sg, acquired, eid, event_image(sg, acquired.TskState, current)))
        which implies mfOwner(mutex) == Some(caller) && UCOS2_inv(sg, acquired) */
if (pcp != OS_PRIO_MUTEX_CEIL_DIS) {
        










/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        mfPCP(mutex) != 255 &&
        (pcp == mfPCP(mutex) && UCOS2_inv(sg, acquired))
        which implies 0 <= pcp && pcp < 64 &&
            data_at(pointer_offset(&OSTCBPrioTbl, pcp, OS_TCB *), OS_TCB *, prio_tbl_entry_to_addr(sg, prioTbl(acquired.TskState, pcp))) *
            store_prio_tbl_missing_i(sg, acquired.TskState.prioTbl, pcp) *
            UCOS2_raw_rep_missing_priority_table(sg, acquired) */
OSTCBPrioTbl[pcp] = ((OS_TCB *)1);
        










/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        pcp == mfPCP(mutex) &&
        0 <= pcp && pcp < 64 &&
        mfPCP(mutex) != 255 &&
        (data_at(pointer_offset(&OSTCBPrioTbl, pcp, OS_TCB *), OS_TCB *, 1) *
            store_prio_tbl_missing_i(sg, acquired.TskState.prioTbl, pcp) *
            UCOS2_raw_rep_missing_priority_table(sg, acquired))
        which implies
            tcb64_storage_rep(task_slot_addr(sg, caller), task_tcb64_image(sg, node)) *
            PtrArray::full(&OSTCBPrioTbl, 64, mutex_del_priority_values(sg, mutex_post_reserved_table(acquired, pcp))) *
            UCharArray::full(&OSRdyTbl, 8, sched_row_values(acquired.TskState, acquired.SchedState.readyList)) *
            data_at(&OSRdyGrp, OS_PRIO, encode_ready_grp(acquired.SchedState.readyList, acquired.TskState)) *
            data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, caller)) *
            data_at(&OSPrioCur, INT8U, sched_priority_byte(acquired.SchedState.curSchedPrio)) *
            mutex_del_priority_frame(sg, acquired, caller) */
prio = OSMutex_EffectivePrio(OSTCBCur)










/*@ where
            image = task_tcb64_image(sg, node),
            table = mutex_del_priority_values(sg, mutex_post_reserved_table(acquired, pcp)),
            fallback = curPrio(node) */
;
        










/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        mfPCP(mutex) != 255 &&
        mutex_effective_priority_result(mutex_del_priority_values(sg, mutex_post_reserved_table(acquired, mfPCP(mutex))), task_slot_addr(sg, caller), curPrio(node), prio) &&
        (0 <= prio && prio <= 255 && tcb64_storage_rep(task_slot_addr(sg, caller), task_tcb64_image(sg, node)))
        which implies 0 <= prio && prio < 64 && task_slot_addr(sg, caller) != 1 &&
            data_at(&((OS_TCB *)task_slot_addr(sg, caller))->OSTCBPrio, INT8U, curPrio(node)) *
            tcb64_storage_without(task_slot_addr(sg, caller), TCBPrio, task_tcb64_image(sg, node)) */
if (OSTCBCur->OSTCBPrio != prio) {
            










/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        mfPCP(mutex) != 255 &&
        (data_at(&((OS_TCB *)task_slot_addr(sg, caller))->OSTCBPrio, INT8U, curPrio(node)) *
                tcb64_storage_without(task_slot_addr(sg, caller), TCBPrio, task_tcb64_image(sg, node)))
        which implies tcb64_storage_rep(task_slot_addr(sg, caller), task_tcb64_image(sg, node)) */
OS_TRACE_MUTEX_TASK_PRIO_DISINHERIT(OSTCBCur, prio);
            OSMutex_RdyAtPrio(OSTCBCur, prio)










/*@ where
                image = task_tcb64_image(sg, node),
                table = mutex_del_priority_values(sg, mutex_post_reserved_table(acquired, pcp)),
                rows = sched_row_values(acquired.TskState, acquired.SchedState.readyList),
                old_prio = curPrio(node), old_x = tcb_x_of_prio(curPrio(node)),
                old_y = tcb_y_of_prio(curPrio(node)), old_bitx = tcb_bit_x_of_prio(curPrio(node)),
                old_bity = tcb_bit_y_of_prio(curPrio(node)),
                group = encode_ready_grp(acquired.SchedState.readyList, acquired.TskState),
                current = task_slot_addr(sg, caller),
                current_prio = sched_priority_byte(acquired.SchedState.curSchedPrio) */
;
        










/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        pcp == mfPCP(mutex) &&
        mfPCP(mutex) != 255 &&
        mutex_effective_priority_result(mutex_del_priority_values(sg, mutex_post_reserved_table(acquired, mfPCP(mutex))), task_slot_addr(sg, caller), curPrio(node), prio) &&
        task_slot_addr(sg, caller) != 1 &&
        curPrio(node) != prio &&
        (tcb64_storage_rep(task_slot_addr(sg, caller), mutex_priority_image(task_tcb64_image(sg, node), prio)) *
                PtrArray::full(&OSTCBPrioTbl, 64, replace_Znth(prio, task_slot_addr(sg, caller), mutex_del_priority_values(sg, mutex_post_reserved_table(acquired, pcp)))) *
                UCharArray::full(&OSRdyTbl, 8, mutex_priority_rows(sched_row_values(acquired.TskState, acquired.SchedState.readyList), tcb_y_of_prio(curPrio(node)), tcb_bit_x_of_prio(curPrio(node)), prio)) *
                data_at(&OSRdyGrp, OS_PRIO, mutex_priority_group(sched_row_values(acquired.TskState, acquired.SchedState.readyList), encode_ready_grp(acquired.SchedState.readyList, acquired.TskState), tcb_y_of_prio(curPrio(node)), tcb_bit_x_of_prio(curPrio(node)), tcb_bit_y_of_prio(curPrio(node)), prio)) *
                data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, caller)) *
                data_at(&OSPrioCur, INT8U, mutex_priority_current(task_slot_addr(sg, caller), task_slot_addr(sg, caller), sched_priority_byte(acquired.SchedState.curSchedPrio), prio)) *
                mutex_del_priority_frame(sg, acquired, caller))
        which implies pcp == mfPCP(mutex) && 0 <= prio && prio < 64 &&
                mutex_post_prepare(sg, mutex, caller, acquired, mutex_post_owner_priority_state(sg, acquired, pcp, caller, node, prio)) &&
            UCOS2_inv(sg, mutex_post_owner_priority_state(sg, acquired, pcp, caller, node, prio)) */
}
    










/*@ (g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        pcp == mfPCP(mutex) &&
        mfPCP(mutex) != 255 &&
        mutex_effective_priority_result(mutex_del_priority_values(sg, mutex_post_reserved_table(acquired, mfPCP(mutex))), task_slot_addr(sg, caller), curPrio(node), prio) &&
        task_slot_addr(sg, caller) != 1 &&
        (curPrio(node) != prio && UCOS2_inv(sg, mutex_post_owner_priority_state(sg, acquired, pcp, caller, node, prio)))) ||
        (g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        pcp == mfPCP(mutex) &&
        mfPCP(mutex) != 255 &&
        mutex_effective_priority_result(mutex_del_priority_values(sg, mutex_post_reserved_table(acquired, mfPCP(mutex))), task_slot_addr(sg, caller), curPrio(node), prio) &&
        task_slot_addr(sg, caller) != 1 &&
        (curPrio(node) == prio && data_at(&((OS_TCB *)task_slot_addr(sg, caller))->OSTCBPrio, INT8U, curPrio(node)) *
             tcb64_storage_without(task_slot_addr(sg, caller), TCBPrio, task_tcb64_image(sg, node)) *
             PtrArray::full(&OSTCBPrioTbl, 64, mutex_del_priority_values(sg, mutex_post_reserved_table(acquired, pcp))) *
             UCharArray::full(&OSRdyTbl, 8, sched_row_values(acquired.TskState, acquired.SchedState.readyList)) *
             data_at(&OSRdyGrp, OS_PRIO, encode_ready_grp(acquired.SchedState.readyList, acquired.TskState)) *
             data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, caller)) *
             data_at(&OSPrioCur, INT8U, sched_priority_byte(acquired.SchedState.curSchedPrio)) * mutex_del_priority_frame(sg, acquired, caller)))
        which implies
        (pcp == mfPCP(mutex) && 0 <= prio && prio < 64 &&
            mutex_post_prepare(sg, mutex, caller, acquired, mutex_post_owner_priority_state(sg, acquired, pcp, caller, node, prio)) &&
            UCOS2_inv(sg, mutex_post_owner_priority_state(sg, acquired, pcp, caller, node, prio))) ||
        (pcp == mfPCP(mutex) && 0 <= prio && prio < 64 &&
            mutex_post_prepare(sg, mutex, caller, acquired, mutex_post_owner_priority_state(sg, acquired, pcp, caller, node, prio)) &&
            UCOS2_inv(sg, mutex_post_owner_priority_state(sg, acquired, pcp, caller, node, prio))) */
}
    






























/*@ (g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        pcp == mfPCP(mutex) &&
        (pcp != 255 && 0 <= prio && prio < 64 && mutex_post_prepare(sg, mutex, caller, acquired, mutex_post_owner_priority_state(sg, acquired, pcp, caller, node, prio)) && UCOS2_inv(sg, mutex_post_owner_priority_state(sg, acquired, pcp, caller, node, prio)))) ||
        (g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        pcp == mfPCP(mutex) &&
        (pcp != 255 && 0 <= prio && prio < 64 && mutex_post_prepare(sg, mutex, caller, acquired, mutex_post_owner_priority_state(sg, acquired, pcp, caller, node, prio)) && UCOS2_inv(sg, mutex_post_owner_priority_state(sg, acquired, pcp, caller, node, prio)))) ||
        (g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        pcp == mfPCP(mutex) &&
        (pcp == 255 && 0 <= prio && prio <= 255 && UCOS2_inv(sg, acquired)))
        which implies
        (exists (prepared: UCOS2_Verify_State),
        pcp == mfPCP(mutex) && 0 <= prio && prio <= 255 &&
        mutex_post_prepare(sg, mutex, caller, acquired, prepared) &&
        mutex_query_lookup(prepared, eid, current) &&
        UCOS2_state_inv(sg, prepared) &&
        UCOS2_inv(sg, prepared)) ||
        (exists (prepared: UCOS2_Verify_State),
        pcp == mfPCP(mutex) && 0 <= prio && prio <= 255 &&
        mutex_post_prepare(sg, mutex, caller, acquired, prepared) &&
        mutex_query_lookup(prepared, eid, current) &&
        UCOS2_state_inv(sg, prepared) &&
        UCOS2_inv(sg, prepared)) ||
        (exists (prepared: UCOS2_Verify_State),
        pcp == mfPCP(mutex) && 0 <= prio && prio <= 255 &&
        mutex_post_prepare(sg, mutex, caller, acquired, prepared) &&
        mutex_query_lookup(prepared, eid, current) &&
        UCOS2_state_inv(sg, prepared) &&
        UCOS2_inv(sg, prepared)) */

/*@ Given prepared */

/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        mutex_post_prepare(sg, mutex, caller, acquired, prepared) &&
        mutex_query_lookup(prepared, eid, current) &&
        UCOS2_state_inv(sg, prepared) &&
        (UCOS2_inv(sg, prepared))
        which implies
        data_at(&((OS_EVENT *)pe)->OSEventGrp, OS_PRIO, encode_event_wait_grp(waitList(current), prepared.TskState)) *
        mutex_post_commit_field_frame(sg, prepared, eid, event_image(sg, prepared.TskState, current), EventGrpField) */
if (pevent->OSEventGrp != 0u) {                   /* Any task waiting for the mutex?               */
                                                      /* Yes, Make HPT waiting for mutex ready         */
        




















/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        mutex_post_prepare(sg, mutex, caller, acquired, prepared) &&
        mutex_query_lookup(prepared, eid, current) &&
        UCOS2_state_inv(sg, prepared) &&
        unsigned_last_nbits(encode_event_wait_grp(waitList(current), prepared.TskState), 32) != 0 &&
        (data_at(&((OS_EVENT *)pe)->OSEventGrp, OS_PRIO, encode_event_wait_grp(waitList(current), prepared.TskState)) *
            mutex_post_commit_field_frame(sg, prepared, eid, event_image(sg, prepared.TskState, current), EventGrpField) *
            unmap_table_rep(sg))
        which implies exists (waiter: Z) (waiting: TaskAbstractState),
            event_task_rdy_entry(sg, prepared.TskState, eid, current, waiter, waiting) &&
            event_task_rdy_pre(sg, prepared.TskState, eid, current, waiter, waiting, 16, 0,
              encode_ready_grp(prepared.SchedState.readyList, prepared.TskState),
              sched_row_values(prepared.TskState, prepared.SchedState.readyList)) *
            mutex_del_wake_frame(sg, prepared, eid, waiter) */

/*@ Given waiter waiting */
prio                = OS_EventTaskRdy(pevent, (void *)0, OS_STAT_MUTEX, OS_STAT_PEND_OK)










/*@ where
            sg = sg, tasks = prepared.TskState, eid = eid, e = current, tid = waiter, t = waiting,
            group = encode_ready_grp(prepared.SchedState.readyList, prepared.TskState),
            rows = sched_row_values(prepared.TskState, prepared.SchedState.readyList) */
;
        




















/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        mutex_post_prepare(sg, mutex, caller, acquired, prepared) &&
        mutex_query_lookup(prepared, eid, current) &&
        UCOS2_state_inv(sg, prepared) &&
        unsigned_last_nbits(encode_event_wait_grp(waitList(current), prepared.TskState), 32) != 0 &&
        event_task_rdy_entry(sg, prepared.TskState, eid, current, waiter, waiting) &&
        (event_task_rdy_post(sg, prepared.TskState, eid, current, waiter, waiting, 0, 16, 0,
              encode_ready_grp(prepared.SchedState.readyList, prepared.TskState),
              sched_row_values(prepared.TskState, prepared.SchedState.readyList), prio) *
            mutex_del_wake_frame(sg, prepared, eid, waiter))
        which implies exists (woken: UCOS2_Verify_State) (found: OSEventAbstractState),
            woken == event_wake_state(sg, prepared, eid, current, waiter, waiting, PendMutex, 0, PendOK) &&
            found == event_set_wait_list(current, remove_Z_eqb(waiter, waitList(current))) &&
            mutex_query_lookup(woken, eid, found) &&
            eventType(found) == mutex_post_kind && mutexFields(found) == Some(mutex) &&
            UCOS2_state_inv(sg, woken) &&
            0 <= prio && prio < 64 &&
            mutex_post_wake_selection(woken.TskState, waiter, waiting, prio) &&
            data_at(&((OS_EVENT *)pe)->OSEventCnt, INT16U, encode_event_cnt_value(found)) *
            mutex_post_commit_field_frame(sg, woken, eid, event_image(sg, woken.TskState, found), EventCntField) *
            unmap_table_rep(sg) */

/*@ Given woken found */
pevent->OSEventCnt &= OS_MUTEX_KEEP_UPPER_8;  /*      Save priority of mutex's new owner       */
        pevent->OSEventCnt |= (INT16U)prio;
        










/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        mutex_post_prepare(sg, mutex, caller, acquired, prepared) &&
        mutex_query_lookup(prepared, eid, current) &&
        UCOS2_state_inv(sg, prepared) &&
        unsigned_last_nbits(encode_event_wait_grp(waitList(current), prepared.TskState), 32) != 0 &&
        event_task_rdy_entry(sg, prepared.TskState, eid, current, waiter, waiting) &&
        woken == event_wake_state(sg, prepared, eid, current, waiter, waiting, PendMutex, 0, PendOK) &&
        found == event_set_wait_list(current, remove_Z_eqb(waiter, waitList(current))) &&
        mutex_query_lookup(woken, eid, found) &&
        eventType(found) == mutex_post_kind &&
        mutexFields(found) == Some(mutex) &&
        UCOS2_state_inv(sg, woken) &&
        mutex_post_wake_selection(woken.TskState, waiter, waiting, prio) &&
        (data_at(&((OS_EVENT *)pe)->OSEventCnt, INT16U,
              (encode_event_cnt_value(found) & 65280) | prio) *
            mutex_post_commit_field_frame(sg, woken, eid, event_image(sg, woken.TskState, found), EventCntField))
        which implies
            data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, encode_event_ptr_value(sg, found)) *
            data_at(pointer_offset(&OSTCBPrioTbl, prio, OS_TCB *), OS_TCB *, task_slot_addr(sg, waiter)) *
            mutex_post_native_owner_store_frame(sg, woken, eid,
              event_write(event_image(sg, woken.TskState, found), EventCntField,
                Some((encode_event_cnt_value(found) & 65280) | prio)), prio) */
pevent->OSEventPtr  = OSTCBPrioTbl[prio];     /*      Link to new mutex owner's OS_TCB         */
        




















/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        mutex_post_prepare(sg, mutex, caller, acquired, prepared) &&
        mutex_query_lookup(prepared, eid, current) &&
        UCOS2_state_inv(sg, prepared) &&
        unsigned_last_nbits(encode_event_wait_grp(waitList(current), prepared.TskState), 32) != 0 &&
        event_task_rdy_entry(sg, prepared.TskState, eid, current, waiter, waiting) &&
        woken == event_wake_state(sg, prepared, eid, current, waiter, waiting, PendMutex, 0, PendOK) &&
        found == event_set_wait_list(current, remove_Z_eqb(waiter, waitList(current))) &&
        mutex_query_lookup(woken, eid, found) &&
        eventType(found) == mutex_post_kind &&
        mutexFields(found) == Some(mutex) &&
        UCOS2_state_inv(sg, woken) &&
        mutex_post_wake_selection(woken.TskState, waiter, waiting, prio) &&
        (data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, task_slot_addr(sg, waiter)) *
            data_at(pointer_offset(&OSTCBPrioTbl, prio, OS_TCB *), OS_TCB *, task_slot_addr(sg, waiter)) *
            mutex_post_native_owner_store_frame(sg, woken, eid,
              event_write(event_image(sg, woken.TskState, found), EventCntField,
                Some((encode_event_cnt_value(found) & 65280) | prio)), prio))
        which implies exists (committed: UCOS2_Verify_State),
            committed == mutex_post_owner_state(woken, eid, found, mutex, Some(waiter), Some(prio)) &&
            mutex_post_critical(sg, eid, caller, acquired, mutex_post_handover_error(sg, mutex, prio), true, committed) &&
            UCOS2_inv(sg, committed) */

/*@ Given committed */
if ((pcp  != OS_PRIO_MUTEX_CEIL_DIS) &&
            (prio <= pcp)) {                          /*      PCP 'must' have a SMALLER prio ...       */
            








/*@ exists saved_value priority_value, mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) && intNesting(before.IntrState) <= 0 && pe != 0 &&
unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 && mutex_post_api_stage(sg, call, acquired) && UCOS2_state_inv(sg, acquired) &&
mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) && task_slot_addr(sg, caller) != 1 &&
interrupt_saved_value(mask, saved_value) &&
mutex_post_critical(sg, eid, caller, acquired, mutex_post_handover_error(sg, mutex, priority_value), true, committed) &&
critical_region_masked(platform, critical, sg, invocation, origin, saved_value, acquired) * UCOS2_inv(sg, committed) * unmap_table_rep(sg) * mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, call, acquired) * data_at(&cpu_sr, OS_CPU_SR, saved_value) * data_at(&prio, INT8U, priority_value)
 which implies
 mutex_post_api_restore_pre(source_env, external, platform, critical, saved_local, sg, call, mask, saved_value, acquired, committed) * data_at(&cpu_sr, OS_CPU_SR, saved_value) * data_at(&prio, INT8U, priority_value) */
OS_EXIT_CRITICAL();                       /*      ... than current task!                   */
            










/*@ exists (checkpoint: UCOS2_Verify_State),
 mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) && mutex_post_api_layout(sg) && intNesting(before.IntrState) <= 0 && pe != 0 &&
 unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
 mutex_post_api_restore_source_post(source_env, external, platform, critical, saved_local, sg, call, mask, checkpoint)
 which implies
 exists (restored: OsSchedCallContext) (unmasked: UCOS2_Verify_State),
 mutex_del_callsite_environment(source_env, external, platform) &&
 kernel_stack_call_same_call(restored, call) &&
 mutex_api_restore_history(source_env, critical, sg, call, checkpoint, restored, unmasked) &&
 os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
   &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 kernel_sched_ready_clients(critical) &&
 os_sched_continuation_call_pre(mutex_del_runtime_sched_environment(source_env), saved_local,
   mutex_del_stack_resources, sg, restored, mask, unmasked) */
OS_Sched();                               /*      Find highest priority task ready to run  */
            












/*@ exists (restored: OsSchedCallContext) (unmasked checkpoint: UCOS2_Verify_State),
 mutex_del_callsite_environment(source_env, external, platform) &&
 mutex_api_restore_history(source_env, critical, sg, call, checkpoint, restored, unmasked) &&
 sched_del_history_return_post(mutex_del_runtime_sched_environment(source_env), critical,
   saved_local, sg, restored, mask, unmasked)
 which implies
 mutex_api_tail_post(source_env, external, platform, critical, saved_local, sg, call, mask, checkpoint, 1) */
OS_TRACE_MUTEX_POST_EXIT(OS_ERR_PCP_LOWER);
            return (OS_ERR_PCP_LOWER);
        } else {
            








/*@ exists saved_value priority_value, mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) && intNesting(before.IntrState) <= 0 && pe != 0 &&
unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 && mutex_post_api_stage(sg, call, acquired) && UCOS2_state_inv(sg, acquired) &&
mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) && task_slot_addr(sg, caller) != 1 &&
interrupt_saved_value(mask, saved_value) &&
mutex_post_critical(sg, eid, caller, acquired, mutex_post_handover_error(sg, mutex, priority_value), true, committed) &&
critical_region_masked(platform, critical, sg, invocation, origin, saved_value, acquired) * UCOS2_inv(sg, committed) * unmap_table_rep(sg) * mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, call, acquired) * data_at(&cpu_sr, OS_CPU_SR, saved_value) * data_at(&prio, INT8U, priority_value)
 which implies
 mutex_post_api_restore_pre(source_env, external, platform, critical, saved_local, sg, call, mask, saved_value, acquired, committed) * data_at(&cpu_sr, OS_CPU_SR, saved_value) * data_at(&prio, INT8U, priority_value) */
OS_EXIT_CRITICAL();
            










/*@ exists (checkpoint: UCOS2_Verify_State),
 mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) && mutex_post_api_layout(sg) && intNesting(before.IntrState) <= 0 && pe != 0 &&
 unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
 mutex_post_api_restore_source_post(source_env, external, platform, critical, saved_local, sg, call, mask, checkpoint)
 which implies
 exists (restored: OsSchedCallContext) (unmasked: UCOS2_Verify_State),
 mutex_del_callsite_environment(source_env, external, platform) &&
 kernel_stack_call_same_call(restored, call) &&
 mutex_api_restore_history(source_env, critical, sg, call, checkpoint, restored, unmasked) &&
 os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
   &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 kernel_sched_ready_clients(critical) &&
 os_sched_continuation_call_pre(mutex_del_runtime_sched_environment(source_env), saved_local,
   mutex_del_stack_resources, sg, restored, mask, unmasked) */
OS_Sched();                               /*      Find highest priority task ready to run  */
            












/*@ exists (restored: OsSchedCallContext) (unmasked checkpoint: UCOS2_Verify_State),
 mutex_del_callsite_environment(source_env, external, platform) &&
 mutex_api_restore_history(source_env, critical, sg, call, checkpoint, restored, unmasked) &&
 sched_del_history_return_post(mutex_del_runtime_sched_environment(source_env), critical,
   saved_local, sg, restored, mask, unmasked)
 which implies
 mutex_api_tail_post(source_env, external, platform, critical, saved_local, sg, call, mask, checkpoint, 1) */
OS_TRACE_MUTEX_POST_EXIT(OS_ERR_NONE);
            return (OS_ERR_NONE);
        }
    }
    










/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        mutex_post_prepare(sg, mutex, caller, acquired, prepared) &&
        mutex_query_lookup(prepared, eid, current) &&
        UCOS2_state_inv(sg, prepared) &&
        unsigned_last_nbits(encode_event_wait_grp(waitList(current), prepared.TskState), 32) == 0 &&
        (data_at(&((OS_EVENT *)pe)->OSEventGrp, OS_PRIO, encode_event_wait_grp(waitList(current), prepared.TskState)) *
        mutex_post_commit_field_frame(sg, prepared, eid, event_image(sg, prepared.TskState, current), EventGrpField))
        which implies data_at(&((OS_EVENT *)pe)->OSEventCnt, INT16U, encode_event_cnt_value(current)) *
        mutex_post_commit_field_frame(sg, prepared, eid, event_image(sg, prepared.TskState, current), EventCntField) */
pevent->OSEventCnt |= OS_MUTEX_AVAILABLE;         /* No,  Mutex is now available                   */
    










/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        mutex_post_prepare(sg, mutex, caller, acquired, prepared) &&
        mutex_query_lookup(prepared, eid, current) &&
        UCOS2_state_inv(sg, prepared) &&
        unsigned_last_nbits(encode_event_wait_grp(waitList(current), prepared.TskState), 32) == 0 &&
        (data_at(&((OS_EVENT *)pe)->OSEventCnt, INT16U, unsigned_last_nbits(encode_event_cnt_value(current), 16) | 255) *
        mutex_post_commit_field_frame(sg, prepared, eid, event_image(sg, prepared.TskState, current), EventCntField))
        which implies data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, encode_event_ptr_value(sg, current)) *
        mutex_post_commit_field_frame(sg, prepared, eid,
          event_write(event_image(sg, prepared.TskState, current), EventCntField,
            Some(encode_event_cnt_value(current) | 255)), EventPtrField) */
pevent->OSEventPtr  = (void *)0;
    




























/*@ g_OSIntNesting(sg) == &OSIntNesting &&
        g_OSTCBCur(sg) == &OSTCBCur &&
        g_OSTCBPrioTbl(sg) == &OSTCBPrioTbl &&
        g_OSPrioCur(sg) == &OSPrioCur &&
        g_OSRdyGrp(sg) == &OSRdyGrp &&
        g_OSRdyTbl(sg) == &OSRdyTbl &&
        g_OSUnMapTbl(sg) == &OSUnMapTbl &&
        mutex_post_api_layout(sg) &&
        mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) &&
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        intNesting(before.IntrState) <= 0 &&
        pe != 0 &&
        pe == event_addr(sg, eid) &&
        sem_query_public_slot(before, eid, observed) &&
        event_object_layout_prop(sg, eid) &&
        unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 &&
        critical_region_interval(critical, sg, invocation, before, acquired) &&
        mutex_query_lookup(acquired, eid, current) &&
        eventType(current) == mutex_post_kind &&
        mutexFields(current) == Some(mutex) &&
        eventGeneration(current) == eventGeneration(observed) &&
        mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) &&
        UCOS2_state_inv(sg, acquired) &&
        mutex_post_native_caller(sg, invocation, origin, acquired, call, caller, node) &&
        curTaskID(acquired.SchedState) == Some(caller) &&
        inUsedTaskStates(acquired.TskState, caller) == Some(node) &&
        mfOwner(mutex) == Some(caller) &&
        mutex_post_prepare(sg, mutex, caller, acquired, prepared) &&
        mutex_query_lookup(prepared, eid, current) &&
        UCOS2_state_inv(sg, prepared) &&
        unsigned_last_nbits(encode_event_wait_grp(waitList(current), prepared.TskState), 32) == 0 &&
        (data_at(&((OS_EVENT *)pe)->OSEventPtr, void *, 0) *
        mutex_post_commit_field_frame(sg, prepared, eid,
          event_write(event_image(sg, prepared.TskState, current), EventCntField,
            Some(encode_event_cnt_value(current) | 255)), EventPtrField))
        which implies exists (committed: UCOS2_Verify_State),
        committed == mutex_post_owner_state(prepared, eid, current, mutex, None, None) &&
        mutex_post_critical(sg, eid, caller, acquired, mutex_post_success, false, committed) &&
        UCOS2_inv(sg, committed) */

/*@ Given committed */

/*@ exists saved_value, mutex_post_api_assumptions(critical, sg, call, invocation, origin, pe, before, eid, observed) && intNesting(before.IntrState) <= 0 && pe != 0 &&
unsigned_last_nbits(event_slot_type_value(before.EventState, eid), 32) == 4 && mutex_post_api_stage(sg, call, acquired) && UCOS2_state_inv(sg, acquired) &&
mutex_owner_event_unlinked(acquired.TskState, acquired.EventState) && task_slot_addr(sg, caller) != 1 &&
interrupt_saved_value(mask, saved_value) &&
mutex_post_critical(sg, eid, caller, acquired, mutex_post_success, false, committed) &&
critical_region_masked(platform, critical, sg, invocation, origin, saved_value, acquired) * UCOS2_inv(sg, committed) * unmap_table_rep(sg) * mutex_del_continuation_acquired(source_env, external, platform, saved_local, sg, call, acquired) * data_at(&cpu_sr, OS_CPU_SR, saved_value)
 which implies
 mutex_post_api_restore_pre(source_env, external, platform, critical, saved_local, sg, call, mask, saved_value, acquired, committed) * data_at(&cpu_sr, OS_CPU_SR, saved_value) */
OS_EXIT_CRITICAL();
    










/*@ exists (checkpoint: UCOS2_Verify_State),
 mutex_post_api_restore_source_post(source_env, external, platform, critical, saved_local, sg, call, mask, checkpoint)
 which implies
 mutex_api_tail_post(source_env, external, platform, critical, saved_local, sg, call, mask, checkpoint, 0) */
OS_TRACE_MUTEX_POST_EXIT(OS_ERR_NONE);
    return (OS_ERR_NONE);
}
