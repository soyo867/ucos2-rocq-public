/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSTaskDel (INT8U prio)
/*@ With (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources) saved_local
         (completed : TaskDeleteCompletedEnvironment) (sg : StableGlobVars) (requested : Z)
         (call : OsSchedCallContext) (mask : Z) (initial : UCOS2_Verify_State) (LitMap : String -> Z)
         (X : Z -> UCOS2_Verify_State -> Prop)
    Require prio == requested &&
      task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
        &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
      os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
        &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
      kernel_sched_ready_clients(critical) &&
      task_delete_safe(environment, critical, sg, requested, LitMap("?"), call, mask, initial, X) &&
      task_delete_entry(environment, critical, saved_local, completed, sg, requested, call, mask, initial) * GlobalStrings(LitMap)
    Ensure task_delete_api_post(environment, critical, saved_local, sg, requested, LitMap("?"), call, mask, initial, __return, X) * GlobalStrings(LitMap)
*/
{
#if (OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u)
    OS_FLAG_NODE *pnode;
#endif
    OS_TCB       *ptcb;
    BOOLEAN       lock_added;
#if OS_CRITICAL_METHOD == 3u                            /* Allocate storage for CPU status register    */
    OS_CPU_SR     cpu_sr = 0u;
#endif



#ifdef OS_SAFETY_CRITICAL_IEC61508
    if (OSSafetyCriticalStartFlag == OS_TRUE) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return (OS_ERR_ILLEGAL_DEL_RUN_TIME);
    }
#endif

    /*@ task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
          &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
        task_delete_entry(environment, critical, saved_local, completed, sg, requested, call, mask, initial)
        which implies
        flag_unlink_layout &&
        data_at(&OSIntNesting, INT8U, task_delete_ints(initial)) *
        wand(task_delete_uchar_cell(&OSIntNesting, task_delete_ints(initial)),
          task_delete_entry(environment, critical, saved_local, completed, sg, requested, call, mask, initial))
    */
    if (OSIntNesting > 0u) {                            /* See if trying to delete from ISR            */
        return (OS_ERR_TASK_DEL_ISR);
    }
    if (prio == OS_TASK_IDLE_PRIO) {                    /* Not allowed to delete idle task             */
        return (OS_ERR_TASK_DEL_IDLE);
    }
#if OS_ARG_CHK_EN > 0u
    if (prio >= OS_LOWEST_PRIO) {                       /* Task priority valid ?                       */
        if (prio != OS_PRIO_SELF) {
            return (OS_ERR_PRIO_INVALID);
        }
    }
#endif

    /*@ task_delete_prefix_passed(sg, requested, initial) &&
        data_at(&OSIntNesting, INT8U, task_delete_ints(initial)) *
        wand(task_delete_uchar_cell(&OSIntNesting, task_delete_ints(initial)),
          task_delete_entry(environment, critical, saved_local, completed, sg, requested, call, mask, initial))
        which implies
        task_delete_static_profile(sg) && 0 <= requested && requested <= 255 &&
        task_delete_c_environment(environment, critical, saved_local, requested, sg, completed) &&
        task_delete_prefix_passed(sg, requested, initial) &&
        task_delete_success_protocol(sg, requested, call, initial) &&
        task_delete_call_closed(environment, saved_local, TaskDeleteLookup(requested), None, sg, call, mask, initial)
    */
    OS_ENTER_CRITICAL();
    /*@ exists (saved_value : Z), data_at(&cpu_sr, OS_CPU_SR, saved_value)
        which implies exists (saved : Z), saved == saved_value && data_at(&cpu_sr, OS_CPU_SR, saved)
    */
    /*@ Given saved */
    /*@ task_delete_static_profile(sg) && 0 <= requested && requested <= 255 &&
        task_delete_prefix_passed(sg, requested, initial) && task_delete_success_protocol(sg, requested, call, initial) &&
        task_delete_save_post(environment, critical, saved_local, requested, TaskDeleteLookup(requested), None,
          sg, call, mask, saved, initial)
        which implies exists (current : OsSchedCallContext) (acquired : UCOS2_Verify_State),
        task_delete_lookup_history(sg, requested, call, initial, current, acquired) &&
        interrupt_saved_value(mask, saved) &&
        task_delete_acquired(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired)
    */
    /*@ Given current acquired */
    if (prio == OS_PRIO_SELF) {                         /* See if requesting to delete self            */
        /*@ requested == 255 &&
            task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
              &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
            task_delete_acquired(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired)
            which implies exists (cid : Z) (caller_node : TaskAbstractState),
            requested == 255 && task_delete_self_binding(sg, acquired, cid, caller_node) &&
            data_at(&OSTCBCur, OS_TCB *, task_delete_current(sg, acquired)) *
            data_at(&(((OS_TCB *)task_delete_current(sg, acquired))->OSTCBPrio), INT8U, curPrio(caller_node)) *
            wand(task_delete_self_cells(sg, acquired, caller_node),
              task_delete_acquired(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired))
        */
        /*@ Given cid caller_node */
        prio = OSTCBCur->OSTCBPrio;                     /* Set priority to delete to current           */
        /*@ requested == 255 && task_delete_self_binding(sg, acquired, cid, caller_node) &&
            task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
              &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
            data_at(&OSTCBCur, OS_TCB *, task_delete_current(sg, acquired)) *
            data_at(&(((OS_TCB *)task_delete_current(sg, acquired))->OSTCBPrio), INT8U, curPrio(caller_node)) *
            wand(task_delete_self_cells(sg, acquired, caller_node),
              task_delete_acquired(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired))
            which implies
            task_delete_selected(sg, requested, acquired, curPrio(caller_node), task_delete_table(sg, acquired, curPrio(caller_node))) &&
            task_delete_acquired(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired)
        */
    }
    /*@ exists (selected : Z), data_at(&prio, INT8U, selected)
        which implies exists (priority : Z), priority == selected && data_at(&prio, INT8U, priority)
    */
    /*@ Given priority */
    /*@ 0 <= priority && priority <= 63 &&
        task_delete_selected(sg, requested, acquired, priority, task_delete_table(sg, acquired, priority)) &&
        task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
          &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
        task_delete_acquired(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired)
        which implies
        0 <= priority && priority <= 63 &&
        task_delete_selected(sg, requested, acquired, priority, task_delete_table(sg, acquired, priority)) &&
        data_at(pointer_offset(OSTCBPrioTbl, priority, sizeof(struct os_tcb *), struct os_tcb *), OS_TCB *, task_delete_table(sg, acquired, priority)) *
        wand(task_delete_ptr_cell(pointer_offset(OSTCBPrioTbl, priority, sizeof(struct os_tcb *), struct os_tcb *), task_delete_table(sg, acquired, priority)),
          task_delete_acquired(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired))
    */
    ptcb = OSTCBPrioTbl[prio];
    /*@ data_at(pointer_offset(OSTCBPrioTbl, priority, sizeof(struct os_tcb *), struct os_tcb *), OS_TCB *, task_delete_table(sg, acquired, priority)) *
        wand(task_delete_ptr_cell(pointer_offset(OSTCBPrioTbl, priority, sizeof(struct os_tcb *), struct os_tcb *), task_delete_table(sg, acquired, priority)),
          task_delete_acquired(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired))
        which implies
        task_delete_acquired(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired)
    */
    if (ptcb == (OS_TCB *)0) {                          /* Task to delete must exist                   */
        /*@ task_delete_acquired(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired)
            which implies
            task_delete_call_masked(environment, critical, saved_local, TaskDeleteStable, None,
              sg, current, saved, acquired, acquired)
        */
        OS_EXIT_CRITICAL();
        return (OS_ERR_TASK_NOT_EXIST);
    }
    if (ptcb == ((OS_TCB *)1)) {                        /* Must not be assigned to Mutex               */
        /*@ task_delete_acquired(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired)
            which implies
            task_delete_call_masked(environment, critical, saved_local, TaskDeleteStable, None,
              sg, current, saved, acquired, acquired)
        */
        OS_EXIT_CRITICAL();
        return (OS_ERR_TASK_DEL);
    }

    /*@ task_delete_selected(sg, requested, acquired, priority, task_delete_table(sg, acquired, priority)) &&
        task_delete_table(sg, acquired, priority) != 0 && task_delete_table(sg, acquired, priority) != 1 &&
        data_at(&ptcb, OS_TCB *, task_delete_table(sg, acquired, priority)) *
        task_delete_acquired(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired)
        which implies exists (tid : Z) (node : TaskAbstractState),
        data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
        task_delete_live_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node)
    */
    /*@ Given tid node */
    /*@ task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
          &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
        task_delete_live_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node)
        which implies
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBY), INT8U, task_delete_tcb_value(sg, node, TCBY)) *
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBBitX), OS_PRIO, task_delete_tcb_value(sg, node, TCBBitX)) *
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBBitY), OS_PRIO, task_delete_tcb_value(sg, node, TCBBitY)) *
        data_at(pointer_offset(OSRdyTbl, task_delete_tcb_value(sg, node, TCBY), sizeof(unsigned char), unsigned char), OS_PRIO, task_delete_ready_row(acquired, node)) *
        data_at(&OSRdyGrp, OS_PRIO, task_delete_ready_group(acquired)) *
        wand(task_delete_ready_cells(sg, acquired, tid, node, true), task_delete_ready_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node))
    */
    OSRdyTbl[ptcb->OSTCBY] &= (OS_PRIO)~ptcb->OSTCBBitX;
    OS_TRACE_TASK_SUSPENDED(ptcb);
    if (OSRdyTbl[ptcb->OSTCBY] == 0u) {                 /* Make task not ready                         */
        OSRdyGrp           &= (OS_PRIO)~ptcb->OSTCBBitY;
    }

#if (OS_EVENT_EN)
    /*@ task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
          &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBY), INT8U, task_delete_tcb_value(sg, node, TCBY)) *
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBBitX), OS_PRIO, task_delete_tcb_value(sg, node, TCBBitX)) *
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBBitY), OS_PRIO, task_delete_tcb_value(sg, node, TCBBitY)) *
        data_at(pointer_offset(OSRdyTbl, task_delete_tcb_value(sg, node, TCBY), sizeof(unsigned char), unsigned char), OS_PRIO, event_task_remove_cleared(task_delete_ready_row(acquired, node), task_delete_tcb_value(sg, node, TCBBitX))) *
        data_at(&OSRdyGrp, OS_PRIO, event_task_remove_group(task_delete_ready_row(acquired, node), task_delete_ready_group(acquired), task_delete_tcb_value(sg, node, TCBBitX), task_delete_tcb_value(sg, node, TCBBitY))) *
        wand(task_delete_ready_cells(sg, acquired, tid, node, true), task_delete_ready_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node))
        which implies
        task_delete_ready_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node)
    */
    /*@ task_delete_ready_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node)
        which implies
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBEventPtr), OS_EVENT *, task_delete_event_handle(sg, node)) *
        wand(task_delete_ptr_cell(tcb_field_address(task_slot_addr(sg, tid), TCBEventPtr), task_delete_event_handle(sg, node)), task_delete_ready_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node))
    */
    if (ptcb->OSTCBEventPtr != (OS_EVENT *)0) {
        /*@ task_delete_event_handle(sg, node) != 0 &&
            data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBEventPtr), OS_EVENT *, task_delete_event_handle(sg, node)) *
            wand(task_delete_ptr_cell(tcb_field_address(task_slot_addr(sg, tid), TCBEventPtr), task_delete_event_handle(sg, node)), task_delete_ready_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node))
            which implies exists (row : Z) (bit_x : Z) (bit_y : Z) (row_value : Z) (group_value : Z),
            data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBEventPtr), OS_EVENT *, task_delete_event_handle(sg, node)) *
            task_delete_event_remove_fields(task_slot_addr(sg, tid),
              &(((OS_EVENT *)task_delete_event_handle(sg, node))->OSEventGrp),
              &(((OS_EVENT *)task_delete_event_handle(sg, node))->OSEventTbl[0]),
              row, bit_x, bit_y, row_value, group_value) *
            wand(event_task_remove_post(task_slot_addr(sg, tid),
              &(((OS_EVENT *)task_delete_event_handle(sg, node))->OSEventGrp),
              &(((OS_EVENT *)task_delete_event_handle(sg, node))->OSEventTbl[0]),
              row, bit_x, bit_y, row_value, group_value),
              task_delete_event_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node))
        */
        /*@ Given row bit_x bit_y row_value group_value */
        OS_EventTaskRemove(ptcb, ptcb->OSTCBEventPtr);  /* Remove this task from any event   wait list */
        /*@ event_task_remove_post(task_slot_addr(sg, tid),
              &(((OS_EVENT *)task_delete_event_handle(sg, node))->OSEventGrp),
              &(((OS_EVENT *)task_delete_event_handle(sg, node))->OSEventTbl[0]),
              row, bit_x, bit_y, row_value, group_value) *
            wand(event_task_remove_post(task_slot_addr(sg, tid),
              &(((OS_EVENT *)task_delete_event_handle(sg, node))->OSEventGrp),
              &(((OS_EVENT *)task_delete_event_handle(sg, node))->OSEventTbl[0]),
              row, bit_x, bit_y, row_value, group_value),
              task_delete_event_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node))
            which implies
            task_delete_event_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node)
        */
    }
#if (OS_EVENT_MULTI_EN > 0u)
    if (ptcb->OSTCBEventMultiPtr != (OS_EVENT **)0) {   /* Remove this task from any events' wait lists*/
        OS_EventTaskRemoveMulti(ptcb, ptcb->OSTCBEventMultiPtr);
    }
#endif
#endif

#if (OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u)
    /*@ Assert
        task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
          &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
          &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        kernel_sched_ready_clients(critical) && interrupt_saved_value(mask, saved) && flag_unlink_layout &&
        task_delete_c_environment(environment, critical, saved_local, requested, sg, completed) &&
        task_delete_safe(environment, critical, sg, requested, LitMap("?"), call, mask, initial, X) &&
        task_delete_event_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node) *
        data_at(&prio, INT8U, priority) * data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&cpu_sr, OS_CPU_SR, saved) * undef_data_at(&lock_added, BOOLEAN) *
        undef_data_at(&pnode, OS_FLAG_NODE *) * GlobalStrings(LitMap)
    */
    /*@ task_delete_event_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node)
        which implies exists (evented : UCOS2_Verify_State) (event_node : TaskAbstractState),
        task_delete_live_history(sg, requested, call, initial, current, acquired, priority, task_slot_addr(sg, tid), tid, node) &&
        task_delete_event_unlinked(task_delete_ready_state(acquired, tid), tid, node, evented, event_node) &&
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBFlagNode), OS_FLAG_NODE *, task_delete_flag_handle(event_node)) *
        wand(task_delete_ptr_cell(tcb_field_address(task_slot_addr(sg, tid), TCBFlagNode), task_delete_flag_handle(event_node)),
          task_delete_masked_raw(environment, critical, saved_local, None, sg, current, saved, acquired, evented))
    */
    /*@ Given evented event_node */
    pnode = ptcb->OSTCBFlagNode;
    if (pnode != (OS_FLAG_NODE *)0) {                   /* If task is waiting on event flag            */
        /*@ flag_unlink_layout && task_delete_flag_handle(event_node) != 0 &&
            task_delete_live_history(sg, requested, call, initial, current, acquired, priority, task_slot_addr(sg, tid), tid, node) &&
            task_delete_event_unlinked(task_delete_ready_state(acquired, tid), tid, node, evented, event_node) &&
            data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBFlagNode), OS_FLAG_NODE *, task_delete_flag_handle(event_node)) *
            wand(task_delete_ptr_cell(tcb_field_address(task_slot_addr(sg, tid), TCBFlagNode), task_delete_flag_handle(event_node)),
              task_delete_masked_raw(environment, critical, saved_local, None, sg, current, saved, acquired, evented))
            which implies exists (waiter : FlagWaiterState),
            flag_unlink_pre(sg, FlagState(evented), task_delete_flag_handle(event_node), waiter, event_node) *
            wand(flag_unlink_post(sg, FlagState(evented), task_delete_flag_handle(event_node), waiter, event_node),
              task_delete_flag_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node))
        */
        /*@ Given waiter */
        OS_FlagUnlink(pnode) /*@ where sg=sg, flags=FlagState(evented), p=task_delete_flag_handle(event_node), w=waiter, t=event_node,
          F=wand(flag_unlink_post(sg, FlagState(evented), task_delete_flag_handle(event_node), waiter, event_node),
            task_delete_flag_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node)) */;                           /* Remove from wait list                       */
        /*@ flag_unlink_post(sg, FlagState(evented), task_delete_flag_handle(event_node), waiter, event_node) *
            wand(flag_unlink_post(sg, FlagState(evented), task_delete_flag_handle(event_node), waiter, event_node),
              task_delete_flag_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node))
            which implies
            task_delete_flag_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node)
        */
    }
#endif

    /*@ Assert
        task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
          &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
          &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        kernel_sched_ready_clients(critical) && interrupt_saved_value(mask, saved) &&
        task_delete_c_environment(environment, critical, saved_local, requested, sg, completed) &&
        task_delete_safe(environment, critical, sg, requested, LitMap("?"), call, mask, initial, X) &&
        task_delete_flag_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node) *
        data_at(&prio, INT8U, priority) * data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&cpu_sr, OS_CPU_SR, saved) * undef_data_at(&lock_added, BOOLEAN) *
        undef_data_at(&pnode, OS_FLAG_NODE *) * GlobalStrings(LitMap)
    */
    /*@ task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
          &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
        task_delete_flag_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node)
        which implies exists (flagged : UCOS2_Verify_State) (flag_node : TaskAbstractState),
        0 <= task_delete_locks(flagged) && task_delete_locks(flagged) <= 255 &&
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBDly), INT32U, task_delete_tcb_value(sg, flag_node, TCBDly)) *
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBStat), INT8U, task_delete_tcb_value(sg, flag_node, TCBStat)) *
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBStatPend), INT8U, task_delete_tcb_value(sg, flag_node, TCBStatPend)) *
        data_at(&OSLockNesting, INT8U, task_delete_locks(flagged)) *
        wand(task_delete_prepare_cells(sg, flagged, tid, flag_node, true),
          task_delete_prepared_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node, task_delete_added_value(flagged)))
    */
    /*@ Given flagged flag_node */
    ptcb->OSTCBDly      = 0u;                           /* Prevent OSTimeTick() from updating          */
    ptcb->OSTCBStat     = OS_STAT_RDY;                  /* Prevent task from being resumed             */
    ptcb->OSTCBStatPend = OS_STAT_PEND_OK;
    lock_added          = OS_FALSE;
    if (OSLockNesting < 255u) {                         /* Make sure we don't context switch           */
        OSLockNesting++;
        lock_added = OS_TRUE;
    }
    /*@ 0 <= task_delete_locks(flagged) && task_delete_locks(flagged) <= 255 &&
        task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
          &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBDly), INT32U, 0) *
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBStat), INT8U, 0) *
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBStatPend), INT8U, 0) *
        data_at(&OSLockNesting, INT8U, task_delete_locks(task_delete_prepare_state(flagged, tid, flag_node))) *
        wand(task_delete_prepare_cells(sg, flagged, tid, flag_node, true),
          task_delete_prepared_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node, task_delete_added_value(flagged)))
        which implies
        0 <= task_delete_locks(flagged) && task_delete_locks(flagged) <= 255 &&
        task_delete_prepared_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node, task_delete_added_value(flagged))
    */
    /*@ Assert
        task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
          &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
          &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        kernel_sched_ready_clients(critical) && interrupt_saved_value(mask, saved) &&
        task_delete_c_environment(environment, critical, saved_local, requested, sg, completed) &&
        task_delete_safe(environment, critical, sg, requested, LitMap("?"), call, mask, initial, X) &&
        task_delete_prepared_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node, task_delete_added_value(flagged)) *
        data_at(&prio, INT8U, priority) * data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&cpu_sr, OS_CPU_SR, saved) * data_at(&lock_added, BOOLEAN, task_delete_added_value(flagged)) *
        undef_data_at(&pnode, OS_FLAG_NODE *) * GlobalStrings(LitMap)
    */
    /*@ task_delete_prepared_body(environment, critical, saved_local, sg, requested, call, initial, current, saved, acquired, priority, task_slot_addr(sg, tid), tid, node, task_delete_added_value(flagged))
        which implies exists (prepared : UCOS2_Verify_State) (loan : option FlagWaiterState),
        task_delete_preparation_history(sg, requested, call, initial, current, acquired, priority, tid, node, prepared, loan) &&
        task_delete_added_value(prepared) == task_delete_added_value(flagged) &&
        task_delete_call_masked(environment, critical, saved_local, TaskDeletePrepared(tid, taskGeneration(node)), loan,
          sg, current, saved, acquired, task_delete_locked(prepared))
    */
    /*@ Given prepared loan */
    OS_EXIT_CRITICAL();                                 /* Enabling INT. ignores next instruc.         */
    /*@ interrupt_saved_value(mask, saved) &&
        task_delete_restore_post(environment, critical, saved_local, requested, TaskDeletePrepared(tid, taskGeneration(node)), loan,
          sg, current, armv7a_irq_fiq_mask(saved), task_delete_locked(prepared))
        which implies exists (middle : OsSchedCallContext) (between : UCOS2_Verify_State),
        task_delete_restore_history(environment, critical, requested, TaskDeletePrepared(tid, taskGeneration(node)), sg,
          current, task_delete_locked(prepared), middle, between) &&
        task_delete_call_closed(environment, saved_local, TaskDeletePrepared(tid, taskGeneration(node)), loan,
          sg, middle, mask, between)
    */
    /*@ Given middle between */
    OS_Dummy() /*@ where F=task_delete_call_closed(environment, saved_local, TaskDeletePrepared(tid, taskGeneration(node)), loan,
      sg, middle, mask, between) */;                     /* ... Dummy ensures that INTs will be         */
    OS_ENTER_CRITICAL();                                /* ... disabled HERE!                          */
    /*@ exists (saved_value : Z), data_at(&cpu_sr, OS_CPU_SR, saved_value)
        which implies exists (saved_again : Z), saved_again == saved_value && data_at(&cpu_sr, OS_CPU_SR, saved_again)
    */
    /*@ Given saved_again */
    /*@ task_delete_preparation_history(sg, requested, call, initial, current, acquired, priority, tid, node, prepared, loan) &&
        task_delete_restore_history(environment, critical, requested, TaskDeletePrepared(tid, taskGeneration(node)), sg,
          current, task_delete_locked(prepared), middle, between) &&
        task_delete_save_post(environment, critical, saved_local, requested, TaskDeletePrepared(tid, taskGeneration(node)), loan,
          sg, middle, mask, saved_again, between)
        which implies exists (resumed_call : OsSchedCallContext) (resumed : UCOS2_Verify_State),
        task_delete_window_history(sg, requested, call, initial, current, acquired, priority, tid, node, prepared, loan, resumed_call, resumed) &&
        interrupt_saved_value(mask, saved_again) &&
        task_delete_call_masked(environment, critical, saved_local, TaskDeletePrepared(tid, taskGeneration(node)), loan,
          sg, resumed_call, saved_again, resumed, resumed)
    */
    /*@ Given resumed_call resumed */
    /*@ task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
          &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
        task_delete_window_history(sg, requested, call, initial, current, acquired, priority, tid, node, prepared, loan, resumed_call, resumed) &&
        task_delete_call_masked(environment, critical, saved_local, TaskDeletePrepared(tid, taskGeneration(node)), loan,
          sg, resumed_call, saved_again, resumed, resumed)
        which implies
        0 <= task_delete_locks(resumed) && task_delete_locks(resumed) <= 255 &&
        data_at(&OSLockNesting, INT8U, task_delete_locks(resumed)) *
        wand(task_delete_uchar_cell(&OSLockNesting, task_delete_locks(task_delete_released(prepared, resumed))),
          task_delete_released_body(environment, critical, saved_local, sg, requested, call, initial, current, acquired, priority, tid, node, prepared, loan, resumed_call, saved_again, resumed))
    */
    if ((lock_added == OS_TRUE) && (OSLockNesting > 0u)) { /* Release only this call's added lock        */
        OSLockNesting--;
    }
    /*@ data_at(&OSLockNesting, INT8U, task_delete_locks(task_delete_released(prepared, resumed))) *
        wand(task_delete_uchar_cell(&OSLockNesting, task_delete_locks(task_delete_released(prepared, resumed))),
          task_delete_released_body(environment, critical, saved_local, sg, requested, call, initial, current, acquired, priority, tid, node, prepared, loan, resumed_call, saved_again, resumed))
        which implies
        task_delete_released_body(environment, critical, saved_local, sg, requested, call, initial, current, acquired, priority, tid, node, prepared, loan, resumed_call, saved_again, resumed)
    */
    OSTaskDelHook(ptcb) /*@ where F=task_delete_released_body(environment, critical, saved_local, sg, requested, call, initial, current, acquired, priority, tid, node, prepared, loan, resumed_call, saved_again, resumed) */; /* Call user defined hook */

#if OS_TASK_CREATE_EXT_EN > 0u
#if defined(OS_TLS_TBL_SIZE) && (OS_TLS_TBL_SIZE > 0u)
    OS_TLS_TaskDel(ptcb);                               /* Call TLS hook                               */
#endif
#endif

    /*@ task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
          &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
        task_delete_released_body(environment, critical, saved_local, sg, requested, call, initial, current, acquired, priority, tid, node, prepared, loan, resumed_call, saved_again, resumed)
        which implies
        data_at(&OSTaskCtr, INT8U, task_delete_count(task_delete_released(prepared, resumed))) *
        data_at(pointer_offset(OSTCBPrioTbl, priority, sizeof(struct os_tcb *), struct os_tcb *), OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&OSTCBFreeList, OS_TCB *, task_delete_free_head(sg, task_delete_released(prepared, resumed))) *
        data_at(&OSTCBList, OS_TCB *, task_delete_list_head(sg, task_delete_released(prepared, resumed))) *
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBNext), OS_TCB *, task_delete_next(sg, task_delete_prepared_node(node))) *
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBPrev), OS_TCB *, task_delete_prev(sg, task_delete_prepared_node(node))) *
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBTaskName), INT8U *, task_delete_tcb_value(sg, task_delete_prepared_node(node), TCBTaskName)) *
        task_delete_neighbor_cells(sg, tid, task_delete_prepared_node(node), false) *
        wand(task_delete_recycle_cells(sg, task_delete_released(prepared, resumed), tid, priority, task_delete_prepared_node(node), LitMap("?"), true),
          task_delete_recycled_body(environment, critical, saved_local, sg, requested, call, initial, resumed_call, saved_again, resumed,
            task_delete_cut(sg, prepared, resumed, tid, priority, node, LitMap("?")), loan, LitMap("?")))
    */
    OSTaskCtr--;                                        /* One less task being managed                 */
    OSTCBPrioTbl[prio] = (OS_TCB *)0;                   /* Clear old priority entry                    */
    if (ptcb->OSTCBPrev == (OS_TCB *)0) {               /* Remove from TCB chain                       */
        /*@ task_delete_window_history(sg, requested, call, initial, current, acquired, priority, tid, node, prepared, loan, resumed_call, resumed) &&
            task_delete_prev(sg, task_delete_prepared_node(node)) == 0 &&
            task_delete_neighbor_cells(sg, tid, task_delete_prepared_node(node), false)
            which implies
            data_at(&(((OS_TCB *)task_delete_next(sg, task_delete_prepared_node(node)))->OSTCBPrev), OS_TCB *, task_slot_addr(sg, tid))
        */
        ptcb->OSTCBNext->OSTCBPrev = (OS_TCB *)0;
        OSTCBList                  = ptcb->OSTCBNext;
        /*@ task_delete_window_history(sg, requested, call, initial, current, acquired, priority, tid, node, prepared, loan, resumed_call, resumed) &&
            task_delete_prev(sg, task_delete_prepared_node(node)) == 0 &&
            data_at(&(((OS_TCB *)task_delete_next(sg, task_delete_prepared_node(node)))->OSTCBPrev), OS_TCB *, 0)
            which implies task_delete_neighbor_cells(sg, tid, task_delete_prepared_node(node), true)
        */
    } else {
        /*@ task_delete_window_history(sg, requested, call, initial, current, acquired, priority, tid, node, prepared, loan, resumed_call, resumed) &&
            task_delete_prev(sg, task_delete_prepared_node(node)) != 0 &&
            task_delete_neighbor_cells(sg, tid, task_delete_prepared_node(node), false)
            which implies
            data_at(&(((OS_TCB *)task_delete_prev(sg, task_delete_prepared_node(node)))->OSTCBNext), OS_TCB *, task_slot_addr(sg, tid)) *
            data_at(&(((OS_TCB *)task_delete_next(sg, task_delete_prepared_node(node)))->OSTCBPrev), OS_TCB *, task_slot_addr(sg, tid))
        */
        ptcb->OSTCBPrev->OSTCBNext = ptcb->OSTCBNext;
        ptcb->OSTCBNext->OSTCBPrev = ptcb->OSTCBPrev;
        /*@ task_delete_window_history(sg, requested, call, initial, current, acquired, priority, tid, node, prepared, loan, resumed_call, resumed) &&
            task_delete_prev(sg, task_delete_prepared_node(node)) != 0 &&
            data_at(&(((OS_TCB *)task_delete_prev(sg, task_delete_prepared_node(node)))->OSTCBNext), OS_TCB *, task_delete_next(sg, task_delete_prepared_node(node))) *
            data_at(&(((OS_TCB *)task_delete_next(sg, task_delete_prepared_node(node)))->OSTCBPrev), OS_TCB *, task_delete_prev(sg, task_delete_prepared_node(node)))
            which implies task_delete_neighbor_cells(sg, tid, task_delete_prepared_node(node), true)
        */
    }
    ptcb->OSTCBNext     = OSTCBFreeList;                /* Return TCB to free TCB list                 */
    OSTCBFreeList       = ptcb;
#if OS_TASK_NAME_EN > 0u
    ptcb->OSTCBTaskName = (INT8U *)(void *)"?";
#endif
    /*@ task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
          &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
        data_at(&OSTaskCtr, INT8U, (task_delete_count(task_delete_released(prepared, resumed)) - 1) % 256) *
        data_at(pointer_offset(OSTCBPrioTbl, priority, sizeof(struct os_tcb *), struct os_tcb *), OS_TCB *, 0) *
        data_at(&OSTCBFreeList, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&OSTCBList, OS_TCB *, task_delete_list_head(sg, task_delete_cut(sg, prepared, resumed, tid, priority, node, LitMap("?")))) *
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBNext), OS_TCB *, task_delete_free_head(sg, task_delete_released(prepared, resumed))) *
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBPrev), OS_TCB *, task_delete_prev(sg, task_delete_prepared_node(node))) *
        data_at(&(((OS_TCB *)task_slot_addr(sg, tid))->OSTCBTaskName), INT8U *, LitMap("?")) *
        task_delete_neighbor_cells(sg, tid, task_delete_prepared_node(node), true) *
        wand(task_delete_recycle_cells(sg, task_delete_released(prepared, resumed), tid, priority, task_delete_prepared_node(node), LitMap("?"), true),
          task_delete_recycled_body(environment, critical, saved_local, sg, requested, call, initial, resumed_call, saved_again, resumed,
            task_delete_cut(sg, prepared, resumed, tid, priority, node, LitMap("?")), loan, LitMap("?")))
        which implies
        task_delete_recycled_body(environment, critical, saved_local, sg, requested, call, initial, resumed_call, saved_again, resumed,
          task_delete_cut(sg, prepared, resumed, tid, priority, node, LitMap("?")), loan, LitMap("?"))
    */
    /*@ task_delete_recycled_body(environment, critical, saved_local, sg, requested, call, initial, resumed_call, saved_again, resumed,
          task_delete_cut(sg, prepared, resumed, tid, priority, node, LitMap("?")), loan, LitMap("?"))
        which implies
        task_delete_result_history(sg, requested, LitMap("?"), call, initial, resumed_call,
          task_delete_cut(sg, prepared, resumed, tid, priority, node, LitMap("?"))) &&
        task_delete_call_masked(environment, critical, saved_local, TaskDeleteStable, loan, sg, resumed_call, saved_again, resumed,
          task_delete_cut(sg, prepared, resumed, tid, priority, node, LitMap("?")))
    */
    OS_EXIT_CRITICAL();
    /*@ interrupt_saved_value(mask, saved_again) &&
        task_delete_result_history(sg, requested, LitMap("?"), call, initial, resumed_call,
          task_delete_cut(sg, prepared, resumed, tid, priority, node, LitMap("?"))) &&
        task_delete_restore_post(environment, critical, saved_local, requested, TaskDeleteStable, loan,
          sg, resumed_call, armv7a_irq_fiq_mask(saved_again), task_delete_cut(sg, prepared, resumed, tid, priority, node, LitMap("?")))
        which implies exists (final_call : OsSchedCallContext) (final_state : UCOS2_Verify_State),
        task_delete_final_body(environment, critical, saved_local, sg, requested, LitMap("?"), call, mask, initial, final_call, final_state,
          task_delete_cut(sg, prepared, resumed, tid, priority, node, LitMap("?")), loan)
    */
    /*@ Given final_call final_state */
    /*@ task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
          &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
        task_delete_final_body(environment, critical, saved_local, sg, requested, LitMap("?"), call, mask, initial, final_call, final_state,
          task_delete_cut(sg, prepared, resumed, tid, priority, node, LitMap("?")), loan)
        which implies
        data_at(&OSRunning, BOOLEAN, task_delete_running(final_state)) *
        wand(task_delete_uchar_cell(&OSRunning, task_delete_running(final_state)),
          task_delete_final_body(environment, critical, saved_local, sg, requested, LitMap("?"), call, mask, initial, final_call, final_state,
            task_delete_cut(sg, prepared, resumed, tid, priority, node, LitMap("?")), loan))
    */
    if (OSRunning == OS_TRUE) {
        /*@ task_delete_running(final_state) == 1 &&
            task_delete_safe(environment, critical, sg, requested, LitMap("?"), call, mask, initial, X) &&
            data_at(&OSRunning, BOOLEAN, task_delete_running(final_state)) *
            wand(task_delete_uchar_cell(&OSRunning, task_delete_running(final_state)),
              task_delete_final_body(environment, critical, saved_local, sg, requested, LitMap("?"), call, mask, initial, final_call, final_state,
                task_delete_cut(sg, prepared, resumed, tid, priority, node, LitMap("?")), loan))
            which implies
            os_sched_continuation_call_pre(environment, saved_local, kernel_program_inv, sg, final_call, mask, final_state) *
            task_delete_return_loan(sg, loan) *
            wand(task_delete_sched_history_return_with_loan(environment, critical, saved_local, sg, final_call, mask, final_state, loan),
              task_delete_api_post(environment, critical, saved_local, sg, requested, LitMap("?"), call, mask, initial, 0, X))
        */
        OS_Sched() /*@ where environment=environment, critical=critical, saved_local=saved_local, sg=sg,
          context=final_call, mask=mask, before=final_state */; /* Find new highest priority task              */
        /*@ os_sched_continuation_history_return_post(environment, critical, saved_local, kernel_program_inv, sg, final_call, mask, final_state) *
            task_delete_return_loan(sg, loan)
            which implies task_delete_sched_history_return_with_loan(environment, critical, saved_local, sg, final_call, mask, final_state, loan)
        */
        /*@ task_delete_sched_history_return_with_loan(environment, critical, saved_local, sg, final_call, mask, final_state, loan) *
            wand(task_delete_sched_history_return_with_loan(environment, critical, saved_local, sg, final_call, mask, final_state, loan),
              task_delete_api_post(environment, critical, saved_local, sg, requested, LitMap("?"), call, mask, initial, 0, X))
            which implies task_delete_api_post(environment, critical, saved_local, sg, requested, LitMap("?"), call, mask, initial, 0, X)
        */
    }
    return (OS_ERR_NONE);
}
