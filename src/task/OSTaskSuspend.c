/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSTaskSuspend (INT8U prio)
/*@ With (X : Z -> UCOS2_Verify_State -> Prop)
         (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
         saved_local (sg : StableGlobVars) (caller : TaskSuspendCaller)
         (mask request : Z) (before : UCOS2_Verify_State) (frame : Assertion)
    Require prio == request &&
            task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            task_suspend_safe(environment, critical, sg, caller, mask, request, before, X) &&
            task_suspend_call_pre(environment, critical, saved_local, sg, caller, mask, before, request, frame)
    Ensure task_suspend_refined_call_post(environment, critical, saved_local, sg, caller, mask, before,
             request, frame, __return, X)
*/
{
    BOOLEAN    self;
    OS_TCB    *ptcb;
    INT8U      y;
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif



#if OS_ARG_CHK_EN > 0u
    if (prio == OS_TASK_IDLE_PRIO) {                            /* Not allowed to suspend idle task    */
        return (OS_ERR_TASK_SUSPEND_IDLE);
    }
    if (prio >= OS_LOWEST_PRIO) {                               /* Task priority valid ?               */
        if (prio != OS_PRIO_SELF) {
            return (OS_ERR_PRIO_INVALID);
        }
    }
#endif
    /*@ Assert prio == request && task_suspend_entry_facts(sg, request) &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        task_suspend_safe(environment, critical, sg, caller, mask, request, before, X) &&
        task_suspend_call_pre(environment, critical, saved_local, sg, caller, mask, before, request, frame) *
        data_at(&cpu_sr, OS_CPU_SR, 0) *
        undef_data_at(&self, BOOLEAN) * undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&y, INT8U)
    */
    /*@ prio == request && task_suspend_entry_facts(sg, request) &&
        task_suspend_call_pre(environment, critical, saved_local, sg, caller, mask, before, request, frame)
        which implies
        prio == request && task_suspend_entry_facts(sg, request) &&
        task_suspend_completed_calls(critical, sg, caller, request, mask, before) &&
        task_suspend_scheduler_clients(critical, caller) &&
        task_suspend_closed(environment, critical, saved_local, sg, caller, mask, before) * frame
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (acquired_call : TaskSuspendCaller) (acquired : UCOS2_Verify_State)
                      pointer priority (residual : Assertion),
        prio == request &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        task_suspend_acquired_facts(critical, sg, caller, request, mask, before, cpu_sr,
          acquired_call, acquired, pointer, priority, residual) &&
        task_suspend_safe(environment, critical, sg, caller, mask, request, before, X) &&
        task_suspend_save_effect(environment, critical, sg, caller, acquired_call, mask, cpu_sr, before, acquired) &&
        task_suspend_tokens(environment, critical, saved_local, sg, acquired_call, cpu_sr, acquired, acquired) *
        data_at(&OSTCBCur, OS_TCB *, pointer) *
        data_at(&((OS_TCB *)pointer)->OSTCBPrio, unsigned char, priority) * residual * frame *
        undef_data_at(&self, BOOLEAN) * undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&y, INT8U)
    */
    /*@ Given acquired_call acquired pointer priority residual */
    if (prio == OS_PRIO_SELF) {                                 /* See if suspend SELF                 */
        prio = OSTCBCur->OSTCBPrio;
        self = OS_TRUE;
    } else if (prio == OSTCBCur->OSTCBPrio) {                   /* See if suspending self              */
        self = OS_TRUE;
    } else {
        self = OS_FALSE;                                        /* No suspending another task          */
    }
    /*@ task_suspend_acquired_facts(critical, sg, caller, request, mask, before, cpu_sr,
          acquired_call, acquired, pointer, priority, residual) &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        data_at(&OSTCBCur, OS_TCB *, pointer) *
        data_at(&((OS_TCB *)pointer)->OSTCBPrio, unsigned char, priority) * residual
        which implies
        task_suspend_acquired_facts(critical, sg, caller, request, mask, before, cpu_sr,
          acquired_call, acquired, pointer, priority, residual) &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && UCOS2_inv(sg, acquired)
    */
    /*@ Assert prio == task_suspend_resolved_priority(sg, request, priority) && 0 <= prio && prio <= 63 &&
        task_suspend_acquired_facts(critical, sg, caller, request, mask, before, cpu_sr,
          acquired_call, acquired, pointer, priority, residual) &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        task_suspend_safe(environment, critical, sg, caller, mask, request, before, X) &&
        task_suspend_save_effect(environment, critical, sg, caller, acquired_call, mask, cpu_sr, before, acquired) &&
        task_suspend_tokens(environment, critical, saved_local, sg, acquired_call, cpu_sr, acquired, acquired) *
        UCOS2_inv(sg, acquired) * frame * undef_data_at(&self, BOOLEAN) *
        undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&y, INT8U)
    */
    /* SELF must obey the same Idle protection as an explicit priority. */
    if (prio == OS_TASK_IDLE_PRIO) {
        /*@ prio == 63 && prio == task_suspend_resolved_priority(sg, request, priority) &&
            task_suspend_acquired_facts(critical, sg, caller, request, mask, before, cpu_sr,
              acquired_call, acquired, pointer, priority, residual) &&
            task_suspend_tokens(environment, critical, saved_local, sg, acquired_call, cpu_sr, acquired, acquired) *
            UCOS2_inv(sg, acquired)
            which implies
            task_suspend_acquired_facts(critical, sg, caller, request, mask, before, cpu_sr,
              acquired_call, acquired, pointer, priority, residual) &&
            prio == 63 && task_suspend_step(sg, request, priority, acquired, 71, 0, acquired) &&
            task_suspend_masked(environment, critical, saved_local, sg, acquired_call, cpu_sr, acquired, acquired)
        */
        OS_EXIT_CRITICAL();
        return (OS_ERR_TASK_SUSPEND_IDLE);
    }
    /*@ task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && 0 <= prio && prio < 64 &&
        UCOS2_inv(sg, acquired)
        which implies
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        UCOS2_state_inv(sg, acquired) &&
        data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), OS_TCB *, task_suspend_table_value(sg, acquired, prio)) *
        task_suspend_table_frame(sg, acquired, prio)
    */
    ptcb = OSTCBPrioTbl[prio];
    /*@ task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && UCOS2_state_inv(sg, acquired) &&
        ptcb == task_suspend_table_value(sg, acquired, prio) &&
        data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), OS_TCB *, task_suspend_table_value(sg, acquired, prio)) *
        task_suspend_table_frame(sg, acquired, prio)
        which implies
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        ptcb == task_suspend_table_value(sg, acquired, prio) && UCOS2_inv(sg, acquired)
    */
    if (ptcb == (OS_TCB *)0) {                                  /* Task to suspend must exist          */
        /*@ ptcb == 0 && ptcb == task_suspend_table_value(sg, acquired, prio) && prio != 63 &&
            prio == task_suspend_resolved_priority(sg, request, priority) &&
            task_suspend_acquired_facts(critical, sg, caller, request, mask, before, cpu_sr,
              acquired_call, acquired, pointer, priority, residual) &&
            task_suspend_tokens(environment, critical, saved_local, sg, acquired_call, cpu_sr, acquired, acquired) *
            UCOS2_inv(sg, acquired)
            which implies
            task_suspend_acquired_facts(critical, sg, caller, request, mask, before, cpu_sr,
              acquired_call, acquired, pointer, priority, residual) &&
            ptcb == 0 && prio == task_suspend_resolved_priority(sg, request, priority) &&
            task_suspend_step(sg, request, priority, acquired, 72, 0, acquired) &&
            task_suspend_masked(environment, critical, saved_local, sg, acquired_call, cpu_sr, acquired, acquired)
        */
        OS_EXIT_CRITICAL();
        return (OS_ERR_TASK_SUSPEND_PRIO);
    }
    if (ptcb == ((OS_TCB *)1)) {                                /* Exact OS_TCB_RESERVED expansion     */
        /*@ ptcb == 1 && ptcb == task_suspend_table_value(sg, acquired, prio) && prio != 63 &&
            prio == task_suspend_resolved_priority(sg, request, priority) &&
            task_suspend_acquired_facts(critical, sg, caller, request, mask, before, cpu_sr,
              acquired_call, acquired, pointer, priority, residual) &&
            task_suspend_tokens(environment, critical, saved_local, sg, acquired_call, cpu_sr, acquired, acquired) *
            UCOS2_inv(sg, acquired)
            which implies
            task_suspend_acquired_facts(critical, sg, caller, request, mask, before, cpu_sr,
              acquired_call, acquired, pointer, priority, residual) &&
            ptcb == 1 && prio == task_suspend_resolved_priority(sg, request, priority) &&
            task_suspend_step(sg, request, priority, acquired, 67, 0, acquired) &&
            task_suspend_masked(environment, critical, saved_local, sg, acquired_call, cpu_sr, acquired, acquired)
        */
        OS_EXIT_CRITICAL();
        return (OS_ERR_TASK_NOT_EXIST);
    }
    /*@ task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        ptcb == task_suspend_table_value(sg, acquired, prio) && ptcb != 0 && ptcb != 1 &&
        0 <= prio && prio < 63 && UCOS2_inv(sg, acquired)
        which implies exists tid (target : TaskAbstractState),
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        ptcb == task_slot_addr(sg, tid) && task_suspend_target_facts(sg, acquired, prio, tid, target) &&
        data_at(&OSTCBCur, OS_TCB *, task_suspend_current_pointer(sg, acquired)) *
        data_at(&OSRdyGrp, unsigned char, os_sched_group(acquired)) *
        UCharArray::full(OSRdyTbl, 8, os_sched_rows(acquired)) *
        task_public_storage(sg, TskState(acquired)) * task_suspend_work_frame(sg, acquired)
    */
    /*@ Given tid target */
    /* Inherited and permanent priority slots may name the same TCB. */
    self = (ptcb == OSTCBCur) ? OS_TRUE : OS_FALSE;
    /*@ task_suspend_target_facts(sg, acquired, prio, tid, target) && ptcb == task_slot_addr(sg, tid) &&
        task_public_storage(sg, TskState(acquired))
        which implies
        task_suspend_target_facts(sg, acquired, prio, tid, target) && ptcb == task_slot_addr(sg, tid) &&
        0 <= tcb_y_of_prio(curPrio(target)) && tcb_y_of_prio(curPrio(target)) < 8 &&
        data_at(&ptcb->OSTCBY, unsigned char, tcb_y_of_prio(curPrio(target))) *
        task_public_storage_without_field(sg, TskState(acquired), tid, target, TCBCommonField(TCBY))
    */
    y            = ptcb->OSTCBY;
    /*@ task_suspend_target_facts(sg, acquired, prio, tid, target) && ptcb == task_slot_addr(sg, tid) &&
        data_at(&ptcb->OSTCBY, unsigned char, tcb_y_of_prio(curPrio(target))) *
        task_public_storage_without_field(sg, TskState(acquired), tid, target, TCBCommonField(TCBY))
        which implies
        task_suspend_target_facts(sg, acquired, prio, tid, target) && ptcb == task_slot_addr(sg, tid) &&
        task_public_storage(sg, TskState(acquired))
    */
    /*@ task_suspend_target_facts(sg, acquired, prio, tid, target) && ptcb == task_slot_addr(sg, tid) &&
        y == tcb_y_of_prio(curPrio(target)) && 0 <= y && y < 8 &&
        task_public_storage(sg, TskState(acquired)) * UCharArray::full(OSRdyTbl, 8, os_sched_rows(acquired))
        which implies
        task_suspend_target_facts(sg, acquired, prio, tid, target) && ptcb == task_slot_addr(sg, tid) &&
        y == tcb_y_of_prio(curPrio(target)) && 0 <= y && y < 8 &&
        0 <= tcb_bit_x_of_prio(curPrio(target)) && tcb_bit_x_of_prio(curPrio(target)) <= 255 &&
        data_at(&ptcb->OSTCBBitX, unsigned char, tcb_bit_x_of_prio(curPrio(target))) *
        task_public_storage_without_field(sg, TskState(acquired), tid, target, TCBCommonField(TCBBitX)) *
        data_at(pointer_offset(OSRdyTbl, y, OS_PRIO), OS_PRIO, Znth(y, os_sched_rows(acquired), 0)) *
        UCharArray::missing_i(OSRdyTbl, y, 0, 8, os_sched_rows(acquired))
    */
    OSRdyTbl[y] &= (OS_PRIO)~ptcb->OSTCBBitX;                   /* Make task not ready                 */
    /*@ task_suspend_target_facts(sg, acquired, prio, tid, target) && ptcb == task_slot_addr(sg, tid) &&
        data_at(&ptcb->OSTCBBitX, unsigned char, tcb_bit_x_of_prio(curPrio(target))) *
        task_public_storage_without_field(sg, TskState(acquired), tid, target, TCBCommonField(TCBBitX))
        which implies
        task_suspend_target_facts(sg, acquired, prio, tid, target) && ptcb == task_slot_addr(sg, tid) &&
        task_public_storage(sg, TskState(acquired))
    */
    if (OSRdyTbl[y] == 0u) {
        /*@ task_suspend_target_facts(sg, acquired, prio, tid, target) && ptcb == task_slot_addr(sg, tid) &&
            task_public_storage(sg, TskState(acquired))
            which implies
            task_suspend_target_facts(sg, acquired, prio, tid, target) && ptcb == task_slot_addr(sg, tid) &&
            0 <= tcb_bit_y_of_prio(curPrio(target)) && tcb_bit_y_of_prio(curPrio(target)) <= 255 &&
            data_at(&ptcb->OSTCBBitY, unsigned char, tcb_bit_y_of_prio(curPrio(target))) *
            task_public_storage_without_field(sg, TskState(acquired), tid, target, TCBCommonField(TCBBitY))
        */
        OSRdyGrp &= (OS_PRIO)~ptcb->OSTCBBitY;
        /*@ task_suspend_target_facts(sg, acquired, prio, tid, target) && ptcb == task_slot_addr(sg, tid) &&
            data_at(&ptcb->OSTCBBitY, unsigned char, tcb_bit_y_of_prio(curPrio(target))) *
            task_public_storage_without_field(sg, TskState(acquired), tid, target, TCBCommonField(TCBBitY))
            which implies
            task_suspend_target_facts(sg, acquired, prio, tid, target) && ptcb == task_slot_addr(sg, tid) &&
            task_public_storage(sg, TskState(acquired))
        */
    }
    /*@ Assert prio == task_suspend_resolved_priority(sg, request, priority) && prio != 63 &&
        ptcb == task_slot_addr(sg, tid) && y == tcb_y_of_prio(curPrio(target)) &&
        self == task_suspend_self_byte(sg, acquired, tid) &&
        task_suspend_target_facts(sg, acquired, prio, tid, target) &&
        task_suspend_acquired_facts(critical, sg, caller, request, mask, before, cpu_sr,
          acquired_call, acquired, pointer, priority, residual) &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        task_suspend_safe(environment, critical, sg, caller, mask, request, before, X) &&
        task_suspend_save_effect(environment, critical, sg, caller, acquired_call, mask, cpu_sr, before, acquired) &&
        task_suspend_tokens(environment, critical, saved_local, sg, acquired_call, cpu_sr, acquired, acquired) *
        data_at(&OSTCBCur, OS_TCB *, task_suspend_current_pointer(sg, acquired)) *
        data_at(&OSRdyGrp, unsigned char, task_suspend_updated_group(acquired, target)) *
        data_at(pointer_offset(OSRdyTbl, y, OS_PRIO), OS_PRIO, task_suspend_cleared_row(acquired, target)) *
        UCharArray::missing_i(OSRdyTbl, y, 0, 8, os_sched_rows(acquired)) *
        task_public_storage(sg, TskState(acquired)) * task_suspend_work_frame(sg, acquired) * frame
    */
    /*@ task_suspend_target_facts(sg, acquired, prio, tid, target) && ptcb == task_slot_addr(sg, tid) &&
        task_public_storage(sg, TskState(acquired))
        which implies
        task_suspend_target_facts(sg, acquired, prio, tid, target) && ptcb == task_slot_addr(sg, tid) &&
        0 <= encode_task_status(stat(target)) && encode_task_status(stat(target)) <= 255 &&
        data_at(&ptcb->OSTCBStat, unsigned char, encode_task_status(stat(target))) *
        task_public_storage_without_field(sg, TskState(acquired), tid, target, TCBCommonField(TCBStat))
    */
    ptcb->OSTCBStat |= OS_STAT_SUSPEND;                         /* Status of task is 'SUSPENDED'       */
    /*@ Assert prio == task_suspend_resolved_priority(sg, request, priority) &&
        self == task_suspend_self_byte(sg, acquired, tid) &&
        task_suspend_acquired_facts(critical, sg, caller, request, mask, before, cpu_sr,
          acquired_call, acquired, pointer, priority, residual) &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        task_suspend_step(sg, request, priority, acquired, 0, self, task_suspend_state(acquired, tid, target)) &&
        (self == 1 => task_suspend_caller_source(sg, acquired_call, task_suspend_state(acquired, tid, target))) &&
        task_suspend_safe(environment, critical, sg, caller, mask, request, before, X) &&
        task_suspend_save_effect(environment, critical, sg, caller, acquired_call, mask, cpu_sr, before, acquired) &&
        task_suspend_masked(environment, critical, saved_local, sg, acquired_call, cpu_sr, acquired,
          task_suspend_state(acquired, tid, target)) * frame *
        undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&y, INT8U)
    */
    OS_EXIT_CRITICAL();
    /*@ Assert exists (checkpoint_call : TaskSuspendCaller) (checkpoint : UCOS2_Verify_State),
        prio == task_suspend_resolved_priority(sg, request, priority) &&
        self == task_suspend_self_byte(sg, acquired, tid) &&
        task_suspend_acquired_facts(critical, sg, caller, request, mask, before, cpu_sr,
          acquired_call, acquired, pointer, priority, residual) &&
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        task_suspend_step(sg, request, priority, acquired, 0, self, task_suspend_state(acquired, tid, target)) &&
        task_suspend_restore_observation(critical, sg, acquired_call, checkpoint_call,
          task_suspend_state(acquired, tid, target), checkpoint) &&
        task_suspend_scheduler_clients(critical, checkpoint_call) &&
        (self == 1 => task_suspend_caller_source(sg, checkpoint_call, checkpoint)) &&
        (self == 1 => task_suspend_scheduler_safe(environment, critical, sg, checkpoint_call, mask, checkpoint, 0, X)) &&
        (self != 1 => task_suspend_return_safe(checkpoint, 0, X)) &&
        task_suspend_closed(environment, critical, saved_local, sg, checkpoint_call, mask, checkpoint) * frame *
        undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&y, INT8U)
    */
    /*@ Given checkpoint_call checkpoint */
    OS_TRACE_TASK_SUSPEND(ptcb);
    OS_TRACE_TASK_SUSPENDED(ptcb);
    if (self == OS_TRUE) {                                      /* Context switch only if SELF         */
        /*@ task_suspend_scheduler_clients(critical, checkpoint_call) &&
            task_suspend_caller_source(sg, checkpoint_call, checkpoint) &&
            task_suspend_closed(environment, critical, saved_local, sg, checkpoint_call, mask, checkpoint)
            which implies
            task_suspend_scheduler_pre(environment, critical, saved_local, sg, checkpoint_call, mask, checkpoint)
        */
        OS_Sched() /*@ where X = X */;                           /* Find new highest priority task      */
    }
    return (OS_ERR_NONE);
}
