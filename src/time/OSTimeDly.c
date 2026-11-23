/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSTimeDly (INT32U ticks)
/*@ With (X : unit -> UCOS2_Verify_State -> Prop)
         (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
         saved_local (sg : StableGlobVars) (caller : TaskSuspendCaller)
         (mask request : Z) (before : UCOS2_Verify_State) (frame : Assertion)
    Require ticks == request &&
            task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            time_dly_safe(environment, critical, sg, caller, mask, request, before, X) &&
            time_dly_call_pre(environment, critical, saved_local, sg, caller, mask, request, before, frame)
    Ensure time_dly_call_post(environment, critical, saved_local, sg, caller, mask, request, before, frame, X)
*/
{
    INT8U      y;
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif



    /*@ task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        time_dly_call_pre(environment, critical, saved_local, sg, caller, mask, request, before, frame)
        which implies
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        time_dly_entry_facts(environment, critical, sg, caller, mask, request, before) &&
        0 <= os_sched_ints(before) && os_sched_ints(before) <= 255 &&
        0 <= os_sched_locks(before) && os_sched_locks(before) <= 255 &&
        data_at(&OSIntNesting, unsigned char, os_sched_ints(before)) *
        data_at(&OSLockNesting, unsigned char, os_sched_locks(before)) *
        time_dly_prefix_frame(environment, saved_local, sg, caller, mask, before) * frame
    */
    if (OSIntNesting > 0u) {                     /* See if trying to call from an ISR                  */
        return;
    }
    if (OSLockNesting > 0u) {                    /* See if called with scheduler locked                */
        return;
    }
    /*@ task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        data_at(&OSIntNesting, unsigned char, os_sched_ints(before)) *
        data_at(&OSLockNesting, unsigned char, os_sched_locks(before)) *
        time_dly_prefix_frame(environment, saved_local, sg, caller, mask, before)
        which implies
        task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        task_suspend_closed(environment, critical, saved_local, sg, caller, mask, before)
    */
    if (ticks > 0u) {                            /* 0 means no delay!                                  */
        OS_ENTER_CRITICAL();
        /*@ Assert exists (active : TaskSuspendCaller) (acquired : UCOS2_Verify_State)
                          tid (target : TaskAbstractState) pointer,
            ticks == request && pointer == task_slot_addr(sg, tid) &&
            task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            time_dly_safe(environment, critical, sg, caller, mask, request, before, X) &&
            time_dly_acquired_facts(environment, critical, sg, caller, mask, request, before,
              cpu_sr, active, acquired, tid, target) &&
            time_dly_target_facts(sg, acquired, tid, target) &&
            task_suspend_tokens(environment, critical, saved_local, sg, active, cpu_sr, acquired, acquired) *
            data_at(&OSTCBCur, OS_TCB *, pointer) *
            data_at(&OSRdyGrp, unsigned char, os_sched_group(acquired)) *
            UCharArray::full(OSRdyTbl, 8, os_sched_rows(acquired)) *
            task_public_storage(sg, TskState(acquired)) * task_suspend_work_frame(sg, acquired) * frame *
            undef_data_at(&y, INT8U)
        */
        /*@ Given active acquired tid target pointer */
        /*@ time_dly_target_facts(sg, acquired, tid, target) && pointer == task_slot_addr(sg, tid) &&
            task_public_storage(sg, TskState(acquired))
            which implies
            time_dly_target_facts(sg, acquired, tid, target) && pointer == task_slot_addr(sg, tid) &&
            0 <= tcb_y_of_prio(curPrio(target)) && tcb_y_of_prio(curPrio(target)) < 8 &&
            data_at(&((OS_TCB *)pointer)->OSTCBY, unsigned char, tcb_y_of_prio(curPrio(target))) *
            task_public_storage_without_field(sg, TskState(acquired), tid, target, TCBCommonField(TCBY))
        */
        y            =  OSTCBCur->OSTCBY;        /* Delay current task                                 */
        /*@ time_dly_target_facts(sg, acquired, tid, target) && pointer == task_slot_addr(sg, tid) &&
            data_at(&((OS_TCB *)pointer)->OSTCBY, unsigned char, tcb_y_of_prio(curPrio(target))) *
            task_public_storage_without_field(sg, TskState(acquired), tid, target, TCBCommonField(TCBY))
            which implies
            time_dly_target_facts(sg, acquired, tid, target) && pointer == task_slot_addr(sg, tid) &&
            task_public_storage(sg, TskState(acquired))
        */
        /*@ time_dly_target_facts(sg, acquired, tid, target) && pointer == task_slot_addr(sg, tid) &&
            y == tcb_y_of_prio(curPrio(target)) && 0 <= y && y < 8 &&
            task_public_storage(sg, TskState(acquired)) * UCharArray::full(OSRdyTbl, 8, os_sched_rows(acquired))
            which implies
            time_dly_target_facts(sg, acquired, tid, target) && pointer == task_slot_addr(sg, tid) &&
            y == tcb_y_of_prio(curPrio(target)) && 0 <= y && y < 8 &&
            0 <= tcb_bit_x_of_prio(curPrio(target)) && tcb_bit_x_of_prio(curPrio(target)) <= 255 &&
            data_at(&((OS_TCB *)pointer)->OSTCBBitX, unsigned char, tcb_bit_x_of_prio(curPrio(target))) *
            task_public_storage_without_field(sg, TskState(acquired), tid, target, TCBCommonField(TCBBitX)) *
            data_at(pointer_offset(OSRdyTbl, y, OS_PRIO), OS_PRIO, Znth(y, os_sched_rows(acquired), 0)) *
            UCharArray::missing_i(OSRdyTbl, y, 0, 8, os_sched_rows(acquired))
        */
        OSRdyTbl[y] &= (OS_PRIO)~OSTCBCur->OSTCBBitX;
        /*@ time_dly_target_facts(sg, acquired, tid, target) && pointer == task_slot_addr(sg, tid) &&
            data_at(&((OS_TCB *)pointer)->OSTCBBitX, unsigned char, tcb_bit_x_of_prio(curPrio(target))) *
            task_public_storage_without_field(sg, TskState(acquired), tid, target, TCBCommonField(TCBBitX))
            which implies
            time_dly_target_facts(sg, acquired, tid, target) && pointer == task_slot_addr(sg, tid) &&
            task_public_storage(sg, TskState(acquired))
        */
        OS_TRACE_TASK_SUSPENDED(OSTCBCur);
        if (OSRdyTbl[y] == 0u) {
            /*@ time_dly_target_facts(sg, acquired, tid, target) && pointer == task_slot_addr(sg, tid) &&
                task_public_storage(sg, TskState(acquired))
                which implies
                time_dly_target_facts(sg, acquired, tid, target) && pointer == task_slot_addr(sg, tid) &&
                0 <= tcb_bit_y_of_prio(curPrio(target)) && tcb_bit_y_of_prio(curPrio(target)) <= 255 &&
                data_at(&((OS_TCB *)pointer)->OSTCBBitY, unsigned char, tcb_bit_y_of_prio(curPrio(target))) *
                task_public_storage_without_field(sg, TskState(acquired), tid, target, TCBCommonField(TCBBitY))
            */
            OSRdyGrp &= (OS_PRIO)~OSTCBCur->OSTCBBitY;
            /*@ time_dly_target_facts(sg, acquired, tid, target) && pointer == task_slot_addr(sg, tid) &&
                data_at(&((OS_TCB *)pointer)->OSTCBBitY, unsigned char, tcb_bit_y_of_prio(curPrio(target))) *
                task_public_storage_without_field(sg, TskState(acquired), tid, target, TCBCommonField(TCBBitY))
                which implies
                time_dly_target_facts(sg, acquired, tid, target) && pointer == task_slot_addr(sg, tid) &&
                task_public_storage(sg, TskState(acquired))
            */
        }
        /*@ Assert ticks == request && pointer == task_slot_addr(sg, tid) &&
            y == tcb_y_of_prio(curPrio(target)) &&
            task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            time_dly_safe(environment, critical, sg, caller, mask, request, before, X) &&
            time_dly_acquired_facts(environment, critical, sg, caller, mask, request, before,
              cpu_sr, active, acquired, tid, target) &&
            time_dly_target_facts(sg, acquired, tid, target) &&
            task_suspend_tokens(environment, critical, saved_local, sg, active, cpu_sr, acquired, acquired) *
            data_at(&OSTCBCur, OS_TCB *, pointer) *
            data_at(&OSRdyGrp, unsigned char, time_dly_updated_group(acquired, target)) *
            data_at(pointer_offset(OSRdyTbl, y, OS_PRIO), OS_PRIO, time_dly_cleared_row(acquired, target)) *
            UCharArray::missing_i(OSRdyTbl, y, 0, 8, os_sched_rows(acquired)) *
            task_public_storage(sg, TskState(acquired)) * task_suspend_work_frame(sg, acquired) * frame
        */
        /*@ time_dly_target_facts(sg, acquired, tid, target) && pointer == task_slot_addr(sg, tid) &&
            task_public_storage(sg, TskState(acquired))
            which implies
            time_dly_target_facts(sg, acquired, tid, target) && pointer == task_slot_addr(sg, tid) &&
            data_at(&((OS_TCB *)pointer)->OSTCBDly, unsigned int, dly(target)) *
            task_public_storage_without_field(sg, TskState(acquired), tid, target, TCBCommonField(TCBDly))
        */
        OSTCBCur->OSTCBDly = ticks;              /* Load ticks in TCB                                  */
        /*@ Assert ticks == request &&
            task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            time_dly_safe(environment, critical, sg, caller, mask, request, before, X) &&
            time_dly_acquired_facts(environment, critical, sg, caller, mask, request, before,
              cpu_sr, active, acquired, tid, target) &&
            task_suspend_masked(environment, critical, saved_local, sg, active, cpu_sr, acquired,
              time_dly_state(acquired, tid, target, request)) * frame * undef_data_at(&y, INT8U)
        */
        OS_TRACE_TASK_DLY(ticks);
        OS_EXIT_CRITICAL();
        /*@ Assert exists (checkpoint_call : TaskSuspendCaller) (checkpoint : UCOS2_Verify_State),
            ticks == request &&
            task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            time_dly_acquired_facts(environment, critical, sg, caller, mask, request, before,
              cpu_sr, active, acquired, tid, target) &&
            time_dly_prefix_step(environment, critical, sg, caller, mask, request, before, checkpoint_call, checkpoint) &&
            time_dly_scheduler_source(sg, checkpoint_call, checkpoint) && kernel_sched_ready_clients(critical) &&
            time_dly_scheduler_safe(environment, critical, sg, checkpoint_call, mask, checkpoint, X) &&
            task_suspend_closed(environment, critical, saved_local, sg, checkpoint_call, mask, checkpoint) * frame *
            undef_data_at(&y, INT8U)
        */
        /*@ Given checkpoint_call checkpoint */
        /*@ kernel_sched_ready_clients(critical) && time_dly_scheduler_source(sg, checkpoint_call, checkpoint) &&
            task_suspend_closed(environment, critical, saved_local, sg, checkpoint_call, mask, checkpoint)
            which implies
            task_suspend_scheduler_pre(environment, critical, saved_local, sg, checkpoint_call, mask, checkpoint)
        */
        OS_Sched() /*@ where X = X */;            /* Find next task to run!                             */
    }
}
