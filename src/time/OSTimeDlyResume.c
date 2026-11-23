/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSTimeDlyResume (INT8U prio)
/*@ With (environment : TaskStackCallEnvironment) saved_local
         (critical : CriticalRegionResources) (sg : StableGlobVars)
         (priority : Z) (caller : TaskResumeCaller) (mask : Z) (initial : UCOS2_Verify_State)
         (X : Z -> UCOS2_Verify_State -> Prop)
    Require prio == priority && 0 <= priority && priority <= 255 &&
            selected_kernel_profile(sg) && g_OSTCBTbl(sg) == OSTCBTbl &&
            os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            (63 <= priority || (task_resume_tcb_pool_aligned(sg) && UCOS2_state_inv(sg, initial) &&
              task_resume_clients(environment, critical, caller) &&
              task_resume_caller_source(sg, caller, initial) &&
              time_dly_resume_entry_protocol(critical, sg, caller, initial))) &&
            time_dly_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
            task_resume_closed(environment, critical, saved_local, sg, caller, mask, initial)
    Ensure time_dly_resume_post(environment, critical, saved_local, sg, caller, mask, initial, priority, __return, X)
*/
{
    OS_TCB    *ptcb;
#if OS_CRITICAL_METHOD == 3u                                   /* Storage for CPU status register      */
    OS_CPU_SR  cpu_sr = 0u;
#endif



    if (prio >= OS_LOWEST_PRIO) {
        return (OS_ERR_PRIO_INVALID);
    }
    OS_ENTER_CRITICAL();
    /*@ Assert exists (saved : Z) (active : TaskResumeCaller) (acquired : UCOS2_Verify_State),
        0 <= priority && priority < 63 && selected_kernel_profile(sg) &&
        task_resume_tcb_pool_aligned(sg) && g_OSTCBTbl(sg) == OSTCBTbl &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && time_dly_resume_acquire_facts(environment, critical, sg, caller, active,
          mask, initial, acquired, saved) && time_dly_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
        task_resume_masked(environment, critical, saved_local, sg, active,
          saved, acquired, acquired) * undef_data_at(&ptcb, OS_TCB *) *
        data_at(&prio, INT8U, priority) * data_at(&cpu_sr, OS_CPU_SR, saved)
    */
    /*@ Given saved active acquired */
    /*@ task_resume_masked(environment, critical, saved_local, sg, active,
          saved, acquired, acquired)
        which implies UCOS2_inv(sg, acquired) *
        task_resume_mask_frame(environment, critical, saved_local, sg, active,
          saved, acquired, acquired)
    */
    /*@ UCOS2_inv(sg, acquired) && 0 <= priority && priority < 63 && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl)
        which implies UCOS2_state_inv(sg, acquired) &&
        data_at(pointer_offset(OSTCBPrioTbl, priority, sizeof(OS_TCB *), OS_TCB *), OS_TCB *,
          prio_tbl_entry_to_addr(sg, prioTbl(TskState(acquired), priority))) *
        task_resume_priority_frame(sg, acquired, priority)
    */
    ptcb = OSTCBPrioTbl[prio];                                 /* Make sure that task exist            */
    if (ptcb == (OS_TCB *)0) {
        /*@ Assert time_dly_resume_acquire_facts(environment, critical, sg, caller, active,
          mask, initial, acquired, saved) &&
            0 <= priority && priority < 63 && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            time_dly_resume_critical_code(sg, priority, acquired, pair(67, false), acquired) &&
            time_dly_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
            task_resume_masked(environment, critical, saved_local, sg, active,
              saved, acquired, acquired) *
            data_at(&ptcb, OS_TCB *, 0) *
            data_at(&prio, INT8U, priority) * data_at(&cpu_sr, OS_CPU_SR, saved)
        */
        OS_EXIT_CRITICAL();
        /*@ Assert exists (returned : TaskResumeCaller) (restored : UCOS2_Verify_State),
            0 <= priority && priority < 63 && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            time_dly_resume_return_facts(environment, critical, sg, caller, returned,
              mask, initial, priority, 67, false, restored) && time_dly_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
            task_resume_closed(environment, critical, saved_local, sg, returned, mask, restored) *
            data_at(&ptcb, OS_TCB *, 0) *
            data_at(&prio, INT8U, priority) * data_at(&cpu_sr, OS_CPU_SR, saved)
        */
        /*@ Given returned restored */
        return (OS_ERR_TASK_NOT_EXIST);                        /* The task does not exist              */
    }
    if (ptcb == ((OS_TCB *)1)) {
        /*@ Assert time_dly_resume_acquire_facts(environment, critical, sg, caller, active,
          mask, initial, acquired, saved) &&
            0 <= priority && priority < 63 && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            time_dly_resume_critical_code(sg, priority, acquired, pair(67, false), acquired) &&
            time_dly_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
            task_resume_masked(environment, critical, saved_local, sg, active,
              saved, acquired, acquired) *
            data_at(&ptcb, OS_TCB *, 1) *
            data_at(&prio, INT8U, priority) * data_at(&cpu_sr, OS_CPU_SR, saved)
        */
        OS_EXIT_CRITICAL();
        /*@ Assert exists (returned : TaskResumeCaller) (restored : UCOS2_Verify_State),
            0 <= priority && priority < 63 && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            time_dly_resume_return_facts(environment, critical, sg, caller, returned,
              mask, initial, priority, 67, false, restored) && time_dly_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
            task_resume_closed(environment, critical, saved_local, sg, returned, mask, restored) *
            data_at(&ptcb, OS_TCB *, 1) *
            data_at(&prio, INT8U, priority) * data_at(&cpu_sr, OS_CPU_SR, saved)
        */
        /*@ Given returned restored */
        return (OS_ERR_TASK_NOT_EXIST);                        /* The task does not exist              */
    }
    /*@ Assert exists (tid : Z) (node : TaskAbstractState),
        0 <= priority && priority < 63 && selected_kernel_profile(sg) &&
        g_OSTCBTbl(sg) == OSTCBTbl && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && time_dly_resume_acquire_facts(environment, critical, sg, caller, active,
          mask, initial, acquired, saved) &&
        UCOS2_state_inv(sg, acquired) &&
        prioTbl(TskState(acquired), priority) == PTTask(tid) &&
        inUsedTaskStates(TskState(acquired), tid) == Some(node) &&
        ptcb == task_slot_addr(sg, tid) &&
        0 <= task_resume_y(node) && task_resume_y(node) < 8 && time_dly_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
        data_at(&(ptcb->OSTCBStat), INT8U, encode_task_status(stat(node))) *
        data_at(&(ptcb->OSTCBStatPend), INT8U, encode_pend_status(statPend(node))) *
        data_at(&(ptcb->OSTCBDly), INT32U, dly(node)) *
        data_at(&(ptcb->OSTCBY), INT8U, task_resume_y(node)) *
        data_at(&(ptcb->OSTCBBitX), INT8U, task_resume_bit_x(node)) *
        data_at(&(ptcb->OSTCBBitY), INT8U, task_resume_bit_y(node)) *
        data_at(&OSRdyGrp, OS_PRIO, task_resume_group(sg, acquired)) *
        data_at(pointer_offset(OSRdyTbl, task_resume_y(node), sizeof(unsigned char), unsigned char),
          OS_PRIO, task_resume_row(acquired, node)) *
        time_dly_resume_node_frame(sg, acquired, tid, node) *
        task_resume_mask_frame(environment, critical, saved_local, sg, active,
          saved, acquired, acquired) *
        data_at(&prio, INT8U, priority) * data_at(&cpu_sr, OS_CPU_SR, saved)
    */
    /*@ Given tid node */
    if (ptcb->OSTCBDly == 0u) {                                /* See if task is delayed               */
        /*@ Assert time_dly_resume_acquire_facts(environment, critical, sg, caller, active,
          mask, initial, acquired, saved) &&
            0 <= priority && priority < 63 && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            time_dly_resume_critical_code(sg, priority, acquired, pair(80, false), acquired) &&
            time_dly_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
            task_resume_masked(environment, critical, saved_local, sg, active,
              saved, acquired, acquired) *
            data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
            data_at(&prio, INT8U, priority) * data_at(&cpu_sr, OS_CPU_SR, saved)
        */
        OS_EXIT_CRITICAL();
        /*@ Assert exists (returned : TaskResumeCaller) (restored : UCOS2_Verify_State),
            0 <= priority && priority < 63 && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            time_dly_resume_return_facts(environment, critical, sg, caller, returned,
              mask, initial, priority, 80, false, restored) && time_dly_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
            task_resume_closed(environment, critical, saved_local, sg, returned, mask, restored) *
            data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
            data_at(&prio, INT8U, priority) * data_at(&cpu_sr, OS_CPU_SR, saved)
        */
        /*@ Given returned restored */
        return (OS_ERR_TIME_NOT_DLY);                          /* Indicate that task was not delayed   */
    }

    ptcb->OSTCBDly = 0u;                                       /* Clear the time delay                 */
    if ((ptcb->OSTCBStat & OS_STAT_PEND_ANY) != OS_STAT_RDY) {
        ptcb->OSTCBStat     &= ~OS_STAT_PEND_ANY;              /* Yes, Clear status flag               */
        ptcb->OSTCBStatPend  =  OS_STAT_PEND_TO;               /* Indicate PEND timeout                */
    } else {
        ptcb->OSTCBStatPend  =  OS_STAT_PEND_OK;
    }
    /*@ Assert 0 <= priority && priority < 63 && selected_kernel_profile(sg) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) && time_dly_resume_acquire_facts(environment, critical, sg, caller, active,
          mask, initial, acquired, saved) && UCOS2_state_inv(sg, acquired) &&
        prioTbl(TskState(acquired), priority) == PTTask(tid) &&
        inUsedTaskStates(TskState(acquired), tid) == Some(node) && dly(node) != 0 &&
        ptcb == task_slot_addr(sg, tid) &&
        0 <= task_resume_y(node) && task_resume_y(node) < 8 && time_dly_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
        data_at(&(ptcb->OSTCBStat), INT8U, encode_task_status(stat(task_expire_delay(node)))) *
        data_at(&(ptcb->OSTCBStatPend), INT8U, encode_pend_status(statPend(task_expire_delay(node)))) *
        data_at(&(ptcb->OSTCBDly), INT32U, 0) *
        data_at(&(ptcb->OSTCBY), INT8U, task_resume_y(node)) *
        data_at(&(ptcb->OSTCBBitX), INT8U, task_resume_bit_x(node)) *
        data_at(&(ptcb->OSTCBBitY), INT8U, task_resume_bit_y(node)) *
        data_at(&OSRdyGrp, OS_PRIO, task_resume_group(sg, acquired)) *
        data_at(pointer_offset(OSRdyTbl, task_resume_y(node), sizeof(unsigned char), unsigned char),
          OS_PRIO, task_resume_row(acquired, node)) *
        time_dly_resume_node_frame(sg, acquired, tid, node) *
        task_resume_mask_frame(environment, critical, saved_local, sg, active,
          saved, acquired, acquired) * data_at(&prio, INT8U, priority) * data_at(&cpu_sr, OS_CPU_SR, saved)
    */
    if ((ptcb->OSTCBStat & OS_STAT_SUSPEND) == OS_STAT_RDY) {  /* Is task suspended?                   */
        OSRdyGrp               |= ptcb->OSTCBBitY;             /* No,  Make ready                      */
        OSRdyTbl[ptcb->OSTCBY] |= ptcb->OSTCBBitX;
        OS_TRACE_TASK_READY(ptcb);
        /*@ Assert time_dly_resume_acquire_facts(environment, critical, sg, caller, active,
          mask, initial, acquired, saved) &&
            0 <= priority && priority < 63 && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            time_dly_resume_critical_code(sg, priority, acquired, pair(0, true), time_dly_resume_state(sg, acquired, tid, node)) &&
            time_dly_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
            task_resume_masked(environment, critical, saved_local, sg, active,
              saved, acquired, time_dly_resume_state(sg, acquired, tid, node)) *
            data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
            data_at(&prio, INT8U, priority) * data_at(&cpu_sr, OS_CPU_SR, saved)
        */
        OS_EXIT_CRITICAL();
        /*@ Assert exists (returned : TaskResumeCaller) (restored : UCOS2_Verify_State),
            0 <= priority && priority < 63 && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            time_dly_resume_return_facts(environment, critical, sg, caller, returned,
              mask, initial, priority, 0, true, restored) && time_dly_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
            task_resume_closed(environment, critical, saved_local, sg, returned, mask, restored) *
            data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
            data_at(&prio, INT8U, priority) * data_at(&cpu_sr, OS_CPU_SR, saved)
        */
        /*@ Given returned restored */
        /*@ Assert time_dly_resume_return_facts(environment, critical, sg, caller, returned,
              mask, initial, priority, 0, true, restored) &&
            0 <= priority && priority < 63 && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            task_resume_sched_safe(environment, critical, sg, returned, mask, restored, 0, X) &&
            task_resume_sched_pre(environment, critical, saved_local, sg, returned, mask, restored) *
            data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&prio, INT8U, priority) * data_at(&cpu_sr, OS_CPU_SR, saved)
        */
        OS_Sched();                                            /* See if this is new highest priority  */
    } else {
        /*@ Assert time_dly_resume_acquire_facts(environment, critical, sg, caller, active,
          mask, initial, acquired, saved) &&
            0 <= priority && priority < 63 && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            time_dly_resume_critical_code(sg, priority, acquired, pair(0, false), time_dly_resume_state(sg, acquired, tid, node)) &&
            time_dly_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
            task_resume_masked(environment, critical, saved_local, sg, active,
              saved, acquired, time_dly_resume_state(sg, acquired, tid, node)) *
            data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
            data_at(&prio, INT8U, priority) * data_at(&cpu_sr, OS_CPU_SR, saved)
        */
        OS_EXIT_CRITICAL();
        /*@ Assert exists (returned : TaskResumeCaller) (restored : UCOS2_Verify_State),
            0 <= priority && priority < 63 && os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            time_dly_resume_return_facts(environment, critical, sg, caller, returned,
              mask, initial, priority, 0, false, restored) && time_dly_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
            task_resume_closed(environment, critical, saved_local, sg, returned, mask, restored) *
            data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
            data_at(&prio, INT8U, priority) * data_at(&cpu_sr, OS_CPU_SR, saved)
        */
        /*@ Given returned restored */                                    /* Task may be suspended                */
    }
    return (OS_ERR_NONE);
}
