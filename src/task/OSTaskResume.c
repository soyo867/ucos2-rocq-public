/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSTaskResume (INT8U prio)
/*@ With (environment : TaskStackCallEnvironment) saved_local
         (critical : CriticalRegionResources) (sg : StableGlobVars)
         (priority : Z) (caller : TaskResumeCaller) (mask : Z) (initial : UCOS2_Verify_State)
         (X : Z -> UCOS2_Verify_State -> Prop)
    Require prio == priority && 0 <= priority && priority <= 255 &&
            selected_kernel_profile(sg) && cfgArgumentChecks(osKernelConfig(sg)) == true &&
            g_OSRunning(sg) == &OSRunning && g_OSTCBTbl(sg) == OSTCBTbl &&
            os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            (63 <= priority || (task_resume_tcb_pool_aligned(sg) && UCOS2_state_inv(sg, initial) &&
              task_resume_clients(environment, critical, caller) &&
              task_resume_caller_source(sg, caller, initial))) &&
            task_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
            task_resume_closed(environment, critical, saved_local, sg, caller, mask, initial)
    Ensure task_resume_post(environment, critical, saved_local, sg, caller, mask, initial, priority, __return, X)
*/
{
    OS_TCB    *ptcb;
#if OS_CRITICAL_METHOD == 3u                                  /* Storage for CPU status register       */
    OS_CPU_SR  cpu_sr = 0u;
#endif



#if OS_ARG_CHK_EN > 0u
    if (prio >= OS_LOWEST_PRIO) {                             /* Make sure task priority is valid      */
        return (OS_ERR_PRIO_INVALID);
    }
#endif
    OS_ENTER_CRITICAL();
    /*@ Assert exists (saved : Z) (active : TaskResumeCaller) (acquired : UCOS2_Verify_State),
        0 <= priority && priority < 63 && selected_kernel_profile(sg) &&
        task_resume_tcb_pool_aligned(sg) &&
        g_OSRunning(sg) == &OSRunning && g_OSTCBTbl(sg) == OSTCBTbl &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        task_resume_acquire_facts(environment, critical, sg, caller, active,
          mask, initial, acquired, saved) &&
        task_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
        task_resume_masked(environment, critical, saved_local, sg, active,
          saved, acquired, acquired) * undef_data_at(&ptcb, OS_TCB *) *
        data_at(&prio, INT8U, priority) *
        data_at(&cpu_sr, OS_CPU_SR, saved)
    */
    /*@ Given saved active acquired */
    /*@ task_resume_masked(environment, critical, saved_local, sg, active,
          saved, acquired, acquired)
        which implies
        UCOS2_inv(sg, acquired) *
        task_resume_mask_frame(environment, critical, saved_local, sg, active,
          saved, acquired, acquired)
    */
    /*@ UCOS2_inv(sg, acquired) && 0 <= priority && priority < 63 &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl)
        which implies
        UCOS2_state_inv(sg, acquired) &&
        data_at(pointer_offset(OSTCBPrioTbl, priority, sizeof(OS_TCB *), OS_TCB *), OS_TCB *,
          prio_tbl_entry_to_addr(sg, prioTbl(TskState(acquired), priority))) *
        task_resume_priority_frame(sg, acquired, priority)
    */
    ptcb = OSTCBPrioTbl[prio];
    if (ptcb == (OS_TCB *)0) {                                /* Task to suspend must exist            */
        /*@ Assert task_resume_acquire_facts(environment, critical, sg, caller, active,
              mask, initial, acquired, saved) &&
            0 <= priority && priority < 63 &&
            task_resume_critical_code(sg, priority, acquired, pair(70, false), acquired) &&
            task_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
            task_resume_masked(environment, critical, saved_local, sg, active,
              saved, acquired, acquired) * data_at(&ptcb, OS_TCB *, 0) *
        data_at(&prio, INT8U, priority) *
        data_at(&cpu_sr, OS_CPU_SR, saved)
        */
        OS_EXIT_CRITICAL();
        return (OS_ERR_TASK_RESUME_PRIO);
    }
    if (ptcb == ((OS_TCB *)1)) {                              /* Exact reserved macro expansion        */
        /*@ Assert task_resume_acquire_facts(environment, critical, sg, caller, active,
              mask, initial, acquired, saved) &&
            0 <= priority && priority < 63 &&
            task_resume_critical_code(sg, priority, acquired, pair(67, false), acquired) &&
            task_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
            task_resume_masked(environment, critical, saved_local, sg, active,
              saved, acquired, acquired) * data_at(&ptcb, OS_TCB *, 1) *
        data_at(&prio, INT8U, priority) *
        data_at(&cpu_sr, OS_CPU_SR, saved)
        */
        OS_EXIT_CRITICAL();
        return (OS_ERR_TASK_NOT_EXIST);
    }
    /*@ Assert exists (tid : Z) (node : TaskAbstractState),
        0 <= priority && priority < 63 && selected_kernel_profile(sg) &&
        g_OSRunning(sg) == &OSRunning && g_OSTCBTbl(sg) == OSTCBTbl &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        task_resume_acquire_facts(environment, critical, sg, caller, active,
          mask, initial, acquired, saved) && UCOS2_state_inv(sg, acquired) &&
        prioTbl(TskState(acquired), priority) == PTTask(tid) &&
        inUsedTaskStates(TskState(acquired), tid) == Some(node) &&
        ptcb == task_slot_addr(sg, tid) &&
        0 <= task_resume_y(node) && task_resume_y(node) < 8 &&
        task_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
        data_at(&(ptcb->OSTCBStat), INT8U, encode_task_status(stat(node))) *
        data_at(&(ptcb->OSTCBDly), INT32U, dly(node)) *
        data_at(&(ptcb->OSTCBY), INT8U, task_resume_y(node)) *
        data_at(&(ptcb->OSTCBBitX), INT8U, task_resume_bit_x(node)) *
        data_at(&(ptcb->OSTCBBitY), INT8U, task_resume_bit_y(node)) *
        data_at(&OSRdyGrp, OS_PRIO, task_resume_group(sg, acquired)) *
        data_at(pointer_offset(OSRdyTbl, task_resume_y(node), sizeof(unsigned char), unsigned char),
          OS_PRIO, task_resume_row(acquired, node)) *
        task_resume_node_frame(sg, acquired, tid, node) *
        task_resume_mask_frame(environment, critical, saved_local, sg, active,
          saved, acquired, acquired) *
        data_at(&prio, INT8U, priority) *
        data_at(&cpu_sr, OS_CPU_SR, saved)
    */
    /*@ Given tid node */
    if ((ptcb->OSTCBStat & OS_STAT_SUSPEND) != OS_STAT_RDY) { /* Task must be suspended                */
        ptcb->OSTCBStat &= (INT8U)~(INT8U)OS_STAT_SUSPEND;    /* Remove suspension                     */
        if ((ptcb->OSTCBStat & OS_STAT_PEND_ANY) == OS_STAT_RDY) { /* See if task is now ready         */
            if (ptcb->OSTCBDly == 0u) {
                OSRdyGrp               |= ptcb->OSTCBBitY;    /* Yes, Make task ready to run           */
                OSRdyTbl[ptcb->OSTCBY] |= ptcb->OSTCBBitX;
                OS_TRACE_TASK_READY(ptcb);
                /*@ Assert task_resume_acquire_facts(environment, critical, sg, caller, active,
                      mask, initial, acquired, saved) &&
                    0 <= priority && priority < 63 &&
                    g_OSRunning(sg) == &OSRunning &&
                    os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                      &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                      &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                    task_resume_critical_code(sg, priority, acquired, pair(0, true),
                      task_resume_state(sg, acquired, tid, node)) &&
                    task_resume_caller_source(sg, active, task_resume_state(sg, acquired, tid, node)) &&
                    task_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
                    task_resume_masked(environment, critical, saved_local, sg, active,
                      saved, acquired, task_resume_state(sg, acquired, tid, node)) *
                    data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&prio, INT8U, priority) *
        data_at(&cpu_sr, OS_CPU_SR, saved)
                */
                OS_EXIT_CRITICAL();
                /*@ Assert exists (returned : TaskResumeCaller) (restored : UCOS2_Verify_State),
                    0 <= priority && priority < 63 && g_OSRunning(sg) == &OSRunning &&
                    os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                      &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                      &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                    task_resume_return_facts(environment, critical, sg, caller, returned,
                      mask, initial, priority, 0, true, restored) &&
                    task_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
                    task_resume_closed(environment, critical, saved_local, sg, returned, mask, restored) *
                    data_at(&cpu_sr, OS_CPU_SR, saved) *
                    data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&prio, INT8U, priority)
                */
                /*@ Given returned restored */
                /*@ g_OSRunning(sg) == &OSRunning &&
                    task_resume_closed(environment, critical, saved_local, sg, returned, mask, restored)
                    which implies
                    data_at(&OSRunning, BOOLEAN, task_resume_running(restored)) *
                    task_resume_running_frame(environment, critical, saved_local, sg, returned, mask, restored)
                */
                if (OSRunning == OS_TRUE) {
                    OS_TRACE_TASK_RESUME(ptcb);
                    /*@ Assert task_resume_return_facts(environment, critical, sg, caller, returned,
                          mask, initial, priority, 0, true, restored) &&
                        0 <= priority && priority < 63 &&
                        task_resume_requests_schedule(true, restored) == true &&
                        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
                        task_resume_sched_safe(environment, critical, sg, returned, mask, restored, 0, X) &&
                        task_resume_sched_pre(environment, critical, saved_local, sg, returned, mask, restored) *
                        data_at(&cpu_sr, OS_CPU_SR, saved) *
                        data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&prio, INT8U, priority)
                    */
                    OS_Sched();                               /* Find new highest priority task        */
                }
            } else {
                /*@ Assert task_resume_acquire_facts(environment, critical, sg, caller, active,
                      mask, initial, acquired, saved) &&
                    0 <= priority && priority < 63 &&
                    task_resume_critical_code(sg, priority, acquired, pair(0, false),
                      task_resume_state(sg, acquired, tid, node)) &&
                    task_resume_caller_source(sg, active, task_resume_state(sg, acquired, tid, node)) &&
                    task_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
                    task_resume_masked(environment, critical, saved_local, sg, active,
                      saved, acquired, task_resume_state(sg, acquired, tid, node)) *
                    data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&prio, INT8U, priority) *
        data_at(&cpu_sr, OS_CPU_SR, saved)
                */
                OS_EXIT_CRITICAL();
            }
        } else {                                              /* Must be pending on event              */
            /*@ Assert task_resume_acquire_facts(environment, critical, sg, caller, active,
                  mask, initial, acquired, saved) &&
                0 <= priority && priority < 63 &&
                task_resume_critical_code(sg, priority, acquired, pair(0, false),
                  task_resume_state(sg, acquired, tid, node)) &&
                task_resume_caller_source(sg, active, task_resume_state(sg, acquired, tid, node)) &&
                task_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
                task_resume_masked(environment, critical, saved_local, sg, active,
                  saved, acquired, task_resume_state(sg, acquired, tid, node)) *
                data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&prio, INT8U, priority) *
        data_at(&cpu_sr, OS_CPU_SR, saved)
            */
            OS_EXIT_CRITICAL();
        }
        return (OS_ERR_NONE);
    }
    /*@ Assert task_resume_acquire_facts(environment, critical, sg, caller, active,
          mask, initial, acquired, saved) &&
        0 <= priority && priority < 63 &&
        task_resume_critical_code(sg, priority, acquired, pair(68, false), acquired) &&
        task_resume_safe(environment, critical, sg, caller, mask, priority, initial, X) &&
        task_resume_masked(environment, critical, saved_local, sg, active,
          saved, acquired, acquired) * data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&prio, INT8U, priority) *
        data_at(&cpu_sr, OS_CPU_SR, saved)
    */
    OS_EXIT_CRITICAL();
    return (OS_ERR_TASK_NOT_SUSPENDED);
}
