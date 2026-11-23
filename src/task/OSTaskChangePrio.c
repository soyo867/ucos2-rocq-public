/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSTaskChangePrio (INT8U  oldprio,
                         INT8U  newprio)
/*@ With (environment : TaskStackCallEnvironment) saved_local
         (critical : CriticalRegionResources) (sg : StableGlobVars)
         (execution : TaskChangePrioExecution) (mask requested destination : Z)
         (before : UCOS2_Verify_State) (X : Z -> UCOS2_Verify_State -> Prop)
    Require oldprio == requested && newprio == destination &&
            0 <= requested && requested <= 255 && 0 <= destination && destination <= 255 &&
            task_change_prio_static(sg) &&
            task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
              &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) &&
            task_change_prio_environment(environment, critical, sg, requested, destination, execution) &&
            task_change_prio_admission(environment, critical, sg, requested, destination, execution, mask, before) &&
            task_change_prio_safe_exec(environment, critical, sg, requested, destination, execution, mask, before, X) &&
            task_change_prio_closed(environment, saved_local, critical, sg, execution, mask, before)
    Ensure task_change_prio_safe_post(environment, saved_local, critical, sg, requested, destination,
             execution, mask, before, __return, X)
*/
{
#if (OS_EVENT_EN)
    OS_EVENT  *pevent;
#if (OS_EVENT_MULTI_EN > 0u)
    OS_EVENT **pevents;
#endif
#endif
    OS_TCB    *ptcb;
    INT8U      y_new;
    INT8U      x_new;
    INT8U      y_old;
    OS_PRIO    bity_new;
    OS_PRIO    bitx_new;
    OS_PRIO    bity_old;
    OS_PRIO    bitx_old;
#if OS_CRITICAL_METHOD == 3u
    OS_CPU_SR  cpu_sr = 0u;                                 /* Storage for CPU status register         */
#endif


#if OS_ARG_CHK_EN > 0u
    if (oldprio >= OS_LOWEST_PRIO) {
        if (oldprio != OS_PRIO_SELF) {
            return (OS_ERR_PRIO_INVALID);
        }
    }
    if (newprio >= OS_LOWEST_PRIO) {
        return (OS_ERR_PRIO_INVALID);
    }
#endif
    /*@ task_change_prio_closed(environment, saved_local, critical, sg, execution, mask, before)
        which implies UCOS2_state_inv(sg, before) &&
        task_change_prio_closed(environment, saved_local, critical, sg, execution, mask, before)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (acquired_execution : TaskChangePrioExecution) (acquired : UCOS2_Verify_State),
        task_change_prio_safe_exec(environment, critical, sg, requested, destination, execution, mask, before, X) &&
        oldprio == requested && newprio == destination && 0 <= requested && requested <= 255 && (requested < 63 || requested == 255) && 0 <= destination && destination < 63 &&
        task_change_prio_static(sg) && task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) &&
        task_change_prio_environment(environment, critical, sg, requested, destination, acquired_execution) &&
        task_change_prio_save_source(environment, critical, sg, requested, destination,
          execution, acquired_execution, mask, cpu_sr, before, acquired) &&
        interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, acquired) &&
        task_change_prio_call_source(acquired_execution, acquired) &&
        task_change_prio_owner_protocol(sg, requested, destination, acquired) &&
        task_change_prio_self_protocol(sg, requested, destination, acquired) &&
        task_change_prio_masked(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired) * undef_data_at(&pevent, OS_EVENT *) * undef_data_at(&ptcb, OS_TCB *) *
        undef_data_at(&y_new, INT8U) * undef_data_at(&x_new, INT8U) * undef_data_at(&y_old, INT8U) *
        undef_data_at(&bity_new, OS_PRIO) * undef_data_at(&bitx_new, OS_PRIO) *
        undef_data_at(&bity_old, OS_PRIO) * undef_data_at(&bitx_old, OS_PRIO)
    */
    /*@ Given acquired_execution acquired */
    /*@ task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) && task_change_prio_masked(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired)
        which implies PtrArray::full(OSTCBPrioTbl, 64, task_change_prio_table(sg, acquired)) *
        task_change_prio_table_frame(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired) */
    if (OSTCBPrioTbl[newprio] != (OS_TCB *)0) {             /* New priority must not already exist     */
        /*@ task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) && UCOS2_state_inv(sg, acquired) &&
        PtrArray::full(OSTCBPrioTbl, 64, task_change_prio_table(sg, acquired)) *
        task_change_prio_table_frame(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired)
        which implies task_change_prio_masked(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired) */
        OS_EXIT_CRITICAL();
        return (OS_ERR_PRIO_EXIST);
    }
    /*@ task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) && UCOS2_state_inv(sg, acquired) &&
        PtrArray::full(OSTCBPrioTbl, 64, task_change_prio_table(sg, acquired)) *
        task_change_prio_table_frame(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired)
        which implies task_change_prio_masked(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired) */
    if (oldprio == OS_PRIO_SELF) {                          /* See if changing self                    */
        /*@ task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) && 0 <= destination && destination < 63 && requested == 255 && Znth(destination, task_change_prio_table(sg, acquired), 0) == 0 &&
            UCOS2_state_inv(sg, acquired) &&
            task_change_prio_self_protocol(sg, requested, destination, acquired) &&
            task_change_prio_masked(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired)
            which implies exists (current_tid : Z) (current_node : TaskAbstractState),
            task_change_prio_current(acquired, current_tid, current_node) &&
            data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, current_tid)) *
            data_at(&((OS_TCB *)task_slot_addr(sg, current_tid))->OSTCBPrio, INT8U, curPrio(current_node)) *
            task_change_prio_self_frame(environment, saved_local, critical, sg,
              acquired_execution, cpu_sr, acquired, acquired, current_tid, current_node)
        */
        /*@ Given current_tid current_node */
        oldprio = OSTCBCur->OSTCBPrio;                      /* Yes, get priority                       */
        /*@ task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) && UCOS2_state_inv(sg, acquired) &&
            task_change_prio_current(acquired, current_tid, current_node) &&
            data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, current_tid)) *
            data_at(&((OS_TCB *)task_slot_addr(sg, current_tid))->OSTCBPrio, INT8U, curPrio(current_node)) *
            task_change_prio_self_frame(environment, saved_local, critical, sg,
              acquired_execution, cpu_sr, acquired, acquired, current_tid, current_node)
            which implies task_change_prio_masked(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired)
        */
    }
    /*@ Assert task_change_prio_safe_exec(environment, critical, sg, requested, destination, execution, mask, before, X) &&
        newprio == destination && 0 <= requested && requested <= 255 && (requested < 63 || requested == 255) && 0 <= destination && destination < 63 &&
        task_change_prio_static(sg) && task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) &&
        task_change_prio_environment(environment, critical, sg, requested, destination, acquired_execution) &&
        task_change_prio_save_source(environment, critical, sg, requested, destination,
          execution, acquired_execution, mask, cpu_sr, before, acquired) &&
        interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, acquired) &&
        task_change_prio_call_source(acquired_execution, acquired) &&
        task_change_prio_owner_protocol(sg, requested, destination, acquired) &&
        task_change_prio_self_protocol(sg, requested, destination, acquired) &&
        task_change_priority_selection(sg, acquired, requested, oldprio) &&
        0 <= oldprio && oldprio <= 63 && Znth(destination, task_change_prio_table(sg, acquired), 0) == 0 &&
        task_change_prio_masked(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired) * undef_data_at(&pevent, OS_EVENT *) * undef_data_at(&ptcb, OS_TCB *) *
        undef_data_at(&y_new, INT8U) * undef_data_at(&x_new, INT8U) * undef_data_at(&y_old, INT8U) *
        undef_data_at(&bity_new, OS_PRIO) * undef_data_at(&bitx_new, OS_PRIO) *
        undef_data_at(&bity_old, OS_PRIO) * undef_data_at(&bitx_old, OS_PRIO)
    */
    /* The resolved SELF target must retain the Idle priority sentinel. */
    if (oldprio == OS_TASK_IDLE_PRIO) {
        OS_EXIT_CRITICAL();
        return (OS_ERR_PRIO_INVALID);
    }
    /*@ task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) && task_change_prio_masked(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired)
        which implies PtrArray::full(OSTCBPrioTbl, 64, task_change_prio_table(sg, acquired)) *
        task_change_prio_table_frame(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired) */
    ptcb = OSTCBPrioTbl[oldprio];
    /*@ task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) && UCOS2_state_inv(sg, acquired) &&
        PtrArray::full(OSTCBPrioTbl, 64, task_change_prio_table(sg, acquired)) *
        task_change_prio_table_frame(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired)
        which implies task_change_prio_masked(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired) */
    if (ptcb == (OS_TCB *)0) {                              /* Does task to change exist?              */
        OS_EXIT_CRITICAL();                                 /* No, can't change its priority!          */
        return (OS_ERR_PRIO);
    }
    if (ptcb == ((OS_TCB *)1)) {                            /* Is task assigned to Mutex               */
        OS_EXIT_CRITICAL();                                 /* No, can't change its priority!          */
        return (OS_ERR_TASK_NOT_EXIST);
    }
    /*@ task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) && UCOS2_state_inv(sg, acquired) && task_change_prio_static(sg) &&
        task_change_priority_selection(sg, acquired, requested, oldprio) &&
        task_change_prio_owner_protocol(sg, requested, destination, acquired) &&
        0 <= oldprio && oldprio < 63 && 0 <= destination && destination < 63 &&
        Znth(destination, task_change_prio_table(sg, acquired), 0) == 0 &&
        ptcb == Znth(oldprio, task_change_prio_table(sg, acquired), 0) && ptcb != 0 && ptcb != 1 &&
        task_change_prio_masked(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired)
        which implies exists (target_tid : Z) (target_node : TaskAbstractState),
        ptcb == task_slot_addr(sg, target_tid) && task_change_prio_live(sg, acquired, requested, oldprio, destination, target_tid, target_node) &&
        0 <= tcb_y_of_prio(curPrio(target_node)) && tcb_y_of_prio(curPrio(target_node)) < 8 &&
        0 <= tcb_x_of_prio(curPrio(target_node)) && tcb_x_of_prio(curPrio(target_node)) < 8 &&
        PtrArray::full(OSTCBPrioTbl, 64, task_change_prio_table(sg, acquired)) *
        UCharArray::full(OSRdyTbl, 8, task_change_prio_ready_rows(acquired)) *
        data_at(&OSRdyGrp, OS_PRIO, task_change_prio_ready_group(acquired)) *
        data_at(&ptcb->OSTCBPrio, INT8U, curPrio(target_node)) *
        data_at(&ptcb->OSTCBY, INT8U, tcb_y_of_prio(curPrio(target_node))) *
        data_at(&ptcb->OSTCBX, INT8U, tcb_x_of_prio(curPrio(target_node))) *
        data_at(&ptcb->OSTCBBitY, OS_PRIO, tcb_bit_y_of_prio(curPrio(target_node))) *
        data_at(&ptcb->OSTCBBitX, OS_PRIO, tcb_bit_x_of_prio(curPrio(target_node))) *
        data_at(&ptcb->OSTCBEventPtr, OS_EVENT *, task_change_prio_event_pointer(sg, target_node)) * event_raw_rep(sg, TskState(acquired), EventState(acquired)) * task_change_prio_work_frame(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired, target_tid, target_node)
    */
    /*@ Given target_tid target_node */
#if OS_LOWEST_PRIO <= 63u
    y_new                 = (INT8U)(newprio >> 3u);         /* Yes, compute new TCB fields             */
    x_new                 = (INT8U)(newprio & 0x07u);
#else
    y_new                 = (INT8U)((INT8U)(newprio >> 4u) & 0x0Fu);
    x_new                 = (INT8U)(newprio & 0x0Fu);
#endif
    bity_new              = (OS_PRIO)(1uL << y_new);
    bitx_new              = (OS_PRIO)(1uL << x_new);

    /*@ 0 <= destination && destination < 63 &&
        y_new == unsigned_last_nbits(destination >> 3, 8) && x_new == (destination & 7)
        which implies
        0 <= y_new && y_new < 8 && 0 <= x_new && x_new < 8 &&
        y_new == tcb_y_of_prio(destination) && x_new == tcb_x_of_prio(destination)
    */

    OSTCBPrioTbl[oldprio] = (OS_TCB *)0;                    /* Remove TCB from old priority            */
    OSTCBPrioTbl[newprio] =  ptcb;                          /* Place pointer to TCB @ new priority     */
    y_old                 =  ptcb->OSTCBY;
    bity_old              =  ptcb->OSTCBBitY;
    bitx_old              =  ptcb->OSTCBBitX;
    if ((OSRdyTbl[y_old] &   bitx_old) != 0u) {             /* If task is ready make it not            */
         OSRdyTbl[y_old] &= (OS_PRIO)~bitx_old;
         if (OSRdyTbl[y_old] == 0u) {
             OSRdyGrp &= (OS_PRIO)~bity_old;
         }
         OSRdyGrp        |= bity_new;                       /* Make new priority ready to run          */
         OSRdyTbl[y_new] |= bitx_new;
         OS_TRACE_TASK_READY(ptcb);
    }
    /*@ Assert task_change_prio_safe_exec(environment, critical, sg, requested, destination, execution, mask, before, X) &&
        newprio == destination && 0 <= requested && requested <= 255 && (requested < 63 || requested == 255) && 0 <= destination && destination < 63 &&
        task_change_prio_static(sg) && task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) &&
        task_change_prio_environment(environment, critical, sg, requested, destination, acquired_execution) &&
        task_change_prio_save_source(environment, critical, sg, requested, destination,
          execution, acquired_execution, mask, cpu_sr, before, acquired) &&
        interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, acquired) &&
        task_change_prio_call_source(acquired_execution, acquired) &&
        task_change_prio_owner_protocol(sg, requested, destination, acquired) &&
        task_change_prio_self_protocol(sg, requested, destination, acquired) && ptcb == task_slot_addr(sg, target_tid) && task_change_prio_live(sg, acquired, requested, oldprio, destination, target_tid, target_node) &&
        y_new == tcb_y_of_prio(destination) && x_new == tcb_x_of_prio(destination) &&
        bity_new == tcb_bit_y_of_prio(destination) && bitx_new == tcb_bit_x_of_prio(destination) &&
        y_old == tcb_y_of_prio(curPrio(target_node)) &&
        0 <= y_old && y_old < 8 && 0 <= y_new && y_new < 8 &&
        bity_old == tcb_bit_y_of_prio(curPrio(target_node)) &&
        bitx_old == tcb_bit_x_of_prio(curPrio(target_node)) &&
        PtrArray::full(OSTCBPrioTbl, 64,
          task_change_prio_updated_table(sg, acquired, target_tid, target_node, oldprio, destination)) *
        UCharArray::full(OSRdyTbl, 8, mutex_priority_rows(task_change_prio_ready_rows(acquired),
            tcb_y_of_prio(curPrio(target_node)), tcb_bit_x_of_prio(curPrio(target_node)), destination)) *
        data_at(&OSRdyGrp, OS_PRIO, mutex_priority_group(task_change_prio_ready_rows(acquired), task_change_prio_ready_group(acquired),
          tcb_y_of_prio(curPrio(target_node)), tcb_bit_x_of_prio(curPrio(target_node)),
          tcb_bit_y_of_prio(curPrio(target_node)), destination)) * data_at(&ptcb->OSTCBPrio, INT8U, curPrio(target_node)) *
        data_at(&ptcb->OSTCBY, INT8U, tcb_y_of_prio(curPrio(target_node))) *
        data_at(&ptcb->OSTCBX, INT8U, tcb_x_of_prio(curPrio(target_node))) *
        data_at(&ptcb->OSTCBBitY, OS_PRIO, tcb_bit_y_of_prio(curPrio(target_node))) *
        data_at(&ptcb->OSTCBBitX, OS_PRIO, tcb_bit_x_of_prio(curPrio(target_node))) *
        data_at(&ptcb->OSTCBEventPtr, OS_EVENT *, task_change_prio_event_pointer(sg, target_node)) * event_raw_rep(sg, TskState(acquired), EventState(acquired)) * task_change_prio_work_frame(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired, target_tid, target_node) * undef_data_at(&pevent, OS_EVENT *)
    */

#if (OS_EVENT_EN)
    pevent = ptcb->OSTCBEventPtr;
    if (pevent != (OS_EVENT *)0) {
        /*@ task_change_prio_static(sg) && task_change_prio_live(sg, acquired, requested, oldprio, destination, target_tid, target_node) &&
            pevent == task_change_prio_event_pointer(sg, target_node) && pevent != 0 &&
            y_old == tcb_y_of_prio(curPrio(target_node)) &&
            bitx_old == tcb_bit_x_of_prio(curPrio(target_node)) &&
            bity_old == tcb_bit_y_of_prio(curPrio(target_node)) &&
            event_raw_rep(sg, TskState(acquired), EventState(acquired))
            which implies exists (waiting_eid : Z) (waiting_event : OSEventAbstractState),
            pevent == event_addr(sg, waiting_eid) &&
            task_change_prio_event_live(acquired, target_node, waiting_eid, waiting_event) &&
            oldprio == curPrio(target_node) &&
            y_old == tcb_y_of_prio(curPrio(target_node)) &&
            bitx_old == tcb_bit_x_of_prio(curPrio(target_node)) &&
            bity_old == tcb_bit_y_of_prio(curPrio(target_node)) &&
            0 <= y_old && y_old < 8 &&
            (Znth(y_old, task_change_prio_event_rows(acquired, waiting_event), 0) & bitx_old) != 0 &&
            UCharArray::full(pevent->OSEventTbl, 8, task_change_prio_event_rows(acquired, waiting_event)) *
            data_at(&pevent->OSEventGrp, OS_PRIO, task_change_prio_event_group(acquired, waiting_event)) *
            task_change_prio_event_frame(sg, acquired, waiting_eid, waiting_event)
        */
        /*@ Given waiting_eid waiting_event */
        pevent->OSEventTbl[y_old] &= (OS_PRIO)~bitx_old;    /* Remove old task prio from wait list     */
        if (pevent->OSEventTbl[y_old] == 0u) {
            pevent->OSEventGrp    &= (OS_PRIO)~bity_old;
        }
        pevent->OSEventGrp        |= bity_new;              /* Add    new task prio to   wait list     */
        pevent->OSEventTbl[y_new] |= bitx_new;
        /*@ Assert task_change_prio_safe_exec(environment, critical, sg, requested, destination, execution, mask, before, X) &&
        newprio == destination && 0 <= requested && requested <= 255 && (requested < 63 || requested == 255) && 0 <= destination && destination < 63 &&
        task_change_prio_static(sg) && task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) &&
        task_change_prio_environment(environment, critical, sg, requested, destination, acquired_execution) &&
        task_change_prio_save_source(environment, critical, sg, requested, destination,
          execution, acquired_execution, mask, cpu_sr, before, acquired) &&
        interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, acquired) &&
        task_change_prio_call_source(acquired_execution, acquired) &&
        task_change_prio_owner_protocol(sg, requested, destination, acquired) &&
        task_change_prio_self_protocol(sg, requested, destination, acquired) && ptcb == task_slot_addr(sg, target_tid) && task_change_prio_live(sg, acquired, requested, oldprio, destination, target_tid, target_node) &&
        y_new == tcb_y_of_prio(destination) && x_new == tcb_x_of_prio(destination) &&
        bity_new == tcb_bit_y_of_prio(destination) && bitx_new == tcb_bit_x_of_prio(destination) &&
        y_old == tcb_y_of_prio(curPrio(target_node)) &&
        bity_old == tcb_bit_y_of_prio(curPrio(target_node)) &&
        bitx_old == tcb_bit_x_of_prio(curPrio(target_node)) &&
            0 <= y_old && y_old < 8 && 0 <= y_new && y_new < 8 &&
            pevent == event_addr(sg, waiting_eid) &&
            task_change_prio_event_live(acquired, target_node, waiting_eid, waiting_event) &&
            PtrArray::full(OSTCBPrioTbl, 64,
          task_change_prio_updated_table(sg, acquired, target_tid, target_node, oldprio, destination)) *
        UCharArray::full(OSRdyTbl, 8, mutex_priority_rows(task_change_prio_ready_rows(acquired),
            tcb_y_of_prio(curPrio(target_node)), tcb_bit_x_of_prio(curPrio(target_node)), destination)) *
        data_at(&OSRdyGrp, OS_PRIO, mutex_priority_group(task_change_prio_ready_rows(acquired), task_change_prio_ready_group(acquired),
          tcb_y_of_prio(curPrio(target_node)), tcb_bit_x_of_prio(curPrio(target_node)),
          tcb_bit_y_of_prio(curPrio(target_node)), destination)) * data_at(&ptcb->OSTCBPrio, INT8U, curPrio(target_node)) *
        data_at(&ptcb->OSTCBY, INT8U, tcb_y_of_prio(curPrio(target_node))) *
        data_at(&ptcb->OSTCBX, INT8U, tcb_x_of_prio(curPrio(target_node))) *
        data_at(&ptcb->OSTCBBitY, OS_PRIO, tcb_bit_y_of_prio(curPrio(target_node))) *
        data_at(&ptcb->OSTCBBitX, OS_PRIO, tcb_bit_x_of_prio(curPrio(target_node))) *
        data_at(&ptcb->OSTCBEventPtr, OS_EVENT *, task_change_prio_event_pointer(sg, target_node)) * task_change_prio_work_frame(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired, target_tid, target_node) *
            UCharArray::full(((OS_EVENT *)event_addr(sg, waiting_eid))->OSEventTbl, 8,
              mutex_priority_rows(task_change_prio_event_rows(acquired, waiting_event),
                tcb_y_of_prio(curPrio(target_node)), tcb_bit_x_of_prio(curPrio(target_node)), destination)) *
            data_at(&((OS_EVENT *)event_addr(sg, waiting_eid))->OSEventGrp, OS_PRIO,
              mutex_priority_group(task_change_prio_event_rows(acquired, waiting_event),
                task_change_prio_event_group(acquired, waiting_event), tcb_y_of_prio(curPrio(target_node)),
                tcb_bit_x_of_prio(curPrio(target_node)), tcb_bit_y_of_prio(curPrio(target_node)), destination)) *
            task_change_prio_event_frame(sg, acquired, waiting_eid, waiting_event)
        */
        /*@ task_change_prio_event_live(acquired, target_node, waiting_eid, waiting_event) &&
            task_change_prio_static(sg) && UCOS2_state_inv(sg, acquired) &&
            UCharArray::full(((OS_EVENT *)event_addr(sg, waiting_eid))->OSEventTbl, 8,
              mutex_priority_rows(task_change_prio_event_rows(acquired, waiting_event),
                tcb_y_of_prio(curPrio(target_node)), tcb_bit_x_of_prio(curPrio(target_node)), destination)) *
            data_at(&((OS_EVENT *)event_addr(sg, waiting_eid))->OSEventGrp, OS_PRIO,
              mutex_priority_group(task_change_prio_event_rows(acquired, waiting_event),
                task_change_prio_event_group(acquired, waiting_event), tcb_y_of_prio(curPrio(target_node)),
                tcb_bit_x_of_prio(curPrio(target_node)), tcb_bit_y_of_prio(curPrio(target_node)), destination)) *
            task_change_prio_event_frame(sg, acquired, waiting_eid, waiting_event)
            which implies task_change_prio_event_storage(sg, acquired, target_node, destination)
        */
    }
#if (OS_EVENT_MULTI_EN > 0u)
    if (ptcb->OSTCBEventMultiPtr != (OS_EVENT **)0) {
        pevents =  ptcb->OSTCBEventMultiPtr;
        pevent  = *pevents;
        while (pevent != (OS_EVENT *)0) {
            pevent->OSEventTbl[y_old] &= (OS_PRIO)~bitx_old;   /* Remove old task prio from wait lists */
            if (pevent->OSEventTbl[y_old] == 0u) {
                pevent->OSEventGrp    &= (OS_PRIO)~bity_old;
            }
            pevent->OSEventGrp        |= bity_new;          /* Add    new task prio to   wait lists    */
            pevent->OSEventTbl[y_new] |= bitx_new;
            pevents++;
            pevent                     = *pevents;
        }
    }
#endif
#endif

    /*@ Assert task_change_prio_safe_exec(environment, critical, sg, requested, destination, execution, mask, before, X) &&
        newprio == destination && 0 <= requested && requested <= 255 && (requested < 63 || requested == 255) && 0 <= destination && destination < 63 &&
        task_change_prio_static(sg) && task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) &&
        task_change_prio_environment(environment, critical, sg, requested, destination, acquired_execution) &&
        task_change_prio_save_source(environment, critical, sg, requested, destination,
          execution, acquired_execution, mask, cpu_sr, before, acquired) &&
        interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, acquired) &&
        task_change_prio_call_source(acquired_execution, acquired) &&
        task_change_prio_owner_protocol(sg, requested, destination, acquired) &&
        task_change_prio_self_protocol(sg, requested, destination, acquired) && ptcb == task_slot_addr(sg, target_tid) && task_change_prio_live(sg, acquired, requested, oldprio, destination, target_tid, target_node) &&
        y_new == tcb_y_of_prio(destination) && x_new == tcb_x_of_prio(destination) &&
        bity_new == tcb_bit_y_of_prio(destination) && bitx_new == tcb_bit_x_of_prio(destination) &&
        y_old == tcb_y_of_prio(curPrio(target_node)) &&
        0 <= y_old && y_old < 8 && 0 <= y_new && y_new < 8 &&
        bity_old == tcb_bit_y_of_prio(curPrio(target_node)) &&
        bitx_old == tcb_bit_x_of_prio(curPrio(target_node)) &&
        pevent == task_change_prio_event_pointer(sg, target_node) &&
        PtrArray::full(OSTCBPrioTbl, 64,
          task_change_prio_updated_table(sg, acquired, target_tid, target_node, oldprio, destination)) *
        UCharArray::full(OSRdyTbl, 8, mutex_priority_rows(task_change_prio_ready_rows(acquired),
            tcb_y_of_prio(curPrio(target_node)), tcb_bit_x_of_prio(curPrio(target_node)), destination)) *
        data_at(&OSRdyGrp, OS_PRIO, mutex_priority_group(task_change_prio_ready_rows(acquired), task_change_prio_ready_group(acquired),
          tcb_y_of_prio(curPrio(target_node)), tcb_bit_x_of_prio(curPrio(target_node)),
          tcb_bit_y_of_prio(curPrio(target_node)), destination)) * data_at(&ptcb->OSTCBPrio, INT8U, curPrio(target_node)) *
        data_at(&ptcb->OSTCBY, INT8U, tcb_y_of_prio(curPrio(target_node))) *
        data_at(&ptcb->OSTCBX, INT8U, tcb_x_of_prio(curPrio(target_node))) *
        data_at(&ptcb->OSTCBBitY, OS_PRIO, tcb_bit_y_of_prio(curPrio(target_node))) *
        data_at(&ptcb->OSTCBBitX, OS_PRIO, tcb_bit_x_of_prio(curPrio(target_node))) *
        data_at(&ptcb->OSTCBEventPtr, OS_EVENT *, task_change_prio_event_pointer(sg, target_node)) * task_change_prio_event_storage(sg, acquired, target_node, destination) * task_change_prio_work_frame(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired, target_tid, target_node)
    */
    ptcb->OSTCBPrio = newprio;                              /* Set new task priority                   */
    ptcb->OSTCBY    = y_new;
    ptcb->OSTCBX    = x_new;
    ptcb->OSTCBBitY = bity_new;
    ptcb->OSTCBBitX = bitx_new;
    /*@ task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) &&
        task_change_prio_work_frame(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired, target_tid, target_node)
        which implies
        data_at(&OSTCBCur, OS_TCB *, encode_task_link(sg, curTaskID(SchedState(acquired)))) *
        data_at(&OSPrioCur, INT8U, sched_priority_byte(curSchedPrio(SchedState(acquired)))) *
        task_change_prio_work_frame_without_current(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired, target_tid, target_node)
    */
    if (ptcb == OSTCBCur) {
        OSPrioCur = newprio;
    }
    /*@ Assert task_change_prio_safe_exec(environment, critical, sg, requested, destination, execution, mask, before, X) &&
        newprio == destination && 0 <= requested && requested <= 255 && (requested < 63 || requested == 255) && 0 <= destination && destination < 63 &&
        task_change_prio_static(sg) && task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) &&
        task_change_prio_environment(environment, critical, sg, requested, destination, acquired_execution) &&
        task_change_prio_save_source(environment, critical, sg, requested, destination,
          execution, acquired_execution, mask, cpu_sr, before, acquired) &&
        interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, acquired) &&
        task_change_prio_call_source(acquired_execution, acquired) &&
        task_change_prio_owner_protocol(sg, requested, destination, acquired) &&
        task_change_prio_self_protocol(sg, requested, destination, acquired) && ptcb == task_slot_addr(sg, target_tid) && task_change_prio_live(sg, acquired, requested, oldprio, destination, target_tid, target_node) &&
        y_new == tcb_y_of_prio(destination) && x_new == tcb_x_of_prio(destination) &&
        bity_new == tcb_bit_y_of_prio(destination) && bitx_new == tcb_bit_x_of_prio(destination) &&
        y_old == tcb_y_of_prio(curPrio(target_node)) &&
        0 <= y_old && y_old < 8 && 0 <= y_new && y_new < 8 &&
        bity_old == tcb_bit_y_of_prio(curPrio(target_node)) &&
        bitx_old == tcb_bit_x_of_prio(curPrio(target_node)) &&
        pevent == task_change_prio_event_pointer(sg, target_node) &&
        PtrArray::full(OSTCBPrioTbl, 64,
          task_change_prio_updated_table(sg, acquired, target_tid, target_node, oldprio, destination)) *
        UCharArray::full(OSRdyTbl, 8, mutex_priority_rows(task_change_prio_ready_rows(acquired),
            tcb_y_of_prio(curPrio(target_node)), tcb_bit_x_of_prio(curPrio(target_node)), destination)) *
        data_at(&OSRdyGrp, OS_PRIO, mutex_priority_group(task_change_prio_ready_rows(acquired), task_change_prio_ready_group(acquired),
          tcb_y_of_prio(curPrio(target_node)), tcb_bit_x_of_prio(curPrio(target_node)),
          tcb_bit_y_of_prio(curPrio(target_node)), destination)) * data_at(&ptcb->OSTCBPrio, INT8U, destination) *
        data_at(&ptcb->OSTCBY, INT8U, tcb_y_of_prio(destination)) *
        data_at(&ptcb->OSTCBX, INT8U, tcb_x_of_prio(destination)) *
        data_at(&ptcb->OSTCBBitY, OS_PRIO, tcb_bit_y_of_prio(destination)) *
        data_at(&ptcb->OSTCBBitX, OS_PRIO, tcb_bit_x_of_prio(destination)) *
        data_at(&ptcb->OSTCBEventPtr, OS_EVENT *, task_change_prio_event_pointer(sg, target_node)) * task_change_prio_event_storage(sg, acquired, target_node, destination) * data_at(&OSTCBCur, OS_TCB *, encode_task_link(sg, curTaskID(SchedState(acquired)))) *
        data_at(&OSPrioCur, INT8U, sched_priority_byte(
          task_change_priority_cached_priority(SchedState(acquired), target_tid, destination))) *
        task_change_prio_work_frame_without_current(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, acquired, target_tid, target_node)
    */
    /*@ Assert task_change_prio_safe_exec(environment, critical, sg, requested, destination, execution, mask, before, X) &&
        newprio == destination && 0 <= requested && requested <= 255 && (requested < 63 || requested == 255) && 0 <= destination && destination < 63 &&
        task_change_prio_static(sg) && task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) &&
        task_change_prio_environment(environment, critical, sg, requested, destination, acquired_execution) &&
        task_change_prio_save_source(environment, critical, sg, requested, destination,
          execution, acquired_execution, mask, cpu_sr, before, acquired) &&
        interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, acquired) &&
        task_change_prio_call_source(acquired_execution, acquired) &&
        task_change_prio_owner_protocol(sg, requested, destination, acquired) &&
        task_change_prio_self_protocol(sg, requested, destination, acquired) && task_change_prio_live(sg, acquired, requested, oldprio, destination, target_tid, target_node) &&
        task_change_prio_critical_code(sg, requested, destination, acquired, 0, task_change_priority_state(sg, acquired, target_tid, target_node, oldprio, destination)) &&
        UCOS2_state_inv(sg, task_change_priority_state(sg, acquired, target_tid, target_node, oldprio, destination)) &&
        task_change_prio_call_source(acquired_execution, task_change_priority_state(sg, acquired, target_tid, target_node, oldprio, destination)) &&
        task_change_prio_masked(environment, saved_local, critical, sg,
          acquired_execution, cpu_sr, acquired, task_change_priority_state(sg, acquired, target_tid, target_node, oldprio, destination)) *
        undef_data_at(&pevent, OS_EVENT *) * undef_data_at(&ptcb, OS_TCB *) *
        undef_data_at(&y_new, INT8U) * undef_data_at(&x_new, INT8U) * undef_data_at(&y_old, INT8U) *
        undef_data_at(&bity_new, OS_PRIO) * undef_data_at(&bitx_new, OS_PRIO) *
        undef_data_at(&bity_old, OS_PRIO) * undef_data_at(&bitx_old, OS_PRIO)
    */
    OS_EXIT_CRITICAL();
    /*@ Assert exists (restored_execution : TaskChangePrioExecution) (restored : UCOS2_Verify_State),
        task_change_prio_safe_exec(environment, critical, sg, requested, destination, execution, mask, before, X) &&
        newprio == destination && 0 <= requested && requested <= 255 && (requested < 63 || requested == 255) && 0 <= destination && destination < 63 &&
        task_change_prio_static(sg) && task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) &&
        task_change_prio_environment(environment, critical, sg, requested, destination, acquired_execution) &&
        task_change_prio_save_source(environment, critical, sg, requested, destination,
          execution, acquired_execution, mask, cpu_sr, before, acquired) &&
        interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, acquired) &&
        task_change_prio_call_source(acquired_execution, acquired) &&
        task_change_prio_owner_protocol(sg, requested, destination, acquired) &&
        task_change_prio_self_protocol(sg, requested, destination, acquired) && task_change_prio_live(sg, acquired, requested, oldprio, destination, target_tid, target_node) &&
        task_change_prio_critical_code(sg, requested, destination, acquired, 0, task_change_priority_state(sg, acquired, target_tid, target_node, oldprio, destination)) &&
        UCOS2_state_inv(sg, task_change_priority_state(sg, acquired, target_tid, target_node, oldprio, destination)) &&
        task_change_prio_restore_source(environment, critical, sg,
          acquired_execution, restored_execution, task_change_priority_state(sg, acquired, target_tid, target_node, oldprio, destination), restored) &&
        task_change_prio_environment(environment, critical, sg, requested, destination, restored_execution) &&
        task_change_prio_call_source(restored_execution, restored) &&
        task_change_prio_closed(environment, saved_local, critical, sg, restored_execution, mask, restored) *
        undef_data_at(&pevent, OS_EVENT *) * undef_data_at(&ptcb, OS_TCB *) *
        undef_data_at(&y_new, INT8U) * undef_data_at(&x_new, INT8U) * undef_data_at(&y_old, INT8U) *
        undef_data_at(&bity_new, OS_PRIO) * undef_data_at(&bitx_new, OS_PRIO) *
        undef_data_at(&bity_old, OS_PRIO) * undef_data_at(&bitx_old, OS_PRIO)
    */
    /*@ Given restored_execution restored */
    /*@ task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) && task_change_prio_closed(environment, saved_local, critical, sg, restored_execution, mask, restored)
        which implies data_at(&OSRunning, INT8U, task_change_prio_running(restored)) *
        task_change_prio_closed_without_running(environment, saved_local, critical, sg,
          restored_execution, mask, restored)
    */
    if (OSRunning == OS_TRUE) {
        /*@ task_change_prio_addresses(sg, OSTCBPrioTbl, &OSTCBCur, &OSRdyGrp, OSRdyTbl, &OSRunning,
          &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, &OSCtxSwCtr, OSUnMapTbl) && data_at(&OSRunning, INT8U, task_change_prio_running(restored)) *
        task_change_prio_closed_without_running(environment, saved_local, critical, sg,
          restored_execution, mask, restored) which implies task_change_prio_closed(environment, saved_local, critical, sg, restored_execution, mask, restored) */
        /*@ task_change_prio_static(sg) &&
            task_change_prio_environment(environment, critical, sg, requested, destination, restored_execution) &&
            task_change_prio_call_source(restored_execution, restored) &&
            task_change_prio_running(restored) == 1 && task_change_prio_closed(environment, saved_local, critical, sg, restored_execution, mask, restored)
            which implies task_change_prio_scheduler_pre(environment, saved_local, critical, sg,
              restored_execution, mask, restored)
        */
        OS_Sched();                                         /* Find new highest priority task          */
    }
    return (OS_ERR_NONE);
}
