/* Single-function full-profile carrier; compose into the original-header input. */
INT8U  OS_EventTaskRdy (OS_EVENT  *pevent,
                        void      *pmsg,
                        INT8U      msk,
                        INT8U      pend_stat)
/*@ With (sg : StableGlobVars) (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState)
         eid (e : OSEventAbstractState) tid (t : TaskAbstractState)
         group (rows : list Z) (pointers : list Z) (instances : EventTaskRemoveMultiInstances)
    Require pevent == event_addr(sg, eid) &&
            &OSUnMapTbl == g_OSUnMapTbl(sg) &&
            &OSTCBPrioTbl == g_OSTCBPrioTbl(sg) &&
            &OSRdyGrp == g_OSRdyGrp(sg) && &OSRdyTbl == g_OSRdyTbl(sg) &&
            event_task_rdy_full_pre(sg, tasks, events, eid, e, tid, t, pointers, instances, msk, pend_stat, group, rows)
    Ensure event_task_rdy_full_post(sg, tasks, events, eid, e, tid, t, pointers, instances, pmsg, msk, pend_stat, group, rows, __return)
*/
{
    OS_TCB   *ptcb;
    INT8U     y;
    INT8U     x;
    INT8U     prio;
#if OS_LOWEST_PRIO > 63u
    OS_PRIO  *ptbl;
#endif


#if OS_LOWEST_PRIO <= 63u
    
/*@ pevent == event_addr(sg, eid) && &OSRdyGrp == g_OSRdyGrp(sg) &&
        event_task_rdy_full_pre(sg, tasks, events, eid, e, tid, t, pointers, instances, msk, pend_stat, group, rows)
        which implies
        pevent == event_addr(sg, eid) && &OSRdyGrp == g_OSRdyGrp(sg) && event_task_rdy_full_entry(sg, tasks, events, eid, e, tid, t, pointers, instances) &&
        0 <= msk && msk < 256 && 0 <= pend_stat && pend_stat < 256 &&
        Zlength(rows) == 8 && 0 <= curPrio(t) && curPrio(t) < 64 &&
        event_wait_priority(tasks, e) == curPrio(t) &&
        prioTbl(tasks, curPrio(t)) == PTTask(tid) &&
        unmap_value(encode_event_wait_grp(waitList(e), tasks)) == tcb_y_of_prio(curPrio(t)) &&
        unmap_value(encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t)))) == tcb_x_of_prio(curPrio(t)) &&
        0 <= tcb_y_of_prio(curPrio(t)) && tcb_y_of_prio(curPrio(t)) < 8 && 0 <= tcb_x_of_prio(curPrio(t)) && tcb_x_of_prio(curPrio(t)) < 8 &&
        tcb_configured_storage_rep(true, true, task_slot_addr(sg, tid), task_layout_image(sg, t)) *
        data_at(&(pevent->OSEventGrp), OS_PRIO, encode_event_wait_grp(waitList(e), tasks)) *
        data_at(pointer_offset(&(pevent->OSEventTbl), tcb_y_of_prio(curPrio(t)), OS_PRIO), OS_PRIO, encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t)))) *
        event_task_remove_multi_event_frame(sg, tasks, events, eid, e, tcb_y_of_prio(curPrio(t))) *
        event_task_rdy_full_array(tcbEventMultiPtr(t), pointers) *
        unmap_table_rep(sg) * store_prio_tbl(sg, prioTbl(tasks)) *
        data_at(&OSRdyGrp, OS_PRIO, group) * UCharArray::full(g_OSRdyTbl(sg), 8, rows)
    */

/*@ &OSUnMapTbl == g_OSUnMapTbl(sg) && unmap_table_rep(sg) * data_at(&(pevent->OSEventGrp), OS_PRIO, encode_event_wait_grp(waitList(e), tasks))
        which implies
        &OSUnMapTbl == g_OSUnMapTbl(sg) && data_at(pointer_offset(&OSUnMapTbl, encode_event_wait_grp(waitList(e), tasks), INT8U), INT8U, unmap_value(encode_event_wait_grp(waitList(e), tasks))) *
        UCharArray::missing_i(g_OSUnMapTbl(sg), encode_event_wait_grp(waitList(e), tasks), 0, 256, unmap_table) *
        data_at(&(pevent->OSEventGrp), OS_PRIO, encode_event_wait_grp(waitList(e), tasks))
    */
y    = OSUnMapTbl[pevent->OSEventGrp];              /* Find HPT waiting for message                */
    
/*@ &OSUnMapTbl == g_OSUnMapTbl(sg) && data_at(pointer_offset(&OSUnMapTbl, encode_event_wait_grp(waitList(e), tasks), INT8U), INT8U, unmap_value(encode_event_wait_grp(waitList(e), tasks))) *
        UCharArray::missing_i(g_OSUnMapTbl(sg), encode_event_wait_grp(waitList(e), tasks), 0, 256, unmap_table) *
        data_at(&(pevent->OSEventGrp), OS_PRIO, encode_event_wait_grp(waitList(e), tasks))
        which implies &OSUnMapTbl == g_OSUnMapTbl(sg) && unmap_table_rep(sg) * data_at(&(pevent->OSEventGrp), OS_PRIO, encode_event_wait_grp(waitList(e), tasks))
    */

/*@ &OSUnMapTbl == g_OSUnMapTbl(sg) && unmap_table_rep(sg) * data_at(pointer_offset(&(pevent->OSEventTbl), tcb_y_of_prio(curPrio(t)), OS_PRIO), OS_PRIO, encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t))))
        which implies
        &OSUnMapTbl == g_OSUnMapTbl(sg) && data_at(pointer_offset(&OSUnMapTbl, encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t))), INT8U), INT8U, unmap_value(encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t))))) *
        UCharArray::missing_i(g_OSUnMapTbl(sg), encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t))), 0, 256, unmap_table) *
        data_at(pointer_offset(&(pevent->OSEventTbl), tcb_y_of_prio(curPrio(t)), OS_PRIO), OS_PRIO, encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t))))
    */
x    = OSUnMapTbl[pevent->OSEventTbl[y]];
    
/*@ &OSUnMapTbl == g_OSUnMapTbl(sg) && data_at(pointer_offset(&OSUnMapTbl, encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t))), INT8U), INT8U, unmap_value(encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t))))) *
        UCharArray::missing_i(g_OSUnMapTbl(sg), encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t))), 0, 256, unmap_table) *
        data_at(pointer_offset(&(pevent->OSEventTbl), tcb_y_of_prio(curPrio(t)), OS_PRIO), OS_PRIO, encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t))))
        which implies &OSUnMapTbl == g_OSUnMapTbl(sg) && unmap_table_rep(sg) * data_at(pointer_offset(&(pevent->OSEventTbl), tcb_y_of_prio(curPrio(t)), OS_PRIO), OS_PRIO, encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t))))
    */
prio = (INT8U)((y << 3u) + x);                      /* Find priority of task getting the msg       */
#else
    if ((pevent->OSEventGrp & 0xFFu) != 0u) {           /* Find HPT waiting for message                */
        y = OSUnMapTbl[ pevent->OSEventGrp & 0xFFu];
    } else {
        y = OSUnMapTbl[(OS_PRIO)(pevent->OSEventGrp >> 8u) & 0xFFu] + 8u;
    }
    ptbl = &pevent->OSEventTbl[y];
    if ((*ptbl & 0xFFu) != 0u) {
        x = OSUnMapTbl[*ptbl & 0xFFu];
    } else {
        x = OSUnMapTbl[(OS_PRIO)(*ptbl >> 8u) & 0xFFu] + 8u;
    }
    prio = (INT8U)((y << 4u) + x);                      /* Find priority of task getting the msg       */
#endif

    
/*@ y == tcb_y_of_prio(curPrio(t)) && x == tcb_x_of_prio(curPrio(t)) && prio == curPrio(t) by local */

/*@ &OSTCBPrioTbl == g_OSTCBPrioTbl(sg) && event_task_rdy_full_entry(sg, tasks, events, eid, e, tid, t, pointers, instances) && store_prio_tbl(sg, prioTbl(tasks))
        which implies &OSTCBPrioTbl == g_OSTCBPrioTbl(sg) && event_task_rdy_full_entry(sg, tasks, events, eid, e, tid, t, pointers, instances) &&
        data_at(pointer_offset(&OSTCBPrioTbl, curPrio(t), OS_TCB *), OS_TCB *, task_slot_addr(sg, tid)) *
        event_task_rdy_prio_frame(sg, tasks, curPrio(t))
    */
ptcb                  =  OSTCBPrioTbl[prio];        /* Point to this task's OS_TCB                 */
    
/*@ ptcb == task_slot_addr(sg, tid) by local */

/*@ &OSTCBPrioTbl == g_OSTCBPrioTbl(sg) && event_task_rdy_full_entry(sg, tasks, events, eid, e, tid, t, pointers, instances) &&
        data_at(pointer_offset(&OSTCBPrioTbl, curPrio(t), OS_TCB *), OS_TCB *, task_slot_addr(sg, tid)) *
        event_task_rdy_prio_frame(sg, tasks, curPrio(t))
        which implies &OSTCBPrioTbl == g_OSTCBPrioTbl(sg) && event_task_rdy_full_entry(sg, tasks, events, eid, e, tid, t, pointers, instances) && store_prio_tbl(sg, prioTbl(tasks))
    */

/*@ tcb_configured_storage_rep(true, true, ptcb, task_layout_image(sg, t))
        which implies data_at(&(ptcb->OSTCBDly), INT32U, dly(t)) *
        data_at(&(ptcb->OSTCBMsg), void *, encode_msg(msg(t))) *
        data_at(&(ptcb->OSTCBStat), INT8U, encode_task_status(stat(t))) *
        data_at(&(ptcb->OSTCBStatPend), INT8U, encode_pend_status(statPend(t))) *
        data_at(&(ptcb->OSTCBY), INT8U, tcb_y_of_prio(curPrio(t))) *
        data_at(&(ptcb->OSTCBBitX), OS_PRIO, tcb_bit_x_of_prio(curPrio(t))) *
        data_at(&(ptcb->OSTCBBitY), OS_PRIO, tcb_bit_y_of_prio(curPrio(t))) *
        data_at(&(ptcb->OSTCBEventPtr), OS_EVENT *, encode_event_link(sg, eventPtr(t))) * event_task_rdy_full_tcb_frame(ptcb, task_layout_image(sg, t))
    */

/*@ &OSRdyTbl == g_OSRdyTbl(sg) && 0 <= tcb_y_of_prio(curPrio(t)) && tcb_y_of_prio(curPrio(t)) < 8 && UCharArray::full(g_OSRdyTbl(sg), 8, rows)
        which implies &OSRdyTbl == g_OSRdyTbl(sg) && 0 <= tcb_y_of_prio(curPrio(t)) && tcb_y_of_prio(curPrio(t)) < 8 &&
        data_at(pointer_offset(&OSRdyTbl, tcb_y_of_prio(curPrio(t)), OS_PRIO), OS_PRIO, Znth(tcb_y_of_prio(curPrio(t)), rows, 0)) *
        UCharArray::missing_i(g_OSRdyTbl(sg), tcb_y_of_prio(curPrio(t)), 0, 8, rows)
    */

/*@ 0 <= group && group < 256 &&
        0 <= Znth(tcb_y_of_prio(curPrio(t)), rows, 0) &&
        Znth(tcb_y_of_prio(curPrio(t)), rows, 0) < 256 by local */
ptcb->OSTCBDly        =  0u;                        /* Prevent OSTimeTick() from readying task     */
#if ((OS_Q_EN > 0u) && (OS_MAX_QS > 0u)) || (OS_MBOX_EN > 0u)
    ptcb->OSTCBMsg        =  pmsg;                      /* Send message directly to waiting task       */
#else
    pmsg                  =  pmsg;                      /* Prevent compiler warning if not used        */
#endif
    ptcb->OSTCBStat      &= (INT8U)~msk;                /* Clear bit associated with event type        */
    ptcb->OSTCBStatPend   =  pend_stat;                 /* Set pend status of post or abort            */
                                                        /* See if task is ready (could be susp'd)      */
    if ((ptcb->OSTCBStat &   OS_STAT_SUSPEND) == OS_STAT_RDY) {
        OSRdyGrp         |=  ptcb->OSTCBBitY;           /* Put task in the ready to run list           */
        OSRdyTbl[y]      |=  ptcb->OSTCBBitX;
        OS_TRACE_TASK_READY(ptcb);
    }

    
/*@ 0 <= tcb_y_of_prio(curPrio(t)) && tcb_y_of_prio(curPrio(t)) < 8 &&
        data_at(&(ptcb->OSTCBY), INT8U, tcb_y_of_prio(curPrio(t))) *
        data_at(&(ptcb->OSTCBBitX), OS_PRIO, tcb_bit_x_of_prio(curPrio(t))) *
        data_at(&(ptcb->OSTCBBitY), OS_PRIO, tcb_bit_y_of_prio(curPrio(t))) *
        data_at(&(ptcb->OSTCBEventPtr), OS_EVENT *, encode_event_link(sg, eventPtr(t))) *
        data_at(&(pevent->OSEventGrp), OS_PRIO, encode_event_wait_grp(waitList(e), tasks)) * data_at(pointer_offset(&(pevent->OSEventTbl), tcb_y_of_prio(curPrio(t)), OS_PRIO), OS_PRIO, encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t))))
        which implies event_task_remove_pre(ptcb, &(pevent->OSEventGrp), &(pevent->OSEventTbl),
          tcb_y_of_prio(curPrio(t)), tcb_bit_x_of_prio(curPrio(t)), tcb_bit_y_of_prio(curPrio(t)), encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t))), encode_event_wait_grp(waitList(e), tasks))
    */
OS_EventTaskRemove(ptcb, pevent)
/*@ where row=tcb_y_of_prio(curPrio(t)), bit_x=tcb_bit_x_of_prio(curPrio(t)), bit_y=tcb_bit_y_of_prio(curPrio(t)),
              row_value=encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t))), group_value=encode_event_wait_grp(waitList(e), tasks) */
;                   /* Remove this task from event   wait list     */

/*@ event_task_remove_post(ptcb, &(pevent->OSEventGrp), &(pevent->OSEventTbl),
          tcb_y_of_prio(curPrio(t)), tcb_bit_x_of_prio(curPrio(t)), tcb_bit_y_of_prio(curPrio(t)), encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t))), encode_event_wait_grp(waitList(e), tasks))
        which implies 0 <= tcb_y_of_prio(curPrio(t)) && tcb_y_of_prio(curPrio(t)) < 8 &&
        data_at(&(ptcb->OSTCBY), INT8U, tcb_y_of_prio(curPrio(t))) *
        data_at(&(ptcb->OSTCBBitX), OS_PRIO, tcb_bit_x_of_prio(curPrio(t))) *
        data_at(&(ptcb->OSTCBBitY), OS_PRIO, tcb_bit_y_of_prio(curPrio(t))) *
        data_at(&(ptcb->OSTCBEventPtr), OS_EVENT *, 0) *
        data_at(&(pevent->OSEventGrp), OS_PRIO, event_task_remove_group(encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t))), encode_event_wait_grp(waitList(e), tasks), tcb_bit_x_of_prio(curPrio(t)), tcb_bit_y_of_prio(curPrio(t)))) *
        data_at(pointer_offset(&(pevent->OSEventTbl), tcb_y_of_prio(curPrio(t)), OS_PRIO), OS_PRIO, event_task_remove_cleared(encode_event_wait_tbl_at_or(waitList(e), tasks, tcb_y_of_prio(curPrio(t))), tcb_bit_x_of_prio(curPrio(t))))
    */

/*@ Assert event_task_rdy_full_after_single(sg, tasks, events, eid, e, tid, t, pointers, instances, pmsg@pre, msk@pre, pend_stat@pre, group, rows) * data_at(&pevent, OS_EVENT *, event_addr(sg, eid)) *
        data_at(&pmsg, void *, pmsg@pre) * data_at(&msk, INT8U, msk@pre) * data_at(&pend_stat, INT8U, pend_stat@pre) *
        data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&y, INT8U, tcb_y_of_prio(curPrio(t))) * data_at(&x, INT8U, tcb_x_of_prio(curPrio(t))) *
        data_at(&prio, INT8U, curPrio(t)) */

/*@ event_task_rdy_full_after_single(sg, tasks, events, eid, e, tid, t, pointers, instances, pmsg@pre, msk@pre, pend_stat@pre, group, rows)
        which implies event_task_rdy_full_entry(sg, tasks, events, eid, e, tid, t, pointers, instances) &&
        event_wait_priority(tasks, e) == curPrio(t) &&
        data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBY), INT8U, tcb_y_of_prio(curPrio(t))) *
        data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBBitX), OS_PRIO, tcb_bit_x_of_prio(curPrio(t))) *
        data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBBitY), OS_PRIO, tcb_bit_y_of_prio(curPrio(t))) *
        data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBEventMultiPtr), OS_EVENT **, tcbEventMultiPtr(t)) *
        data_at(field_addr(task_slot_addr(sg, tid), struct os_tcb, OSTCBEventMultiRdy), OS_EVENT *, encode_event_link(sg, eventMultiRdy(t))) *
        event_task_rdy_full_multi_frame(task_slot_addr(sg, tid), event_task_rdy_full_after_remove_image(sg, t, pmsg@pre, msk@pre, pend_stat@pre)) *
        event_raw_rep(sg, tasks, event_task_rdy_full_after_remove(events, eid, e, tid)) *
        event_task_rdy_full_array(tcbEventMultiPtr(t), pointers) *
        unmap_table_rep(sg) * store_prio_tbl(sg, prioTbl(tasks)) * event_task_rdy_full_ready(sg, t, msk@pre, group, rows)
    */
#if (OS_EVENT_MULTI_EN > 0u)
    if (ptcb->OSTCBEventMultiPtr != (OS_EVENT **)0) {   /* Remove this task from events' wait lists    */
        
/*@ event_task_rdy_full_entry(sg, tasks, events, eid, e, tid, t, pointers, instances) && tcbEventMultiPtr(t) != 0 &&
          event_task_rdy_full_array(tcbEventMultiPtr(t), pointers) * event_raw_rep(sg, tasks, event_task_rdy_full_after_remove(events, eid, e, tid))
          which implies event_task_remove_multi_input(sg, tasks, event_task_rdy_full_after_remove(events, eid, e, tid), tid, t, pointers, instances) &&
          event_multi_array_rep(tcbEventMultiPtr(t), pointers) * event_raw_rep(sg, tasks, event_task_rdy_full_after_remove(events, eid, e, tid)) */
OS_EventTaskRemoveMulti(ptcb, ptcb->OSTCBEventMultiPtr)
/*@ where sg=sg, tasks=tasks, entry=event_task_rdy_full_after_remove(events, eid, e, tid), tid=tid, t=t,
                  pointers=pointers, instances=instances, frame=event_task_rdy_full_ready(sg, t, msk@pre, group, rows) */
;
        
/*@ event_task_remove_multi_post(sg, tasks, event_task_rdy_full_after_remove(events, eid, e, tid), tid, t, pointers, instances, ptcb, tcbEventMultiPtr(t))
            which implies data_at(&(ptcb->OSTCBY), INT8U, tcb_y_of_prio(curPrio(t))) *
              data_at(&(ptcb->OSTCBBitX), OS_PRIO, tcb_bit_x_of_prio(curPrio(t))) *
              data_at(&(ptcb->OSTCBBitY), OS_PRIO, tcb_bit_y_of_prio(curPrio(t))) *
              event_multi_array_rep(tcbEventMultiPtr(t), pointers) *
              event_raw_rep(sg, tasks, event_task_remove_multi_events(event_task_rdy_full_after_remove(events, eid, e, tid), tid, instances)) */
ptcb->OSTCBEventMultiPtr  = (OS_EVENT **)0;     /* No longer pending on multi list             */
        ptcb->OSTCBEventMultiRdy  = (OS_EVENT  *)pevent;/* Return event as first multi-pend event ready*/
    }
#endif

    
/*@ Assert event_task_rdy_full_post(sg, tasks, events, eid, e, tid, t, pointers, instances, pmsg@pre, msk@pre, pend_stat@pre, group, rows, curPrio(t)) * data_at(&pevent, OS_EVENT *, event_addr(sg, eid)) *
        data_at(&pmsg, void *, pmsg@pre) * data_at(&msk, INT8U, msk@pre) * data_at(&pend_stat, INT8U, pend_stat@pre) *
        data_at(&ptcb, OS_TCB *, task_slot_addr(sg, tid)) *
        data_at(&y, INT8U, tcb_y_of_prio(curPrio(t))) * data_at(&x, INT8U, tcb_x_of_prio(curPrio(t))) *
        data_at(&prio, INT8U, curPrio(t)) */
return (prio);
}
