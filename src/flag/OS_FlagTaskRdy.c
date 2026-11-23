/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

static  BOOLEAN  OS_FlagTaskRdy (OS_FLAG_NODE *pnode,
                                 OS_FLAGS      flags_rdy,
                                 INT8U         pend_stat)
/*@ With (sg : StableGlobVars) (s : UCOS2_Verify_State) (p : Z)
         (w : FlagWaiterState) (old : TaskAbstractState) (bits : Z)
         (result : PendStatus) (F : Assertion)
    Require pnode == p && flags_rdy == bits && pend_stat == encode_pend_status(result) &&
            &OSRdyGrp == g_OSRdyGrp(sg) && &OSRdyTbl == g_OSRdyTbl(sg) &&
            flag_task_rdy_pre(sg, s, p, w, old, bits) * F
    Ensure flag_task_rdy_post(sg, s, p, w, bits, result, __return) * F
*/
{
    OS_TCB   *ptcb;
    BOOLEAN   sched;


    /*@ flag_task_rdy_pre(sg, s, p, w, old, bits)
        which implies flag_task_rdy_domain(sg, s, p, w, old, bits) &&
        flag_raw_rep(sg, FlagState(s)) * flag_unlink_task_rep(sg, w, old) *
        task_public_storage_without_task(sg, TskState(s), flagTask(w)) *
        sched_raw_rep(sg, TskState(s), SchedState(s))
    */
    /*@ flag_task_rdy_domain(sg, s, p, w, old, bits) &&
        data_at(&pnode, OS_FLAG_NODE *, p) * flag_raw_rep(sg, FlagState(s))
        which implies flag_task_rdy_domain(sg, s, p, w, old, bits) &&
        data_at(&pnode, OS_FLAG_NODE *, p) *
        data_at(&(pnode->OSFlagNodeTCB), void *, flag_unlink_tcb_addr(w)) *
        flag_task_rdy_node_frame(sg, FlagState(s), p, w)
    */
    ptcb                 = (OS_TCB *)pnode->OSFlagNodeTCB; /* Point to TCB of waiting task             */
    /*@ flag_task_rdy_domain(sg, s, p, w, old, bits) &&
        data_at(&pnode, OS_FLAG_NODE *, p) *
        data_at(&(pnode->OSFlagNodeTCB), void *, flag_unlink_tcb_addr(w)) *
        flag_task_rdy_node_frame(sg, FlagState(s), p, w)
        which implies flag_task_rdy_domain(sg, s, p, w, old, bits) &&
        data_at(&pnode, OS_FLAG_NODE *, p) * flag_raw_rep(sg, FlagState(s))
    */
    /*@ flag_task_rdy_domain(sg, s, p, w, old, bits) &&
        data_at(&ptcb, OS_TCB *, flag_unlink_tcb_addr(w)) * flag_unlink_task_rep(sg, w, old)
        which implies flag_task_rdy_domain(sg, s, p, w, old, bits) &&
        0 <= tcb_y_of_prio(curPrio(old)) && tcb_y_of_prio(curPrio(old)) < 8 &&
        data_at(&ptcb, OS_TCB *, flag_unlink_tcb_addr(w)) *
        data_at(&(ptcb->OSTCBDly), INT32U, dly(old)) *
        data_at(&(ptcb->OSTCBFlagsRdy), OS_FLAGS, tcbFlagsRdy(old)) *
        data_at(&(ptcb->OSTCBStat), INT8U, encode_task_status(stat(old))) *
        data_at(&(ptcb->OSTCBStatPend), INT8U, encode_pend_status(statPend(old))) *
        data_at(&(ptcb->OSTCBY), INT8U, tcb_y_of_prio(curPrio(old))) *
        data_at(&(ptcb->OSTCBBitX), OS_PRIO, tcb_bit_x_of_prio(curPrio(old))) *
        data_at(&(ptcb->OSTCBBitY), OS_PRIO, tcb_bit_y_of_prio(curPrio(old))) *
        flag_task_rdy_tcb_frame(flag_unlink_tcb_addr(w), task_tcb64_image(sg, old))
    */
    ptcb->OSTCBDly       = 0u;
    ptcb->OSTCBFlagsRdy  = flags_rdy;
    ptcb->OSTCBStat     &= (INT8U)~(INT8U)OS_STAT_FLAG;
    ptcb->OSTCBStatPend  = pend_stat;
    /*@ ptcb->OSTCBStat == flag_task_rdy_status(old) by local */
    if (ptcb->OSTCBStat == OS_STAT_RDY) {                  /* Task now ready?                          */
        /*@ flag_task_rdy_domain(sg, s, p, w, old, bits) && &OSRdyGrp == g_OSRdyGrp(sg) &&
            &OSRdyTbl == g_OSRdyTbl(sg) && sched_raw_rep(sg, TskState(s), SchedState(s))
            which implies flag_task_rdy_domain(sg, s, p, w, old, bits) && &OSRdyGrp == g_OSRdyGrp(sg) &&
            &OSRdyTbl == g_OSRdyTbl(sg) &&
            data_at(&OSRdyGrp, OS_PRIO, flag_task_rdy_ready_group(s)) *
            data_at(pointer_offset(&OSRdyTbl, tcb_y_of_prio(curPrio(old)), OS_PRIO),
                    OS_PRIO, flag_task_rdy_ready_row(s, old)) *
            flag_task_rdy_ready_frame(sg, s, old)
        */
        /*@ 0 <= flag_task_rdy_ready_group(s) && flag_task_rdy_ready_group(s) < 256 &&
            0 <= flag_task_rdy_ready_row(s, old) && flag_task_rdy_ready_row(s, old) < 256 by local */
        OSRdyGrp               |= ptcb->OSTCBBitY;         /* Put task into ready list                 */
        OSRdyTbl[ptcb->OSTCBY] |= ptcb->OSTCBBitX;
        OS_TRACE_TASK_READY(ptcb);
        sched                   = OS_TRUE;
        /*@ flag_task_rdy_domain(sg, s, p, w, old, bits) && flag_task_rdy_status(old) == 0 &&
            &OSRdyGrp == g_OSRdyGrp(sg) && &OSRdyTbl == g_OSRdyTbl(sg) &&
            data_at(&OSRdyGrp, OS_PRIO, flag_task_rdy_ready_group(s) | tcb_bit_y_of_prio(curPrio(old))) *
            data_at(pointer_offset(&OSRdyTbl, tcb_y_of_prio(curPrio(old)), OS_PRIO),
                    OS_PRIO, flag_task_rdy_ready_row(s, old) | tcb_bit_x_of_prio(curPrio(old))) *
            flag_task_rdy_ready_frame(sg, s, old)
            which implies flag_task_rdy_domain(sg, s, p, w, old, bits) && flag_task_rdy_status(old) == 0 &&
            sched_raw_rep(sg, flag_task_rdy_after_tasks(s, w, old, bits, result), flag_task_rdy_after_sched(sg, s, w, old, bits, result))
        */
    } else {
        sched                   = OS_FALSE;
        /*@ flag_task_rdy_domain(sg, s, p, w, old, bits) && flag_task_rdy_status(old) != 0 &&
            sched_raw_rep(sg, TskState(s), SchedState(s))
            which implies flag_task_rdy_domain(sg, s, p, w, old, bits) && flag_task_rdy_status(old) != 0 &&
            sched_raw_rep(sg, flag_task_rdy_after_tasks(s, w, old, bits, result), flag_task_rdy_after_sched(sg, s, w, old, bits, result))
        */
    }
    /*@ Assert flag_task_rdy_domain(sg, s, p, w, old, bits) && sched == flag_task_rdy_return(old) &&
        data_at(&pnode, OS_FLAG_NODE *, p) *
        data_at(&flags_rdy, OS_FLAGS, bits) *
        data_at(&pend_stat, INT8U, encode_pend_status(result)) *
        data_at(&ptcb, OS_TCB *, flag_unlink_tcb_addr(w)) *
        data_at(&(ptcb->OSTCBDly), INT32U, 0) *
        data_at(&(ptcb->OSTCBFlagsRdy), OS_FLAGS, bits) *
        data_at(&(ptcb->OSTCBStat), INT8U, flag_task_rdy_status(old)) *
        data_at(&(ptcb->OSTCBStatPend), INT8U, encode_pend_status(result)) *
        data_at(&(ptcb->OSTCBY), INT8U, tcb_y_of_prio(curPrio(old))) *
        data_at(&(ptcb->OSTCBBitX), OS_PRIO, tcb_bit_x_of_prio(curPrio(old))) *
        data_at(&(ptcb->OSTCBBitY), OS_PRIO, tcb_bit_y_of_prio(curPrio(old))) *
        flag_task_rdy_tcb_frame(flag_unlink_tcb_addr(w), task_tcb64_image(sg, old)) *
        flag_raw_rep(sg, FlagState(s)) *
        task_public_storage_without_task(sg, TskState(s), flagTask(w)) *
        sched_raw_rep(sg, flag_task_rdy_after_tasks(s, w, old, bits, result), flag_task_rdy_after_sched(sg, s, w, old, bits, result)) * F
    */
    /*@ flag_task_rdy_domain(sg, s, p, w, old, bits) && data_at(&ptcb, OS_TCB *, flag_unlink_tcb_addr(w)) *
        data_at(&(ptcb->OSTCBDly), INT32U, 0) *
        data_at(&(ptcb->OSTCBFlagsRdy), OS_FLAGS, bits) *
        data_at(&(ptcb->OSTCBStat), INT8U, flag_task_rdy_status(old)) *
        data_at(&(ptcb->OSTCBStatPend), INT8U, encode_pend_status(result)) *
        data_at(&(ptcb->OSTCBY), INT8U, tcb_y_of_prio(curPrio(old))) *
        data_at(&(ptcb->OSTCBBitX), OS_PRIO, tcb_bit_x_of_prio(curPrio(old))) *
        data_at(&(ptcb->OSTCBBitY), OS_PRIO, tcb_bit_y_of_prio(curPrio(old))) *
        flag_task_rdy_tcb_frame(flag_unlink_tcb_addr(w), task_tcb64_image(sg, old))
        which implies flag_task_rdy_domain(sg, s, p, w, old, bits) && data_at(&ptcb, OS_TCB *, flag_unlink_tcb_addr(w)) *
        flag_unlink_task_rep(sg, w, flag_task_rdy_middle(old, bits, result))
    */
    /*@ flag_task_rdy_domain(sg, s, p, w, old, bits) &&
        flag_raw_rep(sg, FlagState(s)) *
        flag_unlink_task_rep(sg, w, flag_task_rdy_middle(old, bits, result))
        which implies flag_task_rdy_domain(sg, s, p, w, old, bits) &&
        flag_unlink_pre(sg, FlagState(s), p, w, flag_task_rdy_middle(old, bits, result))
    */
    /*@ task_public_storage_without_task(sg, TskState(s), flagTask(w)) *
        sched_raw_rep(sg, flag_task_rdy_after_tasks(s, w, old, bits, result), flag_task_rdy_after_sched(sg, s, w, old, bits, result)) * F
        which implies flag_task_rdy_call_frame(sg, s, w, old, bits, result, F)
    */
    OS_FlagUnlink(pnode)
    /*@ where sg=sg, flags=FlagState(s), p=p, w=w,
              t=flag_task_rdy_middle(old, bits, result),
              F=flag_task_rdy_call_frame(sg, s, w, old, bits, result, F) */;
    /*@ flag_task_rdy_domain(sg, s, p, w, old, bits) &&
        flag_unlink_post(sg, FlagState(s), p, w, flag_task_rdy_middle(old, bits, result)) *
        flag_task_rdy_call_frame(sg, s, w, old, bits, result, F)
        which implies flag_task_rdy_post(sg, s, p, w, bits, result, flag_task_rdy_return(old)) * F
    */
    return (sched);
}
