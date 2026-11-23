/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

static  void  OS_FlagBlock (OS_FLAG_GRP  *pgrp,
                            OS_FLAG_NODE *pnode,
                            OS_FLAGS      flags,
                            INT8U         wait_type,
                            INT32U        timeout)
/*@ With (sg : StableGlobVars) (s : UCOS2_Verify_State)
         (w : FlagWaiterState) (t : TaskAbstractState) (g : FlagGroupState)
         (v : FlagGroupImage) (delay : Z) (F : Assertion)
    Require pgrp == flag_block_call_group(sg,w) && pnode == flag_block_call_node(w) &&
            flags == flag_block_call_mask(w) && wait_type == flag_block_call_mode(w) &&
            timeout == delay && &OSTCBCur == g_OSTCBCur(sg) && OSRdyTbl == g_OSRdyTbl(sg) && &OSRdyGrp == g_OSRdyGrp(sg) &&
            flag_block_call_fields_pre(sg,s,w,t,g,v,delay) * F
    Ensure flag_block_call_fields_post(sg,s,w,t,delay) * F
*/
{
    OS_FLAG_NODE  *pnode_next;
    INT8U          y;

    /*@ &OSTCBCur == g_OSTCBCur(sg) && OSRdyTbl == g_OSRdyTbl(sg) && &OSRdyGrp == g_OSRdyGrp(sg) &&
        flag_block_call_fields_pre(sg,s,w,t,g,v,delay) *
        data_at(&pgrp, OS_FLAG_GRP *, flag_block_call_group(sg,w)) *
        data_at(&pnode, OS_FLAG_NODE *, flag_block_call_node(w)) *
        data_at(&flags, OS_FLAGS, flag_block_call_mask(w)) *
        data_at(&wait_type, INT8U, flag_block_call_mode(w)) *
        data_at(&timeout, INT32U, delay)
        which implies
        flag_block_call_context(sg,s,w,t,g,v,delay) && flag_block_call_ranges(s,t) &&
        &OSTCBCur == g_OSTCBCur(sg) && OSRdyTbl == g_OSRdyTbl(sg) && &OSRdyGrp == g_OSRdyGrp(sg) &&
        data_at(&pgrp, OS_FLAG_GRP *, flag_block_call_group(sg,w)) *
        data_at(&pnode, OS_FLAG_NODE *, flag_block_call_node(w)) *
        data_at(&flags, OS_FLAGS, flag_block_call_mask(w)) *
        data_at(&wait_type, INT8U, flag_block_call_mode(w)) *
        data_at(&timeout, INT32U, delay) *
        data_at(&OSTCBCur, OS_TCB *, flag_block_call_tcb(sg,w)) *
        data_at(field_addr(flag_block_call_tcb(sg,w), OS_TCB, OSTCBStat), INT8U, flag_block_call_status(t)) *
        data_at(field_addr(flag_block_call_tcb(sg,w), OS_TCB, OSTCBStatPend), INT8U, flag_block_call_pend(t)) *
        data_at(field_addr(flag_block_call_tcb(sg,w), OS_TCB, OSTCBDly), INT32U, flag_block_call_delay(t)) *
        data_at(field_addr(flag_block_call_tcb(sg,w), OS_TCB, OSTCBFlagNode), OS_FLAG_NODE *, 0) *
        data_at(field_addr(flag_block_call_tcb(sg,w), OS_TCB, OSTCBY), INT8U, flag_block_call_y(t)) *
        data_at(field_addr(flag_block_call_tcb(sg,w), OS_TCB, OSTCBBitX), INT8U, flag_block_call_bit_x(t)) *
        data_at(field_addr(flag_block_call_tcb(sg,w), OS_TCB, OSTCBBitY), INT8U, flag_block_call_bit_y(t)) *
        undef_data_at(field_addr(flag_block_call_node(w), OS_FLAG_NODE, OSFlagNodeFlags), OS_FLAGS) *
        undef_data_at(field_addr(flag_block_call_node(w), OS_FLAG_NODE, OSFlagNodeWaitType), INT8U) *
        undef_data_at(field_addr(flag_block_call_node(w), OS_FLAG_NODE, OSFlagNodeTCB), void *) *
        undef_data_at(field_addr(flag_block_call_node(w), OS_FLAG_NODE, OSFlagNodeNext), void *) *
        undef_data_at(field_addr(flag_block_call_node(w), OS_FLAG_NODE, OSFlagNodePrev), void *) *
        undef_data_at(field_addr(flag_block_call_node(w), OS_FLAG_NODE, OSFlagNodeFlagGrp), void *) *
        data_at(field_addr(flag_block_call_group(sg,w), OS_FLAG_GRP, OSFlagWaitList), void *, flag_block_call_head(v)) *
        data_at(pointer_offset(&OSRdyTbl, flag_block_call_y(t), unsigned char), INT8U, flag_block_call_row(s,t)) *
        data_at(&OSRdyGrp, INT8U, flag_block_call_grp(s)) *
        flag_block_call_fields_nodes(sg,s) *
        flag_block_call_residual(sg,s,w,t,v)
    */

    OSTCBCur->OSTCBStat      |= OS_STAT_FLAG;
    OSTCBCur->OSTCBStatPend   = OS_STAT_PEND_OK;
    OSTCBCur->OSTCBDly        = timeout;              /* Store timeout in task's TCB                   */
#if OS_TASK_DEL_EN > 0u
    OSTCBCur->OSTCBFlagNode   = pnode;                /* TCB to link to node                           */
#endif
    pnode->OSFlagNodeFlags    = flags;                /* Save the flags that we need to wait for       */
    pnode->OSFlagNodeWaitType = wait_type;            /* Save the type of wait we are doing            */
    pnode->OSFlagNodeTCB      = (void *)OSTCBCur;     /* Link to task's TCB                            */
    pnode->OSFlagNodeNext     = pgrp->OSFlagWaitList; /* Add node at beginning of event flag wait list */
    pnode->OSFlagNodePrev     = (void *)0;
    pnode->OSFlagNodeFlagGrp  = (void *)pgrp;         /* Link to Event Flag Group                      */
    pnode_next                = (OS_FLAG_NODE *)pgrp->OSFlagWaitList;
    if (pnode_next != (void *)0) {                    /* Is this the first NODE to insert?             */
        /*@ flag_block_call_context(sg,s,w,t,g,v,delay) && flag_block_call_head(v) != 0 &&
            flag_block_call_fields_nodes(sg,s)
            which implies
            exists previous, flag_block_call_context(sg,s,w,t,g,v,delay) &&
            flag_block_call_head(v) != 0 && flag_block_call_head_lookup(s,v,previous) &&
            undef_data_at(field_addr(flag_block_call_head(v), OS_FLAG_NODE, OSFlagNodePrev), void *) *
            flag_block_call_fields_head_frame(sg,s,v,previous)
        */
        /*@ Given previous */
        pnode_next->OSFlagNodePrev = pnode;           /* No, link in doubly linked list                */
        /*@ flag_block_call_context(sg,s,w,t,g,v,delay) && flag_block_call_head(v) != 0 &&
            flag_block_call_head_lookup(s,v,previous) &&
            data_at(field_addr(flag_block_call_head(v), OS_FLAG_NODE, OSFlagNodePrev), void *, flag_block_call_node(w)) *
            flag_block_call_fields_head_frame(sg,s,v,previous)
            which implies
            flag_block_call_context(sg,s,w,t,g,v,delay) && flag_block_call_fields_old_nodes(sg,s,w,v)
        */
    }
    pgrp->OSFlagWaitList = (void *)pnode;

    /*@ Assert flag_block_call_context(sg,s,w,t,g,v,delay) && flag_block_call_ranges(s,t) &&
        &OSTCBCur == g_OSTCBCur(sg) && OSRdyTbl == g_OSRdyTbl(sg) && &OSRdyGrp == g_OSRdyGrp(sg) &&
        data_at(&pgrp, OS_FLAG_GRP *, flag_block_call_group(sg,w)) *
        data_at(&pnode, OS_FLAG_NODE *, flag_block_call_node(w)) *
        data_at(&flags, OS_FLAGS, flag_block_call_mask(w)) *
        data_at(&wait_type, INT8U, flag_block_call_mode(w)) *
        data_at(&timeout, INT32U, delay) *
        data_at(&pnode_next, OS_FLAG_NODE *, flag_block_call_head(v)) * undef_data_at(&y, INT8U) *
        flag_block_call_fields_ready_stage(sg,s,w,t,v,delay) * F
    */
    /*@ &OSTCBCur == g_OSTCBCur(sg) && OSRdyTbl == g_OSRdyTbl(sg) && &OSRdyGrp == g_OSRdyGrp(sg) &&
        flag_block_call_fields_ready_stage(sg,s,w,t,v,delay)
        which implies
        &OSTCBCur == g_OSTCBCur(sg) && OSRdyTbl == g_OSRdyTbl(sg) && &OSRdyGrp == g_OSRdyGrp(sg) &&
        data_at(&OSTCBCur, OS_TCB *, flag_block_call_tcb(sg,w)) *
        data_at(field_addr(flag_block_call_tcb(sg,w), OS_TCB, OSTCBY), INT8U, flag_block_call_y(t)) *
        data_at(field_addr(flag_block_call_tcb(sg,w), OS_TCB, OSTCBBitX), INT8U, flag_block_call_bit_x(t)) *
        data_at(field_addr(flag_block_call_tcb(sg,w), OS_TCB, OSTCBBitY), INT8U, flag_block_call_bit_y(t)) *
        data_at(pointer_offset(&OSRdyTbl, flag_block_call_y(t), unsigned char), INT8U, flag_block_call_row(s,t)) *
        data_at(&OSRdyGrp, INT8U, flag_block_call_grp(s)) *
        flag_block_call_fields_ready_frame(sg,s,w,t,v,delay)
    */

    y            =  OSTCBCur->OSTCBY;                 /* Suspend current task until flag(s) received   */
    OSRdyTbl[y] &= (OS_PRIO)~OSTCBCur->OSTCBBitX;
    OS_TRACE_TASK_SUSPENDED(OSTCBCur);
    if (OSRdyTbl[y] == 0x00u) {
        OSRdyGrp &= (OS_PRIO)~OSTCBCur->OSTCBBitY;
    }
    /*@ Assert flag_block_call_context(sg,s,w,t,g,v,delay) && flag_block_call_ranges(s,t) &&
        data_at(&pgrp, OS_FLAG_GRP *, flag_block_call_group(sg,w)) *
        data_at(&pnode, OS_FLAG_NODE *, flag_block_call_node(w)) *
        data_at(&flags, OS_FLAGS, flag_block_call_mask(w)) *
        data_at(&wait_type, INT8U, flag_block_call_mode(w)) *
        data_at(&timeout, INT32U, delay) *
        data_at(&pnode_next, OS_FLAG_NODE *, flag_block_call_head(v)) * data_at(&y, INT8U, flag_block_call_y(t)) *
        flag_block_call_fields_written(sg,s,w,t,v,delay) * F
    */
    /*@ flag_block_call_context(sg,s,w,t,g,v,delay) &&
        flag_block_call_fields_written(sg,s,w,t,v,delay)
        which implies flag_block_call_fields_post(sg,s,w,t,delay)
    */
}
