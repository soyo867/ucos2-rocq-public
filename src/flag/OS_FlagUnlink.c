/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OS_FlagUnlink (OS_FLAG_NODE *pnode)
/*@ With (sg : StableGlobVars) (flags : GlobFlagState) (p : Z)
         (w : FlagWaiterState) (t : TaskAbstractState) (F : Assertion)
    Require pnode == p && flag_unlink_pre(sg, flags, p, w, t) * F
    Ensure flag_unlink_post(sg, flags, p, w, t) * F
*/
{
#if OS_TASK_DEL_EN > 0u
    OS_TCB       *ptcb;
#endif
    OS_FLAG_GRP  *pgrp;
    OS_FLAG_NODE *pnode_prev;
    OS_FLAG_NODE *pnode_next;


    /*@ flag_unlink_pre(sg, flags, p, w, t) * data_at(&pnode, OS_FLAG_NODE *, p)
        which implies
        exists post, flag_unlink_context(sg, flags, p, w, t, post) &&
        data_at(&pnode, OS_FLAG_NODE *, p) *
        data_at(&(pnode->OSFlagNodeNext), void *, flag_unlink_next(w)) *
        data_at(&(pnode->OSFlagNodePrev), void *, flag_unlink_prev(w)) *
        data_at(&(pnode->OSFlagNodeTCB), void *, flag_unlink_tcb_addr(w)) *
        data_at(&(pnode->OSFlagNodeFlagGrp), void *, flag_unlink_group_addr(w)) *
        flag_unlink_read_frame(sg, flags, p, w) * flag_unlink_task_rep(sg, w, t)
    */
    /*@ Given post */
    pnode_prev = (OS_FLAG_NODE *)pnode->OSFlagNodePrev;
    pnode_next = (OS_FLAG_NODE *)pnode->OSFlagNodeNext;
    if (pnode_prev == (OS_FLAG_NODE *)0) {                      /* Is it first node in wait list?      */
        pgrp                 = (OS_FLAG_GRP *)pnode->OSFlagNodeFlagGrp;
        /*@ flag_unlink_context(sg, flags, p, w, t, post) &&
            data_at(&pnode, OS_FLAG_NODE *, p) *
            data_at(&(pnode->OSFlagNodeNext), void *, flag_unlink_next(w)) *
            data_at(&(pnode->OSFlagNodePrev), void *, flag_unlink_prev(w)) *
            data_at(&(pnode->OSFlagNodeTCB), void *, flag_unlink_tcb_addr(w)) *
            data_at(&(pnode->OSFlagNodeFlagGrp), void *, flag_unlink_group_addr(w)) *
            flag_unlink_read_frame(sg, flags, p, w)
            which implies
            flag_unlink_context(sg, flags, p, w, t, post) &&
            data_at(&pnode, OS_FLAG_NODE *, p) * flag_raw_rep(sg, flags)
        */
        /*@ flag_unlink_context(sg, flags, p, w, t, post) && flag_unlink_prev(w) == 0 &&
            data_at(&pgrp, OS_FLAG_GRP *, flag_unlink_group_addr(w)) * flag_raw_rep(sg, flags)
            which implies
            exists image, flag_unlink_context(sg, flags, p, w, t, post) && flag_unlink_prev(w) == 0 &&
            flag_unlink_group_lookup(flags, w, image) &&
            data_at(&pgrp, OS_FLAG_GRP *, flag_unlink_group_addr(w)) *
            data_at(&(pgrp->OSFlagWaitList), void *, p) * flag_unlink_head_store_frame(sg, flags, w, image)
        */
        /*@ Given image */
        pgrp->OSFlagWaitList = (void *)pnode_next;              /*      Update list for new 1st node   */
        /*@ flag_unlink_context(sg, flags, p, w, t, post) && flag_unlink_prev(w) == 0 &&
            flag_unlink_group_lookup(flags, w, image) &&
            data_at(&pgrp, OS_FLAG_GRP *, flag_unlink_group_addr(w)) *
            data_at(&(pgrp->OSFlagWaitList), void *, flag_unlink_next(w)) * flag_unlink_head_store_frame(sg, flags, w, image)
            which implies
            flag_unlink_context(sg, flags, p, w, t, post) &&
            data_at(&pgrp, OS_FLAG_GRP *, flag_unlink_group_addr(w)) * flag_unlink_after_first_store_rep(sg, flags, post, w)
        */
        if (pnode_next != (OS_FLAG_NODE *)0) {
            /*@ flag_unlink_context(sg, flags, p, w, t, post) && flag_unlink_next(w) != 0 &&
                data_at(&pnode_next, OS_FLAG_NODE *, flag_unlink_next(w)) * flag_unlink_after_first_store_rep(sg, flags, post, w)
                which implies
                exists following, flag_unlink_context(sg, flags, p, w, t, post) && flag_unlink_next(w) != 0 &&
                flag_unlink_next_lookup(flags, w, following) &&
                data_at(&pnode_next, OS_FLAG_NODE *, flag_unlink_next(w)) *
                data_at(&(pnode_next->OSFlagNodePrev), void *, p) * flag_unlink_next_store_frame(sg, flags, post, w, following)
            */
            /*@ Given following */
            pnode_next->OSFlagNodePrev = (OS_FLAG_NODE *)0;     /*      Link new 1st node PREV to NULL */
            /*@ flag_unlink_context(sg, flags, p, w, t, post) && flag_unlink_prev(w) == 0 && flag_unlink_next(w) != 0 &&
                flag_unlink_next_lookup(flags, w, following) &&
                data_at(&pnode_next, OS_FLAG_NODE *, flag_unlink_next(w)) *
                data_at(&(pnode_next->OSFlagNodePrev), void *, 0) * flag_unlink_next_store_frame(sg, flags, post, w, following)
                which implies
                flag_unlink_context(sg, flags, p, w, t, post) &&
                data_at(&pnode_next, OS_FLAG_NODE *, flag_unlink_next(w)) * flag_unlink_loan(sg, w) * flag_raw_rep(sg, post)
            */
        }
        /*@ Assert flag_unlink_context(sg, flags, p, w, t, post) &&
            data_at(&pnode, OS_FLAG_NODE *, p) * data_at(&pnode_prev, OS_FLAG_NODE *, 0) *
            data_at(&pnode_next, OS_FLAG_NODE *, flag_unlink_next(w)) *
            data_at(&pgrp, OS_FLAG_GRP *, flag_unlink_group_addr(w)) * undef_data_at(&ptcb, OS_TCB *) *
            flag_unlink_after_next_store_rep(sg, flags, post, w) * flag_unlink_task_rep(sg, w, t) * F
        */
        /*@ flag_unlink_context(sg, flags, p, w, t, post) && flag_unlink_after_next_store_rep(sg, flags, post, w)
            which implies
            flag_unlink_context(sg, flags, p, w, t, post) && flag_unlink_loan(sg, w) * flag_raw_rep(sg, post)
        */
    } else {                                                    /* No,  A node somewhere in the list   */
        /*@ flag_unlink_context(sg, flags, p, w, t, post) &&
            data_at(&pnode, OS_FLAG_NODE *, p) *
            data_at(&(pnode->OSFlagNodeNext), void *, flag_unlink_next(w)) *
            data_at(&(pnode->OSFlagNodePrev), void *, flag_unlink_prev(w)) *
            data_at(&(pnode->OSFlagNodeTCB), void *, flag_unlink_tcb_addr(w)) *
            data_at(&(pnode->OSFlagNodeFlagGrp), void *, flag_unlink_group_addr(w)) *
            flag_unlink_read_frame(sg, flags, p, w)
            which implies
            flag_unlink_context(sg, flags, p, w, t, post) &&
            data_at(&pnode, OS_FLAG_NODE *, p) * flag_raw_rep(sg, flags)
        */
        /*@ flag_unlink_context(sg, flags, p, w, t, post) && flag_unlink_prev(w) != 0 &&
            data_at(&pnode_prev, OS_FLAG_NODE *, flag_unlink_prev(w)) * flag_raw_rep(sg, flags)
            which implies
            exists previous, flag_unlink_context(sg, flags, p, w, t, post) && flag_unlink_prev(w) != 0 &&
            flag_unlink_prev_lookup(flags, w, previous) &&
            data_at(&pnode_prev, OS_FLAG_NODE *, flag_unlink_prev(w)) *
            data_at(&(pnode_prev->OSFlagNodeNext), void *, p) * flag_unlink_prev_store_frame(sg, flags, w, previous)
        */
        /*@ Given previous */
        pnode_prev->OSFlagNodeNext = pnode_next;                /*      Link around the node to unlink */
        /*@ flag_unlink_context(sg, flags, p, w, t, post) && flag_unlink_prev(w) != 0 &&
            flag_unlink_prev_lookup(flags, w, previous) &&
            data_at(&pnode_prev, OS_FLAG_NODE *, flag_unlink_prev(w)) *
            data_at(&(pnode_prev->OSFlagNodeNext), void *, flag_unlink_next(w)) * flag_unlink_prev_store_frame(sg, flags, w, previous)
            which implies
            flag_unlink_context(sg, flags, p, w, t, post) &&
            data_at(&pnode_prev, OS_FLAG_NODE *, flag_unlink_prev(w)) * flag_unlink_after_first_store_rep(sg, flags, post, w)
        */
        if (pnode_next != (OS_FLAG_NODE *)0) {                  /*      Was this the LAST node?        */
            /*@ flag_unlink_context(sg, flags, p, w, t, post) && flag_unlink_next(w) != 0 &&
                data_at(&pnode_next, OS_FLAG_NODE *, flag_unlink_next(w)) * flag_unlink_after_first_store_rep(sg, flags, post, w)
                which implies
                exists following, flag_unlink_context(sg, flags, p, w, t, post) && flag_unlink_next(w) != 0 &&
                flag_unlink_next_lookup(flags, w, following) &&
                data_at(&pnode_next, OS_FLAG_NODE *, flag_unlink_next(w)) *
                data_at(&(pnode_next->OSFlagNodePrev), void *, p) * flag_unlink_next_store_frame(sg, flags, post, w, following)
            */
            /*@ Given following */
            pnode_next->OSFlagNodePrev = pnode_prev;            /*      No, Link around current node   */
            /*@ flag_unlink_context(sg, flags, p, w, t, post) && flag_unlink_next(w) != 0 &&
                flag_unlink_next_lookup(flags, w, following) &&
                data_at(&pnode_next, OS_FLAG_NODE *, flag_unlink_next(w)) *
                data_at(&(pnode_next->OSFlagNodePrev), void *, flag_unlink_prev(w)) * flag_unlink_next_store_frame(sg, flags, post, w, following)
                which implies
                flag_unlink_context(sg, flags, p, w, t, post) &&
                data_at(&pnode_next, OS_FLAG_NODE *, flag_unlink_next(w)) * flag_unlink_loan(sg, w) * flag_raw_rep(sg, post)
            */
        }
        /*@ Assert flag_unlink_context(sg, flags, p, w, t, post) &&
            data_at(&pnode, OS_FLAG_NODE *, p) * data_at(&pnode_prev, OS_FLAG_NODE *, flag_unlink_prev(w)) *
            data_at(&pnode_next, OS_FLAG_NODE *, flag_unlink_next(w)) * undef_data_at(&pgrp, OS_FLAG_GRP *) *
            undef_data_at(&ptcb, OS_TCB *) * flag_unlink_after_next_store_rep(sg, flags, post, w) *
            flag_unlink_task_rep(sg, w, t) * F
        */
        /*@ flag_unlink_context(sg, flags, p, w, t, post) && flag_unlink_after_next_store_rep(sg, flags, post, w)
            which implies
            flag_unlink_context(sg, flags, p, w, t, post) && flag_unlink_loan(sg, w) * flag_raw_rep(sg, post)
        */
    }
#if OS_TASK_DEL_EN > 0u
    /*@ flag_unlink_context(sg, flags, p, w, t, post) &&
        data_at(&pnode, OS_FLAG_NODE *, p) * flag_unlink_loan(sg, w)
        which implies
        flag_unlink_context(sg, flags, p, w, t, post) &&
        data_at(&pnode, OS_FLAG_NODE *, p) *
        data_at(&(pnode->OSFlagNodeTCB), void *, flag_unlink_tcb_addr(w)) * flag_unlink_node_without_tcb(sg, p, w)
    */
    ptcb                = (OS_TCB *)pnode->OSFlagNodeTCB;
    /*@ flag_unlink_context(sg, flags, p, w, t, post) &&
        data_at(&pnode, OS_FLAG_NODE *, p) *
        data_at(&(pnode->OSFlagNodeTCB), void *, flag_unlink_tcb_addr(w)) * flag_unlink_node_without_tcb(sg, p, w)
        which implies
        flag_unlink_context(sg, flags, p, w, t, post) &&
        data_at(&pnode, OS_FLAG_NODE *, p) * flag_unlink_loan(sg, w)
    */
    /*@ flag_unlink_context(sg, flags, p, w, t, post) &&
        data_at(&ptcb, OS_TCB *, flag_unlink_tcb_addr(w)) * flag_unlink_task_rep(sg, w, t)
        which implies
        flag_unlink_context(sg, flags, p, w, t, post) &&
        data_at(&ptcb, OS_TCB *, flag_unlink_tcb_addr(w)) *
        data_at(&(ptcb->OSTCBFlagNode), OS_FLAG_NODE *, p) * flag_unlink_task_without_node(sg, w, t)
    */
    ptcb->OSTCBFlagNode = (OS_FLAG_NODE *)0;
    /*@ flag_unlink_context(sg, flags, p, w, t, post) &&
        data_at(&ptcb, OS_TCB *, flag_unlink_tcb_addr(w)) *
        data_at(&(ptcb->OSTCBFlagNode), OS_FLAG_NODE *, 0) * flag_unlink_task_without_node(sg, w, t)
        which implies
        flag_unlink_context(sg, flags, p, w, t, post) &&
        data_at(&ptcb, OS_TCB *, flag_unlink_tcb_addr(w)) * flag_unlink_task_rep(sg, w, task_set_flag_node(t, 0))
    */
#endif
    /*@ flag_unlink_context(sg, flags, p, w, t, post) &&
        flag_raw_rep(sg, post) * flag_unlink_loan(sg, w) * flag_unlink_task_rep(sg, w, task_set_flag_node(t, 0))
        which implies flag_unlink_post(sg, flags, p, w, t)
    */
}
