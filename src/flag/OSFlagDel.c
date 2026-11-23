/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

OS_FLAG_GRP  *OSFlagDel (OS_FLAG_GRP  *pgrp,
                         INT8U         opt,
                         INT8U        *perr)
/*@ With (source : FlagDelSourceABI) (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
         (local : Armv7aContinuation -> Assertion) (sg : StableGlobVars)
         (caller : TaskSuspendCaller) (mask : Z) (view : FlagQueryView)
         (before : UCOS2_Verify_State) (observed : FlagGroupImage) (name pointer option error_address : Z)
         (X : (Z * Z) -> UCOS2_Verify_State -> Prop) (LitMap : String -> Z) (F : Assertion)
    Require pgrp == pointer && opt == option && perr == error_address &&
            os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
            flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
            flag_del_argument(sg, pgrp, view, before, observed) &&
            flag_del_safe(environment, critical, sg, caller, mask, view, pgrp, opt, name, before, X) &&
            flag_del_source_public_entry(source, environment, critical, local, sg, caller, mask, before, pgrp, view, perr, F) * GlobalStrings(LitMap)
    Ensure exists (returned : TaskSuspendCaller) (current : UCOS2_Verify_State)
                  (after_local : Armv7aContinuation -> Assertion) (error : Z),
             flag_del_source_return_cut(environment, critical, after_local, sg, caller, returned, mask,
               pointer, view, option, name, before, current, pair(__return, error), X) *
             data_at(error_address, INT8U, error) * GlobalStrings(LitMap) * F
*/

{
    BOOLEAN       tasks_waiting;
    OS_FLAG_NODE *pnode;
    OS_FLAG_GRP  *pgrp_return;
#if OS_CRITICAL_METHOD == 3u                               /* Allocate storage for CPU status register */
    OS_CPU_SR     cpu_sr = 0u;
#endif

    /* The original INT8U parameter supplies this range; it is not an API premise. */
    /*@ 0 <= opt && opt <= 255 by local */

    /*@ flag_del_source_public_entry(source, environment, critical, local, sg, caller, mask, before, pgrp, view, perr, F)
        which implies
        flag_del_source_cut(sg, caller, before) &&
        flag_del_closed(environment, local, sg, caller, mask, before) *
        flag_del_raw_type(pgrp, view) * undef_data_at(perr, INT8U) * F
    */

#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return ((OS_FLAG_GRP *)0);
    }
#endif

#ifdef OS_SAFETY_CRITICAL_IEC61508
    if (OSSafetyCriticalStartFlag == OS_TRUE) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        *perr = OS_ERR_ILLEGAL_DEL_RUN_TIME;
        return ((OS_FLAG_GRP *)0);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pgrp == (OS_FLAG_GRP *)0) {                        /* Validate 'pgrp'                          */
        *perr = OS_ERR_FLAG_INVALID_PGRP;
        /*@ Assert  pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
         flag_del_source_return_cut(environment, critical, local, sg, caller, caller, mask,
              pgrp, view, opt, name, before, before, pair(pgrp, OS_ERR_FLAG_INVALID_PGRP), X) *
              data_at(perr, INT8U, OS_ERR_FLAG_INVALID_PGRP) * GlobalStrings(LitMap) * F *
          undef_data_at(&cpu_sr, OS_CPU_SR) * undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
        return (pgrp);
    }
#endif

    OS_TRACE_FLAG_DEL_ENTER(pgrp, opt);

    /*@ os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        flag_del_closed(environment, local, sg, caller, mask, before)
        which implies
        data_at(&OSIntNesting, INT8U, os_sched_ints(before)) *
        flag_del_nesting_frame(environment, local, sg, caller, mask, before)
    */
    if (OSIntNesting > 0u) {                               /* See if called from ISR ...               */
        *perr = OS_ERR_DEL_ISR;                            /* ... can't DELETE from an ISR             */
        OS_TRACE_FLAG_DEL_EXIT(*perr);
        /*@ Assert  pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
         flag_del_source_return_cut(environment, critical, local, sg, caller, caller, mask,
              pgrp, view, opt, name, before, before, pair(pgrp, OS_ERR_DEL_ISR), X) *
              data_at(perr, INT8U, OS_ERR_DEL_ISR) * GlobalStrings(LitMap) * F *
          undef_data_at(&cpu_sr, OS_CPU_SR) * undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
        return (pgrp);
    }
    /*@ Assert  pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_source_cut(sg, caller, before) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
        flag_del_safe(environment, critical, sg, caller, mask, view, pgrp, opt, name, before, X) &&
        pgrp != 0 && os_sched_ints(before) == 0 &&
        flag_del_type_cut(environment, local, sg, caller, mask, pgrp, view, before, observed) *
        undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&cpu_sr, OS_CPU_SR) * undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
    /*@ pgrp != 0 && flag_del_argument(sg, pgrp, view, before, observed) &&
        flag_del_type_cut(environment, local, sg, caller, mask, pgrp, view, before, observed)
        which implies
        data_at(&(pgrp->OSFlagType), INT8U, flagImageType(observed)) *
        flag_del_type_read_frame(environment, local, sg, caller, mask, pgrp, view, before, observed)
    */
    if (pgrp->OSFlagType != OS_EVENT_TYPE_FLAG) {          /* Validate event group type                */
        *perr = OS_ERR_EVENT_TYPE;
        OS_TRACE_FLAG_DEL_EXIT(*perr);
        /*@ Assert  pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
         flag_del_source_return_cut(environment, critical, local, sg, caller, caller, mask,
              pgrp, view, opt, name, before, before, pair(pgrp, OS_ERR_EVENT_TYPE), X) *
              data_at(perr, INT8U, OS_ERR_EVENT_TYPE) * GlobalStrings(LitMap) * F *
          undef_data_at(&cpu_sr, OS_CPU_SR) * undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
        return (pgrp);
    }
    /*@ Assert  pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
         os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
        flag_del_source_cut(sg, caller, before) && pgrp != 0 && os_sched_ints(before) == 0 &&
        flagImageType(observed) == 5 &&
        flag_del_safe(environment, critical, sg, caller, mask, view, pgrp, opt, name, before, X) &&
        flag_del_closed(environment, local, sg, caller, mask, before) *
        undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&cpu_sr, OS_CPU_SR) * undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
    /*@ flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) && flag_del_source_cut(sg, caller, before) &&
        flag_del_closed(environment, local, sg, caller, mask, before)
        which implies exists (save_heap : model),
        os_sched_active_heap_cut(flag_del_source_save_input(environment, critical, local, sg, caller, mask, before), save_heap)
    */
    /*@ Given save_heap */
    cpu_sr = OS_CPU_SR_Save()/*@ where environment = environment, critical = critical, local = local, sg = sg, caller = caller, mask = mask, before = before, first_heap = save_heap */;
    /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller) (acquired : UCOS2_Verify_State)
                      (id : Z) (image : FlagGroupImage),
 pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
        flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && view == FlagQueryPool(id) && flag_query_selected(view, acquired, image) &&
        flag_del_source_cut(sg, active, acquired) &&
        flag_del_masked_type_cut(environment, critical, protected_local, sg, active, cpu_sr, acquired,
          pgrp, id, acquired, image) * undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */

    /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller) (acquired : UCOS2_Verify_State)
                      (id : Z) (image : FlagGroupImage),
 pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
        flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && view == FlagQueryPool(id) && flag_query_selected(view, acquired, image) &&
        flag_del_source_cut(sg, active, acquired) &&
        data_at(&(pgrp->OSFlagType), INT8U, flagImageType(image)) *
        flag_del_masked_type_frame(environment, critical, protected_local, sg, active, cpu_sr, acquired,
          pgrp, id, acquired, image) * undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
    /* Another task may have deleted this group before interrupts were masked. */
    if (((opt == OS_DEL_NO_PEND) || (opt == OS_DEL_ALWAYS)) &&
        (pgrp->OSFlagType != OS_EVENT_TYPE_FLAG)) {
        /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller) (acquired : UCOS2_Verify_State),
 pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                  os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
          flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) &&
          flag_del_protected_result(sg, view, pgrp, opt, name, acquired,
            pgrp, OS_ERR_EVENT_TYPE, false, acquired) &&
          flag_del_source_cut(sg, active, acquired) &&
          flag_del_masked(environment, critical, protected_local, sg, active, cpu_sr, acquired, acquired) *
          undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
        /*@ Given protected_local active acquired */
/*@ flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) && flag_del_source_restore_cut(sg, active, acquired, false) &&
    flag_del_masked(environment, critical, protected_local, sg, active, cpu_sr, acquired, acquired)
    which implies exists (restore_heap : model), os_sched_active_heap_cut(flag_del_source_restore_input(environment, critical, protected_local, sg, active, cpu_sr, acquired, acquired, false), restore_heap) */
/*@ Given restore_heap */
OS_CPU_SR_Restore(cpu_sr)/*@ where schedule = false, first_heap = restore_heap */;
        /*@ Assert pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
         os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
          flag_del_source_after_restore(environment, critical, sg, caller, mask,
            view, pgrp, opt, name, before, X, pgrp, OS_ERR_EVENT_TYPE, false) *
          undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&cpu_sr, OS_CPU_SR) * undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
        *perr = OS_ERR_EVENT_TYPE;
        OS_TRACE_FLAG_DEL_EXIT(*perr);
        /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (returned : TaskSuspendCaller) (current : UCOS2_Verify_State),
 pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                  flag_del_source_return_cut(environment, critical, protected_local, sg, caller, returned, mask,
            pgrp, view, opt, name, before, current, pair(pgrp, OS_ERR_EVENT_TYPE), X) *
          data_at(perr, INT8U, OS_ERR_EVENT_TYPE) * GlobalStrings(LitMap) * F *
          undef_data_at(&cpu_sr, OS_CPU_SR) * undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
        return (pgrp);
    }
    /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller) (acquired : UCOS2_Verify_State)
                      (id : Z) (image : FlagGroupImage),
 pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
        flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && view == FlagQueryPool(id) && flag_query_selected(view, acquired, image) && flag_del_rechecked(opt, image) &&
        flag_del_source_cut(sg, active, acquired) &&
        flag_del_group_cut(environment, critical, protected_local, sg, active, cpu_sr, acquired,
          pgrp, id, acquired, image) * undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
    /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller) (acquired : UCOS2_Verify_State)
                      (id : Z) (image : FlagGroupImage),
 pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
        flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && view == FlagQueryPool(id) && flag_query_selected(view, acquired, image) && flag_del_rechecked(opt, image) &&
        
        flag_del_source_cut(sg, active, acquired) &&
        data_at(&(pgrp->OSFlagType), INT8U, flagImageType(image)) *
        data_at(&(pgrp->OSFlagWaitList), void *, flagImageHead(image)) *
        data_at(&(pgrp->OSFlagFlags), OS_FLAGS, flagImageBits(image)) *
        data_at(&(pgrp->OSFlagName), INT8U *, flagImageName(image)) *
        data_at(&OSFlagFreeList, OS_FLAG_GRP *, flag_del_free_head_state(sg, acquired)) *
        flag_del_group_frame(environment, critical, protected_local, sg, active, cpu_sr, acquired,
          pgrp, id, acquired, image) * undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) * undef_data_at(&tasks_waiting, BOOLEAN) */
    if (pgrp->OSFlagWaitList != (void *)0) {               /* See if any tasks waiting on event flags  */
        tasks_waiting = OS_TRUE;                           /* Yes                                      */
    } else {
        tasks_waiting = OS_FALSE;                          /* No                                       */
    }
    /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller) (acquired : UCOS2_Verify_State)
                      (id : Z) (image : FlagGroupImage),
 pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
        flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && view == FlagQueryPool(id) && flag_query_selected(view, acquired, image) && flag_del_rechecked(opt, image) &&
        tasks_waiting == flag_del_waiting(image) &&
        flag_del_source_cut(sg, active, acquired) &&
        flag_del_group_cut(environment, critical, protected_local, sg, active, cpu_sr, acquired,
          pgrp, id, acquired, image) * undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
    switch (opt) {
        case OS_DEL_NO_PEND:                               /* Delete group if no task waiting          */
    /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller) (acquired : UCOS2_Verify_State)
                      (id : Z) (image : FlagGroupImage),
 opt == 0 && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
        flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && view == FlagQueryPool(id) && flag_query_selected(view, acquired, image) && flag_del_rechecked(opt, image) &&
        tasks_waiting == flag_del_waiting(image) &&
        flag_del_source_cut(sg, active, acquired) &&
        data_at(&(pgrp->OSFlagType), INT8U, flagImageType(image)) *
        data_at(&(pgrp->OSFlagWaitList), void *, flagImageHead(image)) *
        data_at(&(pgrp->OSFlagFlags), OS_FLAGS, flagImageBits(image)) *
        data_at(&(pgrp->OSFlagName), INT8U *, flagImageName(image)) *
        data_at(&OSFlagFreeList, OS_FLAG_GRP *, flag_del_free_head_state(sg, acquired)) *
        flag_del_group_frame(environment, critical, protected_local, sg, active, cpu_sr, acquired,
          pgrp, id, acquired, image) * undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
             if (tasks_waiting == OS_FALSE) {
#if OS_FLAG_NAME_EN > 0u
                 pgrp->OSFlagName     = (INT8U *)(void *)"?";
#endif
                 pgrp->OSFlagType     = OS_EVENT_TYPE_UNUSED;
                 pgrp->OSFlagWaitList = (void *)OSFlagFreeList; /* Return group to free list           */
                 pgrp->OSFlagFlags    = (OS_FLAGS)0;
                 OSFlagFreeList       = pgrp;
                 /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller) (acquired : UCOS2_Verify_State)
                      (id : Z) (image : FlagGroupImage),
 opt == 0 && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                  os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
          flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && view == FlagQueryPool(id) &&
          flag_del_protected_result(sg, view, pgrp, opt, name, acquired,
            0, OS_ERR_NONE, false, flag_del_release_state(sg, acquired, id, image, name)) &&
          flag_del_source_cut(sg, active, flag_del_release_state(sg, acquired, id, image, name)) &&
          flag_del_masked(environment, critical, protected_local, sg, active, cpu_sr, acquired,
            flag_del_release_state(sg, acquired, id, image, name)) * undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
                 /*@ Given protected_local active acquired id image */
/*@ flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) && flag_del_source_restore_cut(sg, active, flag_del_release_state(sg, acquired, id, image, name), false) &&
    flag_del_masked(environment, critical, protected_local, sg, active, cpu_sr, acquired, flag_del_release_state(sg, acquired, id, image, name))
    which implies exists (restore_heap : model), os_sched_active_heap_cut(flag_del_source_restore_input(environment, critical, protected_local, sg, active, cpu_sr, acquired, flag_del_release_state(sg, acquired, id, image, name), false), restore_heap) */
/*@ Given restore_heap */
OS_CPU_SR_Restore(cpu_sr)/*@ where schedule = false, first_heap = restore_heap */;
                 /*@ Assert opt == 0 && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
         os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
                   flag_del_source_after_restore(environment, critical, sg, caller, mask,
                     view, pgrp, opt, name, before, X, 0, OS_ERR_NONE, false) *
                   undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&cpu_sr, OS_CPU_SR) * undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
                 *perr                = OS_ERR_NONE;
                 pgrp_return          = (OS_FLAG_GRP *)0;  /* Event Flag Group has been deleted        */
             } else {
                 /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller) (acquired : UCOS2_Verify_State),
 opt == 0 && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                  os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
          flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && flag_del_protected_result(sg, view, pgrp, opt, name, acquired,
            pgrp, OS_ERR_TASK_WAITING, false, acquired) &&
          flag_del_source_cut(sg, active, acquired) &&
          flag_del_masked(environment, critical, protected_local, sg, active, cpu_sr, acquired, acquired) *
          undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
                 /*@ Given protected_local active acquired */
/*@ flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) && flag_del_source_restore_cut(sg, active, acquired, false) &&
    flag_del_masked(environment, critical, protected_local, sg, active, cpu_sr, acquired, acquired)
    which implies exists (restore_heap : model), os_sched_active_heap_cut(flag_del_source_restore_input(environment, critical, protected_local, sg, active, cpu_sr, acquired, acquired, false), restore_heap) */
/*@ Given restore_heap */
OS_CPU_SR_Restore(cpu_sr)/*@ where schedule = false, first_heap = restore_heap */;
                 /*@ Assert opt == 0 && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
         os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
                   flag_del_source_after_restore(environment, critical, sg, caller, mask,
                     view, pgrp, opt, name, before, X, pgrp, OS_ERR_TASK_WAITING, false) *
                   undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&cpu_sr, OS_CPU_SR) * undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
                 *perr                = OS_ERR_TASK_WAITING;
                 pgrp_return          = pgrp;
             }
             break;

        case OS_DEL_ALWAYS:                                /* Always delete the event flag group       */
    /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller) (acquired : UCOS2_Verify_State)
                      (id : Z) (image : FlagGroupImage),
 opt == 1 && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
        flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && view == FlagQueryPool(id) && flag_query_selected(view, acquired, image) && flag_del_rechecked(opt, image) &&
        tasks_waiting == flag_del_waiting(image) &&
        flag_del_source_cut(sg, active, acquired) &&
        data_at(&(pgrp->OSFlagType), INT8U, flagImageType(image)) *
        data_at(&(pgrp->OSFlagWaitList), void *, flagImageHead(image)) *
        data_at(&(pgrp->OSFlagFlags), OS_FLAGS, flagImageBits(image)) *
        data_at(&(pgrp->OSFlagName), INT8U *, flagImageName(image)) *
        data_at(&OSFlagFreeList, OS_FLAG_GRP *, flag_del_free_head_state(sg, acquired)) *
        flag_del_group_frame(environment, critical, protected_local, sg, active, cpu_sr, acquired,
          pgrp, id, acquired, image) * undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
             pnode = (OS_FLAG_NODE *)pgrp->OSFlagWaitList;
             /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller) (acquired current : UCOS2_Verify_State)
                    (id : Z) (image : FlagGroupImage) (order visited remaining : list Z)
                    (now_local : Armv7aContinuation -> Assertion),
 opt == 1 && flag_del_local_prefix(sg, visited, acquired, protected_local, current, now_local) && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                       os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
               flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && view == FlagQueryPool(id) &&
               flag_del_acquired_group(acquired, id, image, order) &&
               tasks_waiting == flag_del_waiting(image) &&
               flag_del_source_loop_facts(sg, active, acquired, id, order, visited, remaining, current, pnode) &&
               flag_del_masked(environment, critical, now_local, sg, active, cpu_sr, acquired, current) *
               undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
             /*@ Inv exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller) (acquired current : UCOS2_Verify_State)
                    (id : Z) (image : FlagGroupImage) (order visited remaining : list Z)
                    (now_local : Armv7aContinuation -> Assertion),
 opt == 1 && flag_del_local_prefix(sg, visited, acquired, protected_local, current, now_local) && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                       os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
               flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && view == FlagQueryPool(id) &&
               flag_del_acquired_group(acquired, id, image, order) &&
               tasks_waiting == flag_del_waiting(image) &&
               flag_del_source_loop_facts(sg, active, acquired, id, order, visited, remaining, current, pnode) &&
               flag_del_masked(environment, critical, now_local, sg, active, cpu_sr, acquired, current) *
               undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
             while (pnode != (OS_FLAG_NODE *)0) {          /* Ready ALL tasks waiting for flags        */
                 /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller)
                    (acquired current : UCOS2_Verify_State) (id : Z)
                    (image : FlagGroupImage) (order visited remaining : list Z)
                    (now_local : Armv7aContinuation -> Assertion)
                    (waiter : FlagWaiterState) (old : TaskAbstractState)
                    (original : TaskStackLease) (fragments : TaskStackFragments),
 opt == 1 && flag_del_local_prefix(sg, visited, acquired, protected_local, current, now_local) && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                           os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
                   flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && view == FlagQueryPool(id) &&
                   flag_del_acquired_group(acquired, id, image, order) &&
                   tasks_waiting == flag_del_waiting(image) &&
                   flag_del_source_loop_facts(sg, active, acquired, id, order, visited, remaining, current, pnode) &&
                   flag_del_waiter_at(current, pnode, waiter, old) &&
                   flag_del_loan_origin(current, waiter, original, fragments) &&
                   flag_task_rdy_fields_pre(sg, current, pnode, waiter, old, 0) *
                   flag_del_iteration_frame(environment, critical, now_local, sg, active, cpu_sr, acquired, current) *
                   undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
                 (void)OS_FlagTaskRdy(pnode, (OS_FLAGS)0, OS_STAT_PEND_ABORT)/*@ where F = F, result = PendAbort */;
                 /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller)
                    (acquired current post : UCOS2_Verify_State) (id node : Z)
                    (image : FlagGroupImage) (order visited remaining : list Z)
                    (now_local : Armv7aContinuation -> Assertion)
                    (waiter : FlagWaiterState) (old : TaskAbstractState)
                    (original : TaskStackLease) (fragments : TaskStackFragments),
 opt == 1 && flag_del_local_prefix(sg, visited, acquired, protected_local, current, now_local) && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                           os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
                   flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && view == FlagQueryPool(id) &&
                   flag_del_acquired_group(acquired, id, image, order) &&
                   tasks_waiting == flag_del_waiting(image) && pnode == node &&
                   flag_del_source_loop_facts(sg, active, acquired, id, order, visited, remaining, current, node) &&
                   flag_del_waiter_at(current, node, waiter, old) &&
                   flag_del_loan_origin(post, waiter, original, fragments) &&
                   flag_del_step(sg, current, node, post) &&
                   flag_del_iteration_next(environment, critical, now_local, sg, active, cpu_sr,
                     acquired, post, node, waiter) * undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
                 /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller)
                    (acquired current post : UCOS2_Verify_State) (id node : Z)
                    (image : FlagGroupImage) (order visited remaining : list Z)
                    (now_local : Armv7aContinuation -> Assertion)
                    (waiter : FlagWaiterState) (old : TaskAbstractState)
                    (original : TaskStackLease) (fragments : TaskStackFragments),
 opt == 1 && flag_del_local_prefix(sg, visited, acquired, protected_local, current, now_local) && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                           os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
                   flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && view == FlagQueryPool(id) &&
                   flag_del_acquired_group(acquired, id, image, order) &&
                   tasks_waiting == flag_del_waiting(image) && pnode == node &&
                   flag_del_source_loop_facts(sg, active, acquired, id, order, visited, remaining, current, node) &&
                   flag_del_waiter_at(current, node, waiter, old) &&
                   flag_del_loan_origin(post, waiter, original, fragments) &&
                   flag_del_step(sg, current, node, post) &&
                   data_at(&(pnode->OSFlagNodeNext), OS_FLAG_NODE *, flag_del_node_next(waiter)) *
                     flag_del_iteration_next_frame(environment, critical, now_local, sg, active,
                       cpu_sr, acquired, post, node, waiter) * undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
                 pnode = (OS_FLAG_NODE *)pnode->OSFlagNodeNext;
                 /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller)
                    (acquired post : UCOS2_Verify_State) (id : Z)
                    (image : FlagGroupImage) (order visited remaining : list Z)
                    (next_local : Armv7aContinuation -> Assertion),
 opt == 1 && flag_del_local_prefix(sg, visited, acquired, protected_local, post, next_local) && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                           os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
                   flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && view == FlagQueryPool(id) &&
                   flag_del_acquired_group(acquired, id, image, order) &&
                   tasks_waiting == flag_del_waiting(image) &&
                   flag_del_source_loop_facts(sg, active, acquired, id, order, visited, remaining, post, pnode) &&
                   flag_del_masked(environment, critical, next_local, sg, active, cpu_sr, acquired, post) *
                   undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
             }
             /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller) (acquired drained : UCOS2_Verify_State)
                    (id : Z) (image drained_image : FlagGroupImage) (order : list Z)
                    (now_local : Armv7aContinuation -> Assertion),
 opt == 1 && flag_del_local_prefix(sg, order, acquired, protected_local, drained, now_local) && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                       os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
               flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && view == FlagQueryPool(id) &&
               flag_del_acquired_group(acquired, id, image, order) &&
               tasks_waiting == flag_del_waiting(image) &&
               flag_del_source_loop_facts(sg, active, acquired, id, order, order, nil, drained, 0) &&
               flag_query_selected(view, drained, drained_image) &&
               flag_del_group_cut(environment, critical, now_local, sg, active, cpu_sr, acquired,
                 pgrp, id, drained, drained_image) * undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
    /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller) (acquired drained : UCOS2_Verify_State)
                    (id : Z) (image drained_image : FlagGroupImage) (order : list Z)
                    (now_local : Armv7aContinuation -> Assertion),
 opt == 1 && flag_del_local_prefix(sg, order, acquired, protected_local, drained, now_local) && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                       os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
               flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && view == FlagQueryPool(id) &&
               flag_del_acquired_group(acquired, id, image, order) &&
               tasks_waiting == flag_del_waiting(image) &&
               flag_del_source_loop_facts(sg, active, acquired, id, order, order, nil, drained, 0) &&
               flag_query_selected(view, drained, drained_image) &&
               data_at(&(pgrp->OSFlagType), INT8U, flagImageType(drained_image)) *
        data_at(&(pgrp->OSFlagWaitList), void *, flagImageHead(drained_image)) *
        data_at(&(pgrp->OSFlagFlags), OS_FLAGS, flagImageBits(drained_image)) *
        data_at(&(pgrp->OSFlagName), INT8U *, flagImageName(drained_image)) *
        data_at(&OSFlagFreeList, OS_FLAG_GRP *, flag_del_free_head_state(sg, drained)) *
        flag_del_group_frame(environment, critical, now_local, sg, active, cpu_sr, acquired,
          pgrp, id, drained, drained_image) * undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
#if OS_FLAG_NAME_EN > 0u
             pgrp->OSFlagName     = (INT8U *)(void *)"?";
#endif
             pgrp->OSFlagType     = OS_EVENT_TYPE_UNUSED;
             pgrp->OSFlagWaitList = (void *)OSFlagFreeList;/* Return group to free list                */
             pgrp->OSFlagFlags    = (OS_FLAGS)0;
             OSFlagFreeList       = pgrp;
             /*@ Assert exists (active : TaskSuspendCaller) (acquired released : UCOS2_Verify_State)
                    (now_local : Armv7aContinuation -> Assertion) (scheduled : bool),
 opt == 1 && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                       os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
               flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) && scheduled == flag_del_schedule_bit(tasks_waiting) &&
               flag_del_protected_result(sg, view, pgrp, opt, name, acquired,
                 0, OS_ERR_NONE, scheduled, released) &&
               flag_del_source_cut(sg, active, released) &&
               flag_del_masked(environment, critical, now_local, sg, active, cpu_sr, acquired, released) *
               undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
             /*@ Given active acquired released now_local scheduled */
/*@ flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) && flag_del_source_restore_cut(sg, active, released, flag_del_schedule_bit(tasks_waiting)) &&
    flag_del_masked(environment, critical, now_local, sg, active, cpu_sr, acquired, released)
    which implies exists (restore_heap : model), os_sched_active_heap_cut(flag_del_source_restore_input(environment, critical, now_local, sg, active, cpu_sr, acquired, released, flag_del_schedule_bit(tasks_waiting)), restore_heap) */
/*@ Given restore_heap */
OS_CPU_SR_Restore(cpu_sr)/*@ where schedule = flag_del_schedule_bit(tasks_waiting), first_heap = restore_heap */;
             /*@ Assert exists (now_local : Armv7aContinuation -> Assertion) (scheduled : bool),
 opt == 1 && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                       os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
               scheduled == flag_del_schedule_bit(tasks_waiting) &&
               flag_del_source_after_restore(environment, critical, sg, caller, mask,
                 view, pgrp, opt, name, before, X, 0, OS_ERR_NONE, scheduled) *
               undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&cpu_sr, OS_CPU_SR) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
             if (tasks_waiting == OS_TRUE) {               /* Reschedule only if task(s) were waiting  */
                 /*@ Assert exists (context : OsSchedCallContext) (current : UCOS2_Verify_State)
                    (now_local : Armv7aContinuation -> Assertion),
 opt == 1 && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                           os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
                   flag_del_prefix_to_scheduler(environment, critical, sg, caller, mask, view, pgrp, opt, name, before, context, current) &&
                    flag_del_scheduler_safe(environment, critical, sg, context, mask, current, 0, OS_ERR_NONE, X) &&
                   flag_del_same_task_call(context, caller) &&
                   os_sched_active_local_stable(flag_del_source_active(sg)) &&
                    os_sched_active_call_pre(environment, now_local, flag_del_source_active(sg),
                     sg, context, mask, current) * undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&cpu_sr, OS_CPU_SR) * undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
                 OS_Sched();                               /* Find highest priority task ready to run  */
             }
             *perr = OS_ERR_NONE;
             pgrp_return          = (OS_FLAG_GRP *)0;      /* Event Flag Group has been deleted        */
             break;

        default:
             /*@ Assert exists (protected_local : Armv7aContinuation -> Assertion) (active : TaskSuspendCaller) (acquired : UCOS2_Verify_State),
 opt != 0 && opt != 1 && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                       os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
               flag_del_source_prefix_facts(environment, critical, sg, caller, mask, view, pgrp, opt, name,
          before, observed, active, cpu_sr, acquired, X) &&
               flag_del_protected_result(sg, view, pgrp, opt, name, acquired,
                 pgrp, OS_ERR_INVALID_OPT, false, acquired) &&
               flag_del_source_cut(sg, active, acquired) &&
               flag_del_masked(environment, critical, protected_local, sg, active, cpu_sr, acquired, acquired) *
               undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
             /*@ Given protected_local active acquired */
/*@ flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) && flag_del_source_restore_cut(sg, active, acquired, false) &&
    flag_del_masked(environment, critical, protected_local, sg, active, cpu_sr, acquired, acquired)
    which implies exists (restore_heap : model), os_sched_active_heap_cut(flag_del_source_restore_input(environment, critical, protected_local, sg, active, cpu_sr, acquired, acquired, false), restore_heap) */
/*@ Given restore_heap */
OS_CPU_SR_Restore(cpu_sr)/*@ where schedule = false, first_heap = restore_heap */;
             /*@ Assert opt != 0 && opt != 1 && pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
         os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSFlagFreeList == g_OSFlagFreeList(sg) && name == LitMap("?") &&
        flag_del_build_context(sg) && flag_del_stack_layout(sg) && kernel_sched_ready_clients(critical) &&
        flag_del_argument(sg, pgrp, view, before, observed) &&
               flag_del_source_after_restore(environment, critical, sg, caller, mask,
                 view, pgrp, opt, name, before, X, pgrp, OS_ERR_INVALID_OPT, false) *
               undef_data_at(perr, INT8U) * GlobalStrings(LitMap) * F *
          undef_data_at(&cpu_sr, OS_CPU_SR) * undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&pgrp_return, OS_FLAG_GRP *) */
             *perr                = OS_ERR_INVALID_OPT;
             pgrp_return          = pgrp;
             break;
    }

    OS_TRACE_FLAG_DEL_EXIT(*perr);

    /*@ Assert exists (returned : TaskSuspendCaller) (current : UCOS2_Verify_State)
                 (after_local : Armv7aContinuation -> Assertion) (error : Z),
 pgrp == pointer && opt == option && 0 <= option && option <= 255 && perr == error_address &&
                flag_del_source_return_cut(environment, critical, after_local, sg, caller, returned, mask,
          pgrp, view, opt, name, before, current, pair(pgrp_return, error), X) * data_at(perr, INT8U, error) * GlobalStrings(LitMap) * F *
          undef_data_at(&cpu_sr, OS_CPU_SR) * undef_data_at(&tasks_waiting, BOOLEAN) * undef_data_at(&pnode, OS_FLAG_NODE *) */
    return (pgrp_return);
}
