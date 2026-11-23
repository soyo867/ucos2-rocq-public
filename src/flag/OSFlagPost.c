/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

OS_FLAGS  OSFlagPost (OS_FLAG_GRP  *pgrp,
                      OS_FLAGS      flags,
                      INT8U         opt,
                      INT8U        *perr)
/*@ With (linked : FlagPostLinkedCSource) (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
         (sg : StableGlobVars) (original : FlagPostExecution) (mask : Z)
         (before : UCOS2_Verify_State) (local : Armv7aContinuation -> Assertion)
         (pointer id requested option_word error_cell old_error : Z) (F : Assertion)
         (X : FlagPostObservation -> UCOS2_Verify_State -> Prop)
    Require pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
            os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
            kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
            flag_post_public_pre(linked, environment, critical, sg, original, mask, before, local,
              pointer, id, requested, option_word, error_cell, old_error, F, X)
    Ensure flag_post_public_post(environment, sg, original, mask, error_cell, __return, F, X)
*/
{
    OS_FLAG_NODE *pnode;
    BOOLEAN       sched;
    OS_FLAGS      flags_cur;
    OS_FLAGS      flags_rdy;
    BOOLEAN       rdy;
#if OS_CRITICAL_METHOD == 3u                         /* Allocate storage for CPU status register       */
    OS_CPU_SR     cpu_sr = 0u;
#endif

    /*@ flag_post_public_pre(linked, environment, critical, sg, original, mask, before, local,
          pointer, id, requested, option_word, error_cell, old_error, F, X)
        which implies
        flag_post_pointer_image(before, id, pointer) &&
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) &&
        flag_post_source_closed(environment, local, sg, original, mask, before) *
        data_at(error_cell, INT8U, old_error) * F
    */

#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        /*@ Assert flag_post_public_post(environment, sg, original, mask, error_cell, 0, F, X) *
            data_at(&pgrp, OS_FLAG_GRP *, pointer) * data_at(&flags, OS_FLAGS, requested) *
            data_at(&opt, INT8U, option_word) * data_at(&perr, INT8U *, error_cell) *
            undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&sched, BOOLEAN) *
            undef_data_at(&flags_cur, OS_FLAGS) * undef_data_at(&flags_rdy, OS_FLAGS) *
            undef_data_at(&rdy, BOOLEAN) * undef_data_at(&cpu_sr, OS_CPU_SR)
        */
        return ((OS_FLAGS)0);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pgrp == (OS_FLAG_GRP *)0) {                  /* Validate 'pgrp'                                */
        *perr = OS_ERR_FLAG_INVALID_PGRP;
        /*@ Assert flag_post_public_post(environment, sg, original, mask, error_cell, 0, F, X) *
            data_at(&pgrp, OS_FLAG_GRP *, pointer) * data_at(&flags, OS_FLAGS, requested) *
            data_at(&opt, INT8U, option_word) * data_at(&perr, INT8U *, error_cell) *
            undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&sched, BOOLEAN) *
            undef_data_at(&flags_cur, OS_FLAGS) * undef_data_at(&flags_rdy, OS_FLAGS) *
            undef_data_at(&rdy, BOOLEAN) * undef_data_at(&cpu_sr, OS_CPU_SR)
        */
        return ((OS_FLAGS)0);
    }
#endif

    OS_TRACE_FLAG_POST_ENTER(pgrp, flags, opt);

    /*@ flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_pointer_image(before, id, pointer) && pointer != 0 && flag_post_source_closed(environment, local, sg, original, mask, before) * data_at(&pgrp, OS_FLAG_GRP *, pointer)
        which implies exists (image : FlagGroupImage),
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_pointer_image(before, id, pointer) && pointer != 0 && flag_post_current_valid(sg, original, before) && flag_post_image_at(before, id, image) &&
        data_at(&pgrp, OS_FLAG_GRP *, pointer) * data_at(&(pgrp->OSFlagType), INT8U, flagImageType(image)) *
        flag_post_type_frame(sg, before, id, image) *
        flag_post_execution_frame(environment, local, sg, original, mask, before)
    */
    if (pgrp->OSFlagType != OS_EVENT_TYPE_FLAG) {    /* Make sure we are pointing to an event flag grp */
        *perr = OS_ERR_EVENT_TYPE;
        OS_TRACE_FLAG_POST_EXIT(*perr);
        /*@ Assert flag_post_public_post(environment, sg, original, mask, error_cell, 0, F, X) *
            data_at(&pgrp, OS_FLAG_GRP *, pointer) * data_at(&flags, OS_FLAGS, requested) *
            data_at(&opt, INT8U, option_word) * data_at(&perr, INT8U *, error_cell) *
            undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&sched, BOOLEAN) *
            undef_data_at(&flags_cur, OS_FLAGS) * undef_data_at(&flags_rdy, OS_FLAGS) *
            undef_data_at(&rdy, BOOLEAN) * undef_data_at(&cpu_sr, OS_CPU_SR)
        */
        return ((OS_FLAGS)0);
    }

    /*@ exists (image : FlagGroupImage),
        flag_post_parameters(sg, pointer, id, requested, option_word) && pointer != 0 &&
        flag_post_current_valid(sg, original, before) &&
        flag_post_image_at(before, id, image) && flagImageType(image) == 5 &&
        data_at(&pgrp, OS_FLAG_GRP *, pointer) * data_at(&(pgrp->OSFlagType), INT8U, flagImageType(image)) *
        flag_post_type_frame(sg, before, id, image) *
        flag_post_execution_frame(environment, local, sg, original, mask, before)
        which implies flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_initial_type_ok(before, id) && flag_post_source_closed(environment, local, sg, original, mask, before) * data_at(&pgrp, OS_FLAG_GRP *, pointer)
    */
    /*@ flag_post_source_closed(environment, local, sg, original, mask, before) *
        data_at(error_cell, INT8U, old_error) * F
        which implies exists (captured : model),
        flag_post_save_input(environment, critical, local, sg, original, mask, before, flag_post_caller_frame(error_cell, old_error, F), captured)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (entry : FlagPostProtectedContext),
        pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) &&
        flag_post_protected_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry) *
        data_at(error_cell, INT8U, old_error) * F *
        undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&sched, BOOLEAN) *
        undef_data_at(&flags_cur, OS_FLAGS) * undef_data_at(&flags_rdy, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
    */

    /* The group may have been deleted before interrupts were masked. */
    /*@ exists (entry : FlagPostProtectedContext), flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_protected_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry) * data_at(&pgrp, OS_FLAG_GRP *, pointer)
        which implies exists (entry : FlagPostProtectedContext) (image : FlagGroupImage),
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_protected_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry) &&
        flag_post_image_at(flag_post_acquired(entry), id, image) &&
        data_at(&pgrp, OS_FLAG_GRP *, pointer) * data_at(&(pgrp->OSFlagType), INT8U, flagImageType(image)) *
        flag_post_type_frame(sg, flag_post_acquired(entry), id, image) *
        flag_post_critical_frame(environment, critical, flag_post_local(entry), sg,
          flag_post_entered(entry), cpu_sr, flag_post_acquired(entry), flag_post_acquired(entry))
    */
    if (((opt == OS_FLAG_CLR) || (opt == OS_FLAG_SET)) &&
        (pgrp->OSFlagType != OS_EVENT_TYPE_FLAG)) {
        /*@ Assert exists (entry : FlagPostProtectedContext) (result : FlagPostProtectedResult)
                             (released : UCOS2_Verify_State) (active_local : Armv7aContinuation -> Assertion),
                 pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
                 flag_post_parameters(sg, pointer, id, requested, option_word) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) && flag_post_result_error(result, 1) && flag_post_exit_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry, result, released, active_local) *
                 data_at(error_cell, INT8U, old_error) * F * undef_data_at(&pnode, OS_FLAG_NODE *) *
                 undef_data_at(&sched, BOOLEAN) * undef_data_at(&flags_cur, OS_FLAGS) *
                 undef_data_at(&flags_rdy, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
             */
             /*@ Given entry result released active_local */
             /*@ flag_post_exit_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry, result, released, active_local) *
                 data_at(error_cell, INT8U, old_error) * F
                 which implies exists (captured : model),
                 flag_post_protected_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry) &&
                 flag_post_protected_run(sg, id, requested, option_word, flag_post_acquired(entry), result, released) &&
                 flag_post_restore_input(environment, critical, mask, active_local, sg,
                   flag_post_entered(entry), cpu_sr, flag_post_acquired(entry), released, flag_post_caller_frame(error_cell, old_error, F), captured)
             */
             /*@ Given captured */
             OS_EXIT_CRITICAL();
             /*@ flag_post_restore_output(environment, critical, sg, flag_post_entered(entry), mask,
                   cpu_sr, flag_post_acquired(entry), released, active_local,
                   flag_post_caller_frame(error_cell, old_error, F), captured)
                 which implies exists (returned : FlagPostExecution) (current : UCOS2_Verify_State)
                   (returned_local : Armv7aContinuation -> Assertion),
                 interrupt_saved_value(mask, cpu_sr) &&
                 flag_post_restore_relation(environment, critical, sg, flag_post_entered(entry), released, returned, current) &&
                 flag_post_source_closed(environment, returned_local, sg, returned, mask, current) *
                 data_at(error_cell, INT8U, old_error) * F
             */

        *perr = OS_ERR_EVENT_TYPE;
        OS_TRACE_FLAG_POST_EXIT(*perr);
        /*@ Assert flag_post_public_post(environment, sg, original, mask, error_cell, 0, F, X) *
            data_at(&pgrp, OS_FLAG_GRP *, pointer) * data_at(&flags, OS_FLAGS, requested) *
            data_at(&opt, INT8U, option_word) * data_at(&perr, INT8U *, error_cell) *
            undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&sched, BOOLEAN) *
            undef_data_at(&flags_cur, OS_FLAGS) * undef_data_at(&flags_rdy, OS_FLAGS) *
            undef_data_at(&rdy, BOOLEAN) * undef_data_at(&cpu_sr, OS_CPU_SR)
        */
        return ((OS_FLAGS)0);
    }

    /*@ exists (entry : FlagPostProtectedContext) (image : FlagGroupImage),
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_protected_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry) &&
        flag_post_image_at(flag_post_acquired(entry), id, image) &&
        flag_post_checked_type(option_word, image) &&
        data_at(&pgrp, OS_FLAG_GRP *, pointer) * data_at(&(pgrp->OSFlagType), INT8U, flagImageType(image)) *
        flag_post_type_frame(sg, flag_post_acquired(entry), id, image) *
        flag_post_critical_frame(environment, critical, flag_post_local(entry), sg,
          flag_post_entered(entry), cpu_sr, flag_post_acquired(entry), flag_post_acquired(entry))
        which implies exists (entry : FlagPostProtectedContext) (image : FlagGroupImage),
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_protected_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry) &&
        flag_post_image_at(flag_post_acquired(entry), id, image) &&
        flag_post_checked_type(option_word, image) &&
        data_at(&pgrp, OS_FLAG_GRP *, pointer) * data_at(&(pgrp->OSFlagFlags), OS_FLAGS, flagImageBits(image)) *
        flag_post_current_word_frame(sg, flag_post_acquired(entry), id, image) *
        flag_post_critical_frame(environment, critical, flag_post_local(entry), sg,
          flag_post_entered(entry), cpu_sr, flag_post_acquired(entry), flag_post_acquired(entry))
    */
    switch (opt) {
        case OS_FLAG_CLR:
             pgrp->OSFlagFlags &= (OS_FLAGS)~flags;  /* Clear the flags specified in the group         */
             break;

        case OS_FLAG_SET:
             pgrp->OSFlagFlags |=  flags;            /* Set   the flags specified in the group         */
             break;

        default:
             /*@ Assert exists (entry : FlagPostProtectedContext) (result : FlagPostProtectedResult)
                             (released : UCOS2_Verify_State) (active_local : Armv7aContinuation -> Assertion),
                 pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
                 flag_post_parameters(sg, pointer, id, requested, option_word) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) && flag_post_result_error(result, 113) && flag_post_exit_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry, result, released, active_local) *
                 data_at(error_cell, INT8U, old_error) * F * undef_data_at(&pnode, OS_FLAG_NODE *) *
                 undef_data_at(&sched, BOOLEAN) * undef_data_at(&flags_cur, OS_FLAGS) *
                 undef_data_at(&flags_rdy, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
             */
             /*@ Given entry result released active_local */
             /*@ flag_post_exit_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry, result, released, active_local) *
                 data_at(error_cell, INT8U, old_error) * F
                 which implies exists (captured : model),
                 flag_post_protected_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry) &&
                 flag_post_protected_run(sg, id, requested, option_word, flag_post_acquired(entry), result, released) &&
                 flag_post_restore_input(environment, critical, mask, active_local, sg,
                   flag_post_entered(entry), cpu_sr, flag_post_acquired(entry), released, flag_post_caller_frame(error_cell, old_error, F), captured)
             */
             /*@ Given captured */
             OS_EXIT_CRITICAL();
             /*@ flag_post_restore_output(environment, critical, sg, flag_post_entered(entry), mask,
                   cpu_sr, flag_post_acquired(entry), released, active_local,
                   flag_post_caller_frame(error_cell, old_error, F), captured)
                 which implies exists (returned : FlagPostExecution) (current : UCOS2_Verify_State)
                   (returned_local : Armv7aContinuation -> Assertion),
                 interrupt_saved_value(mask, cpu_sr) &&
                 flag_post_restore_relation(environment, critical, sg, flag_post_entered(entry), released, returned, current) &&
                 flag_post_source_closed(environment, returned_local, sg, returned, mask, current) *
                 data_at(error_cell, INT8U, old_error) * F
             */
                     /* INVALID option                                 */
             *perr = OS_ERR_FLAG_INVALID_OPT;
             OS_TRACE_FLAG_POST_EXIT(*perr);
             /*@ Assert flag_post_public_post(environment, sg, original, mask, error_cell, 0, F, X) *
            data_at(&pgrp, OS_FLAG_GRP *, pointer) * data_at(&flags, OS_FLAGS, requested) *
            data_at(&opt, INT8U, option_word) * data_at(&perr, INT8U *, error_cell) *
            undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&sched, BOOLEAN) *
            undef_data_at(&flags_cur, OS_FLAGS) * undef_data_at(&flags_rdy, OS_FLAGS) *
            undef_data_at(&rdy, BOOLEAN) * undef_data_at(&cpu_sr, OS_CPU_SR)
        */
        return ((OS_FLAGS)0);
    }
    /*@ Assert exists (context : FlagPostLoopContext),
        pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_initial_scan(context) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) &&
        flag_post_loop_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, flag_post_remaining_node(flag_post_remaining(context)), 0) *
        data_at(error_cell, INT8U, old_error) * F * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&sched, BOOLEAN) *
        undef_data_at(&flags_cur, OS_FLAGS) * undef_data_at(&flags_rdy, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
    */
    /*@ exists (context : FlagPostLoopContext),
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_initial_scan(context) &&
        flag_post_loop_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, flag_post_remaining_node(flag_post_remaining(context)), 0) * data_at(&pgrp, OS_FLAG_GRP *, pointer)
        which implies exists (context : FlagPostLoopContext) (image : FlagGroupImage),
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_initial_scan(context) &&
        flag_post_loop_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, flagImageHead(image), 0) &&
        flag_post_image_at(flag_post_scan_state(flag_post_accumulator(context)), id, image) &&
        data_at(&pgrp, OS_FLAG_GRP *, pointer) * data_at(&(pgrp->OSFlagWaitList), void *, flagImageHead(image)) *
        flag_post_group_head_frame(sg, flag_post_scan_state(flag_post_accumulator(context)), id, image) *
        flag_post_critical_frame(environment, critical, flag_post_loop_local(context), sg,
          flag_post_entered(flag_post_loop_entry(context)), cpu_sr, flag_post_acquired(flag_post_loop_entry(context)),
          flag_post_scan_state(flag_post_accumulator(context)))
    */
    sched = OS_FALSE;                                /* Indicate that we don't need rescheduling       */
    pnode = (OS_FLAG_NODE *)pgrp->OSFlagWaitList;
    /*@ Assert exists (context : FlagPostLoopContext),
        pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) && flag_post_loop_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, sched) *
        data_at(error_cell, INT8U, old_error) * F * undef_data_at(&flags_cur, OS_FLAGS) *
        undef_data_at(&flags_rdy, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
    */
    /*@ Inv exists (context : FlagPostLoopContext),
        pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) && flag_post_loop_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, sched) *
        data_at(error_cell, INT8U, old_error) * F * undef_data_at(&flags_cur, OS_FLAGS) *
        undef_data_at(&flags_rdy, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
    */
    while (pnode != (OS_FLAG_NODE *)0) {             /* Go through all tasks waiting on event flag(s)  */
        /*@ exists (context : FlagPostLoopContext),
            pnode != 0 &&
            flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_loop_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, sched) * data_at(&pgrp, OS_FLAG_GRP *, pointer)
        which implies exists (context : FlagPostLoopContext) (waiter : FlagWaiterState) (image : FlagGroupImage),
            flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_loop_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, sched) &&
            flag_post_waiter_at(flag_post_scan_state(flag_post_accumulator(context)), pnode, waiter) &&
            flag_post_image_at(flag_post_scan_state(flag_post_accumulator(context)), id, image) &&
            data_at(&pgrp, OS_FLAG_GRP *, pointer) * data_at(&pnode->OSFlagNodeNext, void *, flagNodeNext(flagWaitImage(waiter))) *
            data_at(&pnode->OSFlagNodePrev, void *, flagNodePrev(flagWaitImage(waiter))) *
            data_at(&pnode->OSFlagNodeTCB, void *, flagNodeTCB(flagWaitImage(waiter))) *
            data_at(&pnode->OSFlagNodeFlagGrp, void *, flagNodeGroup(flagWaitImage(waiter))) *
            data_at(&pnode->OSFlagNodeFlags, OS_FLAGS, flagNodeMask(flagWaitImage(waiter))) *
            data_at(&pnode->OSFlagNodeWaitType, INT8U, flagNodeMode(flagWaitImage(waiter))) *
            data_at(&(pgrp->OSFlagFlags), OS_FLAGS, flagImageBits(image)) *
            flag_post_node_word_frame(sg, flag_post_scan_state(flag_post_accumulator(context)), id, pnode, image) *
            flag_post_critical_frame(environment, critical, flag_post_loop_local(context), sg,
              flag_post_entered(flag_post_loop_entry(context)), cpu_sr, flag_post_acquired(flag_post_loop_entry(context)),
              flag_post_scan_state(flag_post_accumulator(context)))
    */
        switch (pnode->OSFlagNodeWaitType) {
            case OS_FLAG_WAIT_SET_ALL:               /* See if all req. flags are set for current node */
                 flags_rdy = (OS_FLAGS)(pgrp->OSFlagFlags & pnode->OSFlagNodeFlags);
                 if (flags_rdy == pnode->OSFlagNodeFlags) {   /* Make task RTR, event(s) Rx'd          */
                     /*@ Assert exists (context : FlagPostLoopContext) (waiter : FlagWaiterState) (old : TaskAbstractState),
                         pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
                         flag_post_parameters(sg, pointer, id, requested, option_word) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) &&
                         sched == flag_post_schedule_word(flag_post_scan_visits(flag_post_accumulator(context))) &&
                         flag_post_helper_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, flags_rdy, waiter, old) *
                         data_at(error_cell, INT8U, old_error) * F * undef_data_at(&flags_cur, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
                     */
                     /*@ exists (context : FlagPostLoopContext) (waiter : FlagWaiterState) (old : TaskAbstractState),
                         sched == flag_post_schedule_word(flag_post_scan_visits(flag_post_accumulator(context))) &&
                         flag_post_helper_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, flags_rdy, waiter, old)
                         which implies exists (context : FlagPostLoopContext) (waiter : FlagWaiterState) (old : TaskAbstractState),
                         0 == encode_pend_status(PendOK) &&
                         flag_post_loop_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, sched) &&
                         flag_post_waiter_at(flag_post_scan_state(flag_post_accumulator(context)), pnode, waiter) &&
                         flag_post_waiter_satisfied(sg, context, waiter, flags_rdy) &&
                         flag_task_rdy_fields_pre(sg, flag_post_scan_state(flag_post_accumulator(context)), pnode, waiter, old, flags_rdy) *
                         UCOS2_raw_rep_missing_task_storage_sched_flag(sg, flag_post_scan_state(flag_post_accumulator(context))) * unmap_table_rep(sg) *
                         flag_post_critical_frame(environment, critical, flag_post_loop_local(context), sg,
                           flag_post_entered(flag_post_loop_entry(context)), cpu_sr, flag_post_acquired(flag_post_loop_entry(context)),
                           flag_post_scan_state(flag_post_accumulator(context)))
                     */
                     rdy = OS_FlagTaskRdy(pnode, flags_rdy, OS_STAT_PEND_OK) /*@ where result=PendOK, F=F */;
                     if (rdy == OS_TRUE) {
                         sched = OS_TRUE;                     /* When done we will reschedule          */
                     }
                 }
                 break;

            case OS_FLAG_WAIT_SET_ANY:               /* See if any flag set                            */
                 flags_rdy = (OS_FLAGS)(pgrp->OSFlagFlags & pnode->OSFlagNodeFlags);
                 if (flags_rdy != (OS_FLAGS)0) {              /* Make task RTR, event(s) Rx'd          */
                     /*@ Assert exists (context : FlagPostLoopContext) (waiter : FlagWaiterState) (old : TaskAbstractState),
                         pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
                         flag_post_parameters(sg, pointer, id, requested, option_word) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) &&
                         sched == flag_post_schedule_word(flag_post_scan_visits(flag_post_accumulator(context))) &&
                         flag_post_helper_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, flags_rdy, waiter, old) *
                         data_at(error_cell, INT8U, old_error) * F * undef_data_at(&flags_cur, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
                     */
                     /*@ exists (context : FlagPostLoopContext) (waiter : FlagWaiterState) (old : TaskAbstractState),
                         sched == flag_post_schedule_word(flag_post_scan_visits(flag_post_accumulator(context))) &&
                         flag_post_helper_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, flags_rdy, waiter, old)
                         which implies exists (context : FlagPostLoopContext) (waiter : FlagWaiterState) (old : TaskAbstractState),
                         0 == encode_pend_status(PendOK) &&
                         flag_post_loop_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, sched) &&
                         flag_post_waiter_at(flag_post_scan_state(flag_post_accumulator(context)), pnode, waiter) &&
                         flag_post_waiter_satisfied(sg, context, waiter, flags_rdy) &&
                         flag_task_rdy_fields_pre(sg, flag_post_scan_state(flag_post_accumulator(context)), pnode, waiter, old, flags_rdy) *
                         UCOS2_raw_rep_missing_task_storage_sched_flag(sg, flag_post_scan_state(flag_post_accumulator(context))) * unmap_table_rep(sg) *
                         flag_post_critical_frame(environment, critical, flag_post_loop_local(context), sg,
                           flag_post_entered(flag_post_loop_entry(context)), cpu_sr, flag_post_acquired(flag_post_loop_entry(context)),
                           flag_post_scan_state(flag_post_accumulator(context)))
                     */
                     rdy = OS_FlagTaskRdy(pnode, flags_rdy, OS_STAT_PEND_OK) /*@ where result=PendOK, F=F */;
                     if (rdy == OS_TRUE) {
                         sched = OS_TRUE;                     /* When done we will reschedule          */
                     }
                 }
                 break;

#if OS_FLAG_WAIT_CLR_EN > 0u
            case OS_FLAG_WAIT_CLR_ALL:               /* See if all req. flags are set for current node */
                 flags_rdy = (OS_FLAGS)~pgrp->OSFlagFlags & pnode->OSFlagNodeFlags;
                 if (flags_rdy == pnode->OSFlagNodeFlags) {   /* Make task RTR, event(s) Rx'd          */
                     /*@ Assert exists (context : FlagPostLoopContext) (waiter : FlagWaiterState) (old : TaskAbstractState),
                         pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
                         flag_post_parameters(sg, pointer, id, requested, option_word) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) &&
                         sched == flag_post_schedule_word(flag_post_scan_visits(flag_post_accumulator(context))) &&
                         flag_post_helper_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, flags_rdy, waiter, old) *
                         data_at(error_cell, INT8U, old_error) * F * undef_data_at(&flags_cur, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
                     */
                     /*@ exists (context : FlagPostLoopContext) (waiter : FlagWaiterState) (old : TaskAbstractState),
                         sched == flag_post_schedule_word(flag_post_scan_visits(flag_post_accumulator(context))) &&
                         flag_post_helper_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, flags_rdy, waiter, old)
                         which implies exists (context : FlagPostLoopContext) (waiter : FlagWaiterState) (old : TaskAbstractState),
                         0 == encode_pend_status(PendOK) &&
                         flag_post_loop_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, sched) &&
                         flag_post_waiter_at(flag_post_scan_state(flag_post_accumulator(context)), pnode, waiter) &&
                         flag_post_waiter_satisfied(sg, context, waiter, flags_rdy) &&
                         flag_task_rdy_fields_pre(sg, flag_post_scan_state(flag_post_accumulator(context)), pnode, waiter, old, flags_rdy) *
                         UCOS2_raw_rep_missing_task_storage_sched_flag(sg, flag_post_scan_state(flag_post_accumulator(context))) * unmap_table_rep(sg) *
                         flag_post_critical_frame(environment, critical, flag_post_loop_local(context), sg,
                           flag_post_entered(flag_post_loop_entry(context)), cpu_sr, flag_post_acquired(flag_post_loop_entry(context)),
                           flag_post_scan_state(flag_post_accumulator(context)))
                     */
                     rdy = OS_FlagTaskRdy(pnode, flags_rdy, OS_STAT_PEND_OK) /*@ where result=PendOK, F=F */;
                     if (rdy == OS_TRUE) {
                         sched = OS_TRUE;                     /* When done we will reschedule          */
                     }
                 }
                 break;

            case OS_FLAG_WAIT_CLR_ANY:               /* See if any flag set                            */
                 flags_rdy = (OS_FLAGS)~pgrp->OSFlagFlags & pnode->OSFlagNodeFlags;
                 if (flags_rdy != (OS_FLAGS)0) {              /* Make task RTR, event(s) Rx'd          */
                     /*@ Assert exists (context : FlagPostLoopContext) (waiter : FlagWaiterState) (old : TaskAbstractState),
                         pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
                         flag_post_parameters(sg, pointer, id, requested, option_word) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) &&
                         sched == flag_post_schedule_word(flag_post_scan_visits(flag_post_accumulator(context))) &&
                         flag_post_helper_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, flags_rdy, waiter, old) *
                         data_at(error_cell, INT8U, old_error) * F * undef_data_at(&flags_cur, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
                     */
                     /*@ exists (context : FlagPostLoopContext) (waiter : FlagWaiterState) (old : TaskAbstractState),
                         sched == flag_post_schedule_word(flag_post_scan_visits(flag_post_accumulator(context))) &&
                         flag_post_helper_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, flags_rdy, waiter, old)
                         which implies exists (context : FlagPostLoopContext) (waiter : FlagWaiterState) (old : TaskAbstractState),
                         0 == encode_pend_status(PendOK) &&
                         flag_post_loop_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, sched) &&
                         flag_post_waiter_at(flag_post_scan_state(flag_post_accumulator(context)), pnode, waiter) &&
                         flag_post_waiter_satisfied(sg, context, waiter, flags_rdy) &&
                         flag_task_rdy_fields_pre(sg, flag_post_scan_state(flag_post_accumulator(context)), pnode, waiter, old, flags_rdy) *
                         UCOS2_raw_rep_missing_task_storage_sched_flag(sg, flag_post_scan_state(flag_post_accumulator(context))) * unmap_table_rep(sg) *
                         flag_post_critical_frame(environment, critical, flag_post_loop_local(context), sg,
                           flag_post_entered(flag_post_loop_entry(context)), cpu_sr, flag_post_acquired(flag_post_loop_entry(context)),
                           flag_post_scan_state(flag_post_accumulator(context)))
                     */
                     rdy = OS_FlagTaskRdy(pnode, flags_rdy, OS_STAT_PEND_OK) /*@ where result=PendOK, F=F */;
                     if (rdy == OS_TRUE) {
                         sched = OS_TRUE;                     /* When done we will reschedule          */
                     }
                 }
                 break;
#endif
            default:
                 /*@ Assert exists (entry : FlagPostProtectedContext) (result : FlagPostProtectedResult)
                             (released : UCOS2_Verify_State) (active_local : Armv7aContinuation -> Assertion),
                 pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
                 flag_post_parameters(sg, pointer, id, requested, option_word) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) && flag_post_result_error(result, 111) && flag_post_exit_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry, result, released, active_local) *
                 data_at(error_cell, INT8U, old_error) * F * undef_data_at(&pnode, OS_FLAG_NODE *) *
                 undef_data_at(&sched, BOOLEAN) * undef_data_at(&flags_cur, OS_FLAGS) *
                 undef_data_at(&flags_rdy, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
             */
             /*@ Given entry result released active_local */
             /*@ flag_post_exit_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry, result, released, active_local) *
                 data_at(error_cell, INT8U, old_error) * F
                 which implies exists (captured : model),
                 flag_post_protected_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry) &&
                 flag_post_protected_run(sg, id, requested, option_word, flag_post_acquired(entry), result, released) &&
                 flag_post_restore_input(environment, critical, mask, active_local, sg,
                   flag_post_entered(entry), cpu_sr, flag_post_acquired(entry), released, flag_post_caller_frame(error_cell, old_error, F), captured)
             */
             /*@ Given captured */
             OS_EXIT_CRITICAL();
             /*@ flag_post_restore_output(environment, critical, sg, flag_post_entered(entry), mask,
                   cpu_sr, flag_post_acquired(entry), released, active_local,
                   flag_post_caller_frame(error_cell, old_error, F), captured)
                 which implies exists (returned : FlagPostExecution) (current : UCOS2_Verify_State)
                   (returned_local : Armv7aContinuation -> Assertion),
                 interrupt_saved_value(mask, cpu_sr) &&
                 flag_post_restore_relation(environment, critical, sg, flag_post_entered(entry), released, returned, current) &&
                 flag_post_source_closed(environment, returned_local, sg, returned, mask, current) *
                 data_at(error_cell, INT8U, old_error) * F
             */

                 *perr = OS_ERR_FLAG_WAIT_TYPE;
                 OS_TRACE_FLAG_POST_EXIT(*perr);
                 /*@ Assert flag_post_public_post(environment, sg, original, mask, error_cell, 0, F, X) *
            data_at(&pgrp, OS_FLAG_GRP *, pointer) * data_at(&flags, OS_FLAGS, requested) *
            data_at(&opt, INT8U, option_word) * data_at(&perr, INT8U *, error_cell) *
            undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&sched, BOOLEAN) *
            undef_data_at(&flags_cur, OS_FLAGS) * undef_data_at(&flags_rdy, OS_FLAGS) *
            undef_data_at(&rdy, BOOLEAN) * undef_data_at(&cpu_sr, OS_CPU_SR)
        */
        return ((OS_FLAGS)0);
        }
        /*@ Assert exists (pending : FlagPostPendingVisit),
            pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
            flag_post_parameters(sg, pointer, id, requested, option_word) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) && flag_post_next_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, pending, pnode, sched) *
            data_at(error_cell, INT8U, old_error) * F * undef_data_at(&flags_cur, OS_FLAGS) *
            undef_data_at(&flags_rdy, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
        */
        /*@ exists (pending : FlagPostPendingVisit), flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_next_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, pending, pnode, sched)
            which implies exists (pending : FlagPostPendingVisit) (next : Z),
            flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_next_is(pending, next) && data_at(&pnode->OSFlagNodeNext, void *, next) *
            flag_post_next_frame(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, pending, pnode, sched)
        */
        pnode = (OS_FLAG_NODE *)pnode->OSFlagNodeNext;
        /*@ Assert exists (context : FlagPostLoopContext),
        pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) && flag_post_loop_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, context, pnode, sched) *
        data_at(error_cell, INT8U, old_error) * F * undef_data_at(&flags_cur, OS_FLAGS) *
        undef_data_at(&flags_rdy, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
    */ /* Point to next task waiting for event flag(s) */
    }
    /*@ Assert exists (entry : FlagPostProtectedContext) (result : FlagPostProtectedResult)
                             (released : UCOS2_Verify_State) (active_local : Armv7aContinuation -> Assertion),
                 pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
                 flag_post_parameters(sg, pointer, id, requested, option_word) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) && flag_post_result_success(result, sched) && flag_post_exit_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry, result, released, active_local) *
                 data_at(error_cell, INT8U, old_error) * F * undef_data_at(&pnode, OS_FLAG_NODE *) *
                 undef_data_at(&flags_cur, OS_FLAGS) *
                 undef_data_at(&flags_rdy, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
             */
             /*@ Given entry result released active_local */
             /*@ flag_post_exit_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry, result, released, active_local) *
                 data_at(error_cell, INT8U, old_error) * F
                 which implies exists (captured : model),
                 flag_post_protected_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, entry) &&
                 flag_post_protected_run(sg, id, requested, option_word, flag_post_acquired(entry), result, released) &&
                 flag_post_restore_input(environment, critical, mask, active_local, sg,
                   flag_post_entered(entry), cpu_sr, flag_post_acquired(entry), released, flag_post_caller_frame(error_cell, old_error, F), captured)
             */
             /*@ Given captured */
             OS_EXIT_CRITICAL();
             /*@ flag_post_restore_output(environment, critical, sg, flag_post_entered(entry), mask,
                   cpu_sr, flag_post_acquired(entry), released, active_local,
                   flag_post_caller_frame(error_cell, old_error, F), captured)
                 which implies exists (returned : FlagPostExecution) (current : UCOS2_Verify_State)
                   (returned_local : Armv7aContinuation -> Assertion),
                 interrupt_saved_value(mask, cpu_sr) &&
                 flag_post_restore_relation(environment, critical, sg, flag_post_entered(entry), released, returned, current) &&
                 flag_post_source_closed(environment, returned_local, sg, returned, mask, current) *
                 data_at(error_cell, INT8U, old_error) * F
             */

    /*@ Assert exists (released_context : FlagPostReleasedContext),
        pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) && flag_post_success_result(released_context, sched) &&
        flag_post_restored_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, released_context) *
        data_at(error_cell, INT8U, old_error) * F * undef_data_at(&pnode, OS_FLAG_NODE *) *
        undef_data_at(&flags_cur, OS_FLAGS) * undef_data_at(&flags_rdy, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
    */
    /*@ Given released_context */
    if (sched == OS_TRUE) {
        /*@ flag_post_parameters(sg, pointer, id, requested, option_word) &&
            flag_post_execution_clients(critical, original) && sched == 1 &&
            flag_post_success_result(released_context, sched) &&
            flag_post_restored_cut(environment, critical, sg, pointer, id, requested, option_word,
              mask, original, before, cpu_sr, released_context)
            which implies
            flag_post_parameters(sg, pointer, id, requested, option_word) &&
            flag_post_execution_clients(critical, original) && sched == 1 &&
            flag_post_success_result(released_context, sched) &&
            flag_post_restored_facts(environment, critical, sg, pointer, id, requested, option_word,
              mask, original, before, cpu_sr, released_context) &&
            flag_post_scheduler_call_pre(environment, critical, flag_post_restored_local(released_context),
              sg, flag_post_released_execution(released_context), mask, flag_post_restored_state(released_context))
        */
        OS_Sched();
        /*@ flag_post_scheduler_call_post(environment, critical, flag_post_restored_local(released_context),
              sg, flag_post_released_execution(released_context), mask, flag_post_restored_state(released_context))
            which implies exists (returned : FlagPostExecution) (current : UCOS2_Verify_State)
              (returned_local : Armv7aContinuation -> Assertion),
            flag_post_scheduler_relation(environment, critical, sg, flag_post_released_execution(released_context),
              mask, flag_post_restored_state(released_context), returned, current) &&
            flag_post_source_closed(environment, returned_local, sg, returned, mask, current)
        */
    }
    /*@ Assert exists (prefix : FlagPostReleasedContext) (scheduled : FlagPostExecution)
                     (current : UCOS2_Verify_State) (current_local : Armv7aContinuation -> Assertion),
        pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) && flag_post_scheduled_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, cpu_sr, prefix, scheduled, current) &&
        flag_post_source_closed(environment, current_local, sg, scheduled, mask, current) *
        data_at(error_cell, INT8U, old_error) * F * undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&sched, BOOLEAN) *
        undef_data_at(&flags_cur, OS_FLAGS) * undef_data_at(&flags_rdy, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
    */
    /*@ Given prefix scheduled current current_local */
    /*@ flag_post_source_closed(environment, current_local, sg, scheduled, mask, current) * data_at(error_cell, INT8U, old_error) * F
        which implies exists (captured : model),
        flag_post_save_input(environment, critical, current_local, sg, scheduled, mask, current, flag_post_caller_frame(error_cell, old_error, F), captured)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (first_saved : Z) (read_context : FlagPostReadContext),
        pgrp == pointer && flags == requested && opt == option_word && perr == error_cell &&
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        kernel_sched_ready_clients(critical) && flag_post_execution_clients(critical, original) &&
        os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        &OSRdyGrp == g_OSRdyGrp(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
        flag_post_api_safe(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, X) && flag_post_read_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, first_saved, cpu_sr, read_context) *
        data_at(error_cell, INT8U, old_error) * F * undef_data_at(&pnode, OS_FLAG_NODE *) *
        undef_data_at(&sched, BOOLEAN) * undef_data_at(&flags_cur, OS_FLAGS) *
        undef_data_at(&flags_rdy, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN)
    */
    /*@ exists (first_saved : Z) (read_context : FlagPostReadContext),
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_read_cut(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, first_saved, cpu_sr, read_context) * data_at(&pgrp, OS_FLAG_GRP *, pointer)
        which implies exists (first_saved : Z) (read_context : FlagPostReadContext),
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_read_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, first_saved, cpu_sr, read_context) &&
        data_at(&pgrp, OS_FLAG_GRP *, pointer) * data_at(&(pgrp->OSFlagFlags), OS_FLAGS, flagImageBits(flag_post_read_image(read_context))) *
        flag_post_current_word_frame(sg, flag_post_read_state(read_context), id, flag_post_read_image(read_context)) *
        flag_post_critical_frame(environment, critical, flag_post_read_local(read_context), sg,
          flag_post_reader(read_context), cpu_sr, flag_post_read_state(read_context), flag_post_read_state(read_context))
    */
    /*@ Given first_saved read_context */
    flags_cur = pgrp->OSFlagFlags;
    /*@
        flags_cur == flagImageBits(flag_post_read_image(read_context)) &&
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_read_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, first_saved, cpu_sr, read_context) &&
        data_at(&pgrp, OS_FLAG_GRP *, pointer) * data_at(&(pgrp->OSFlagFlags), OS_FLAGS, flags_cur) *
        flag_post_current_word_frame(sg, flag_post_read_state(read_context), id, flag_post_read_image(read_context)) *
        flag_post_critical_frame(environment, critical, flag_post_read_local(read_context), sg,
          flag_post_reader(read_context), cpu_sr, flag_post_read_state(read_context), flag_post_read_state(read_context))
        * data_at(error_cell, INT8U, old_error) * F
        which implies exists (read_captured : model),
        flag_post_parameters(sg, pointer, id, requested, option_word) &&
        flag_post_read_facts(environment, critical, sg, pointer, id, requested, option_word, mask, original, before, first_saved, cpu_sr, read_context) &&
        flags_cur == flagImageBits(flag_post_read_image(read_context)) &&
        flag_post_restore_input(environment, critical, mask, flag_post_read_local(read_context), sg,
          flag_post_reader(read_context), cpu_sr, flag_post_read_state(read_context), flag_post_read_state(read_context), flag_post_caller_frame(error_cell, old_error, F), read_captured) * data_at(&pgrp, OS_FLAG_GRP *, pointer)
    */
    /*@ Given read_captured */
    OS_EXIT_CRITICAL();
    /*@ flag_post_restore_output(environment, critical, sg, flag_post_reader(read_context), mask,
          cpu_sr, flag_post_read_state(read_context), flag_post_read_state(read_context), flag_post_read_local(read_context),
          flag_post_caller_frame(error_cell, old_error, F), read_captured)
        which implies exists (returned : FlagPostExecution) (current : UCOS2_Verify_State)
          (returned_local : Armv7aContinuation -> Assertion),
        interrupt_saved_value(mask, cpu_sr) &&
        flag_post_restore_relation(environment, critical, sg, flag_post_reader(read_context),
          flag_post_read_state(read_context), returned, current) &&
        flag_post_source_closed(environment, returned_local, sg, returned, mask, current) *
        data_at(error_cell, INT8U, old_error) * F
    */
    *perr     = OS_ERR_NONE;
    OS_TRACE_FLAG_POST_EXIT(*perr);

    /*@ Assert flag_post_public_post(environment, sg, original, mask, error_cell, flags_cur, F, X) *
            data_at(&pgrp, OS_FLAG_GRP *, pointer) * data_at(&flags, OS_FLAGS, requested) *
            data_at(&opt, INT8U, option_word) * data_at(&perr, INT8U *, error_cell) *
        undef_data_at(&pnode, OS_FLAG_NODE *) * undef_data_at(&sched, BOOLEAN) *
        undef_data_at(&flags_rdy, OS_FLAGS) * undef_data_at(&rdy, BOOLEAN) * undef_data_at(&cpu_sr, OS_CPU_SR)
    */
    return (flags_cur);
}
