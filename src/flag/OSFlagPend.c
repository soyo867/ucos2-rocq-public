/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

OS_FLAGS  OSFlagPend (OS_FLAG_GRP  *pgrp,
                      OS_FLAGS      flags,
                      INT8U         wait_type,
                      INT32U        timeout,
                      INT8U        *perr)
/*@ With (base_environment : TaskStackCallEnvironment) (local : Armv7aContinuation -> Assertion)
         (critical : CriticalRegionResources) (entry_boundary : PendPhaseCandidate::FlagPendEntryBoundary) (sg : StableGlobVars)
         (caller : FlagPendCaller) (call : OsSchedCallContext) (mask : Z) (before : UCOS2_Verify_State)
         (i pgrp0 requested original_mode delay errp : Z) X (F : Assertion)
    Require pgrp == pgrp0 && flags == requested && wait_type == original_mode &&
            timeout == delay && perr == errp &&
            PendPhaseCandidate::flag_pend_source_layout && kernel_sched_ready_clients(critical) &&
            PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
            FlagPendInactiveSelectedInput::flag_pend_selected_owned_input(task_sw_hook_call_environment(base_environment), critical, entry_boundary, local, sg, caller, call,
              mask, i, pgrp0, requested, original_mode, delay, errp, before, X, F)
    Ensure PendPhaseCandidate::flag_pend_public_post(task_sw_hook_call_environment(base_environment), local, sg, caller, call, mask, errp,
             before, __return, X) * F
*/

{
    OS_FLAG_NODE  node;
    OS_FLAGS      flags_rdy;
    INT8U         result;
    INT8U         pend_stat;
    BOOLEAN       consume;
#if OS_CRITICAL_METHOD == 3u                               /* Allocate storage for CPU status register */
    OS_CPU_SR     cpu_sr = 0u;
#endif


    /*@ perr == errp && FlagPendInactiveSelectedInput::flag_pend_selected_owned_input(task_sw_hook_call_environment(base_environment), critical, entry_boundary, local, sg, caller, call,
          mask, i, pgrp0, requested, original_mode, delay, errp, before, X, F)
        which implies
        FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_caller_world(task_sw_hook_call_environment(base_environment), local, sg, caller, mask, before) *
        undef_data_at(perr, INT8U) * F
    */

#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return ((OS_FLAGS)0);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pgrp == (OS_FLAG_GRP *)0) {                        /* Validate 'pgrp'                          */
        *perr = OS_ERR_FLAG_INVALID_PGRP;
        return ((OS_FLAGS)0);
    }
#endif

    OS_TRACE_FLAG_PEND_ENTER(pgrp, flags, timeout, wait_type);

    /*@ FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_source_layout &&
        PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
        PendPhaseCandidate::flag_pend_caller_world(task_sw_hook_call_environment(base_environment), local, sg, caller, mask, before)
        which implies
         0 <= os_sched_ints(before) && os_sched_ints(before) < 256 &&
         0 <= os_sched_locks(before) && os_sched_locks(before) < 256 &&
        PendPhaseCandidate::flag_pend_caller_control(task_sw_hook_call_environment(base_environment), local, sg, caller, mask, before) *
        data_at(&OSIntNesting, INT8U, os_sched_ints(before)) *
        data_at(&OSLockNesting, INT8U, os_sched_locks(before)) *
        PendPhaseCandidate::flag_pend_counter_frame(sg, before)
    */
    if (OSIntNesting > 0u) {                               /* See if called from ISR ...               */
    /*@ FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_source_layout &&
        PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
        PendPhaseCandidate::flag_pend_caller_control(task_sw_hook_call_environment(base_environment), local, sg, caller, mask, before) *
        data_at(&OSIntNesting, INT8U, os_sched_ints(before)) *
        data_at(&OSLockNesting, INT8U, os_sched_locks(before)) *
        PendPhaseCandidate::flag_pend_counter_frame(sg, before)
        which implies PendPhaseCandidate::flag_pend_caller_world(task_sw_hook_call_environment(base_environment), local, sg, caller, mask, before)
    */
        *perr = OS_ERR_PEND_ISR;                           /* ... can't PEND from an ISR               */
        OS_TRACE_FLAG_PEND_EXIT(*perr);
        return ((OS_FLAGS)0);
    }
    if (OSLockNesting > 0u) {                              /* See if called with scheduler locked ...  */
    /*@ FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_source_layout &&
        PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
        PendPhaseCandidate::flag_pend_caller_control(task_sw_hook_call_environment(base_environment), local, sg, caller, mask, before) *
        data_at(&OSIntNesting, INT8U, os_sched_ints(before)) *
        data_at(&OSLockNesting, INT8U, os_sched_locks(before)) *
        PendPhaseCandidate::flag_pend_counter_frame(sg, before)
        which implies PendPhaseCandidate::flag_pend_caller_world(task_sw_hook_call_environment(base_environment), local, sg, caller, mask, before)
    */
        *perr = OS_ERR_PEND_LOCKED;                        /* ... can't PEND when locked               */
        OS_TRACE_FLAG_PEND_EXIT(*perr);
        return ((OS_FLAGS)0);
    }
    /*@ FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_source_layout &&
        PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
        PendPhaseCandidate::flag_pend_caller_control(task_sw_hook_call_environment(base_environment), local, sg, caller, mask, before) *
        data_at(&OSIntNesting, INT8U, os_sched_ints(before)) *
        data_at(&OSLockNesting, INT8U, os_sched_locks(before)) *
        PendPhaseCandidate::flag_pend_counter_frame(sg, before)
        which implies PendPhaseCandidate::flag_pend_caller_world(task_sw_hook_call_environment(base_environment), local, sg, caller, mask, before)
    */
    /*@ pgrp0 != 0 && FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_source_layout &&
        PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
        PendPhaseCandidate::flag_pend_caller_world(task_sw_hook_call_environment(base_environment), local, sg, caller, mask, before) *
        data_at(&pgrp, OS_FLAG_GRP *, pgrp0)
        which implies exists (observed : FlagGroupImage),
        PendPhaseCandidate::flag_pend_group_lookup(before, i, observed) && UCOS2_state_inv(sg, before) &&
        data_at(&pgrp, OS_FLAG_GRP *, pgrp0) *
        PendPhaseCandidate::flag_pend_caller_control(task_sw_hook_call_environment(base_environment), local, sg, caller, mask, before) *
        data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(observed)) *
        data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(observed)) *
        PendPhaseCandidate::flag_pend_group_frame(sg, before, i, observed)
    */
    /*@ Given observed */
    if (pgrp->OSFlagType != OS_EVENT_TYPE_FLAG) {          /* Validate event block type                */
    /*@ pgrp == pgrp0 && pgrp0 != 0 && FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_source_layout &&
        PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
        UCOS2_state_inv(sg, before) && PendPhaseCandidate::flag_pend_group_lookup(before, i, observed) &&
        PendPhaseCandidate::flag_pend_caller_control(task_sw_hook_call_environment(base_environment), local, sg, caller, mask, before) *
        data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(observed)) *
        data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(observed)) *
        PendPhaseCandidate::flag_pend_group_frame(sg, before, i, observed)
        which implies PendPhaseCandidate::flag_pend_caller_world(task_sw_hook_call_environment(base_environment), local, sg, caller, mask, before) *
        data_at(&pgrp, OS_FLAG_GRP *, pgrp0)
    */
        *perr = OS_ERR_EVENT_TYPE;
        OS_TRACE_FLAG_PEND_EXIT(*perr);
        return ((OS_FLAGS)0);
    }
    /*@ pgrp == pgrp0 && pgrp0 != 0 && FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_source_layout &&
        PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
        UCOS2_state_inv(sg, before) && PendPhaseCandidate::flag_pend_group_lookup(before, i, observed) &&
        PendPhaseCandidate::flag_pend_caller_control(task_sw_hook_call_environment(base_environment), local, sg, caller, mask, before) *
        data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(observed)) *
        data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(observed)) *
        PendPhaseCandidate::flag_pend_group_frame(sg, before, i, observed)
        which implies PendPhaseCandidate::flag_pend_caller_world(task_sw_hook_call_environment(base_environment), local, sg, caller, mask, before) *
        data_at(&pgrp, OS_FLAG_GRP *, pgrp0)
    */
    result = (INT8U)(wait_type & OS_FLAG_CONSUME);
    if (result != (INT8U)0) {                              /* See if we need to consume the flags      */
        wait_type &= (INT8U)~(INT8U)OS_FLAG_CONSUME;
        consume    = OS_TRUE;
    } else {
        consume    = OS_FALSE;
    }

    /*@ FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        pgrp0 != 0 && os_sched_ints(before) <= 0 && os_sched_locks(before) <= 0 &&
        PendPhaseCandidate::flag_pend_group_lookup(before, i, observed) && PendPhaseCandidate::flag_pend_group_type(observed) == 5 &&
        PendPhaseCandidate::flag_pend_caller_world(task_sw_hook_call_environment(base_environment), local, sg, caller, mask, before)
        which implies
        ((FlagPendActiveCallerControl::flag_pend_caller_counters_zero(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), caller, before) &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), before)) &&
        flag_pend_caller_save_input(task_sw_hook_call_environment(base_environment), critical, local, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before),
          sg, caller, call, mask, before))
    */
    /*@ ((FlagPendActiveCallerControl::flag_pend_caller_counters_zero(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), caller, before) &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), before)) &&
        flag_pend_caller_save_input(task_sw_hook_call_environment(base_environment), critical, local, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before),
          sg, caller, call, mask, before))
        which implies exists (first_heap : model),
        os_sched_active_heap_cut(flag_pend_caller_save_input(task_sw_hook_call_environment(base_environment), critical, local,
          PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, caller, call, mask, before), first_heap)
    */
    /*@ Given first_heap */
    cpu_sr = OS_CPU_SR_Save()
        /*@ where environment=task_sw_hook_call_environment(base_environment),
          critical=critical,
          local=local,
          active=PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before),
          sg=sg,
           caller=caller,
          call=call,
          mask=mask,
          before=before,
          entry_heap=first_heap */;
    /*@ pgrp0 != 0 && os_sched_ints(before) <= 0 && os_sched_locks(before) <= 0 &&
        PendPhaseCandidate::flag_pend_group_lookup(before, i, observed) &&
        PendPhaseCandidate::flag_pend_group_type(observed) == 5 &&
        FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_source_layout &&
        PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), before) &&
        FlagPendActiveCaller::flag_pend_selected_caller_save_output(task_sw_hook_call_environment(base_environment), critical, local, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before),
          sg, caller, call, mask, before, first_heap, cpu_sr)
        which implies exists (entered_caller : FlagPendCaller) (entered : OsSchedCallContext) (acquired : UCOS2_Verify_State)
                             (acquired_local : Armv7aContinuation -> Assertion),
        FlagPendActiveCaller::flag_pend_caller_save_observation(task_sw_hook_call_environment(base_environment), critical, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, caller, call, entered_caller, entered, mask, cpu_sr, before, acquired) &&
        FlagPendActiveCaller::flag_pend_caller_endpoint_observations(task_sw_hook_call_environment(base_environment), PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, caller, call, before, entered, acquired) &&
        interrupt_saved_value(mask, cpu_sr) &&
        PendPhaseCandidate::flag_pend_first_registration(original_mode, call, before, entered, acquired) &&
        ((FlagPendActiveCallerControl::flag_pend_caller_counters_zero(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), entered_caller, acquired) &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), acquired)) &&
        PendPhaseCandidate::flag_pend_caller_fields_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local, sg,
          entered_caller, entered, cpu_sr, acquired, acquired))
    */
    /*@ Given entered_caller entered acquired acquired_local */
    /*@ pgrp0 != 0 && FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_source_layout &&
        PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
        ((FlagPendActiveCallerControl::flag_pend_caller_counters_zero(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), entered_caller, acquired) &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), acquired)) &&
        PendPhaseCandidate::flag_pend_caller_fields_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local, sg, entered_caller,
          entered, cpu_sr, acquired, acquired)) *
        data_at(&pgrp, OS_FLAG_GRP *, pgrp0)
        which implies exists (protected_image : FlagGroupImage),
        PendPhaseCandidate::flag_pend_group_lookup(acquired, i, protected_image) && UCOS2_state_inv(sg, acquired) &&
        data_at(&pgrp, OS_FLAG_GRP *, pgrp0) *
        PendPhaseCandidate::flag_pend_caller_masked_control(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg, entered_caller, entered, cpu_sr, acquired, acquired) *
        data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
        data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
        PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
    */
    /*@ Given protected_image */
    /* A task may delete the group before this first protected observation. */
    if (((wait_type == OS_FLAG_WAIT_SET_ALL) || (wait_type == OS_FLAG_WAIT_SET_ANY)
#if OS_FLAG_WAIT_CLR_EN > 0u
         || (wait_type == OS_FLAG_WAIT_CLR_ALL) || (wait_type == OS_FLAG_WAIT_CLR_ANY)
#endif
        ) && (pgrp->OSFlagType != OS_EVENT_TYPE_FLAG)) {
        /*@ PendPhaseCandidate::flag_pend_valid_mode(original_mode) &&
                pgrp0 != 0 && os_sched_ints(before) <= 0 && os_sched_locks(before) <= 0 &&
                PendPhaseCandidate::flag_pend_group_lookup(before, i, observed) &&
                PendPhaseCandidate::flag_pend_group_type(observed) == 5 &&
                interrupt_saved_value(mask, cpu_sr) &&
                FlagPendActiveCaller::flag_pend_caller_save_observation(task_sw_hook_call_environment(base_environment), critical, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, caller, call, entered_caller, entered, mask, cpu_sr, before, acquired) &&
                FlagPendActiveCaller::flag_pend_caller_endpoint_observations(task_sw_hook_call_environment(base_environment), PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, caller, call, before, entered, acquired) &&
                PendPhaseCandidate::flag_pend_caller_masked_control(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                  entered_caller, entered, cpu_sr, acquired, acquired) *
                data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
                data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
                PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                which implies
                FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
                PendPhaseCandidate::flag_pend_caller_save_observation(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, entered_caller, entered, mask, cpu_sr, before, acquired) &&
                PendPhaseCandidate::flag_pend_call_source_observations(task_sw_hook_call_environment(base_environment), sg, caller, call, before, entered, acquired) &&
                PendPhaseCandidate::flag_pend_caller_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, before, i, pgrp0, entered_caller, entered, cpu_sr, acquired) &&
                PendPhaseCandidate::flag_pend_caller_masked_control(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                  entered_caller, entered, cpu_sr, acquired, acquired) *
                data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
                data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
                PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
            */
        /*@ pgrp == pgrp0 && pgrp0 != 0 && FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_source_layout &&
        PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
        UCOS2_state_inv(sg, acquired) &&
             FlagPendActiveCallerControl::flag_pend_caller_counters_zero(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), entered_caller, acquired) &&
             FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), acquired) &&
             PendPhaseCandidate::flag_pend_group_lookup(acquired, i, protected_image) &&
            PendPhaseCandidate::flag_pend_caller_masked_control(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg, entered_caller,
              entered, cpu_sr, acquired, acquired) *
            data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
            data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
            PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
            which implies
            ((FlagPendActiveCallerControl::flag_pend_caller_counters_zero(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), entered_caller, acquired) &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), acquired)) &&
        PendPhaseCandidate::flag_pend_caller_fields_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local, sg, entered_caller,
              entered, cpu_sr, acquired, acquired)) *
            data_at(&pgrp, OS_FLAG_GRP *, pgrp0)
        */
        /*@ PendPhaseCandidate::flag_pend_first_registration(original_mode, call, before, entered, acquired) &&
            ((FlagPendActiveCallerControl::flag_pend_caller_counters_zero(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), entered_caller, acquired) &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), acquired)) &&
        PendPhaseCandidate::flag_pend_caller_fields_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local, sg, entered_caller,
              entered, cpu_sr, acquired, acquired))
            which implies exists (release_heap : model),
            os_sched_active_heap_cut(flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
              PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, entered_caller, entered, cpu_sr, acquired, acquired), release_heap)
        */
        /*@ Given release_heap */
        OS_CPU_SR_Restore(cpu_sr)
        /*@ where environment=task_sw_hook_call_environment(base_environment),
          critical=critical,
          local=acquired_local,
          active=PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before),
          sg=sg,
           caller=entered_caller,
          call=entered,
          saved=cpu_sr,
          acquired=acquired,
          released=acquired,
          release_heap=release_heap */;
    /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
        FlagPendActiveCaller::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, entered_caller, entered, cpu_sr, acquired, acquired, release_heap)
        which implies
        SelectedCallerPhaseComponent::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, entered_caller, entered, cpu_sr, acquired, acquired, release_heap)
    */
        *perr = OS_ERR_EVENT_TYPE;
        OS_TRACE_FLAG_PEND_EXIT(*perr);
        return ((OS_FLAGS)0);
    }
    /* The completed revalidation branches share this protected observation. */
    /*@ Assert exists (joined_saved joined_mode joined_consume joined_result : Z),
        PendPhaseCandidate::flag_pend_source_layout && kernel_sched_ready_clients(critical) &&
        PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
        FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        pgrp0 != 0 && os_sched_ints(before) <= 0 && os_sched_locks(before) <= 0 &&
        UCOS2_state_inv(sg, before) &&
        PendPhaseCandidate::flag_pend_group_lookup(before, i, observed) && PendPhaseCandidate::flag_pend_group_type(observed) == 5 &&
        FlagPendActiveCaller::flag_pend_caller_save_observation(task_sw_hook_call_environment(base_environment), critical, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, caller, call, entered_caller, entered, mask, joined_saved, before, acquired) &&
        FlagPendActiveCaller::flag_pend_caller_endpoint_observations(task_sw_hook_call_environment(base_environment), PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, caller, call, before, entered, acquired) &&
        interrupt_saved_value(mask, joined_saved) &&
        PendPhaseCandidate::flag_pend_first_registration(original_mode, call, before, entered, acquired) &&
        FlagPendActiveCallerControl::flag_pend_caller_counters_zero(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), entered_caller, acquired) &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), acquired) &&
        UCOS2_state_inv(sg, acquired) && PendPhaseCandidate::flag_pend_group_lookup(acquired, i, protected_image) &&
        PendPhaseCandidate::flag_pend_mode_parameters(original_mode, joined_mode, joined_consume) &&
        ((joined_mode != 0 && joined_mode != 1 && joined_mode != 2 && joined_mode != 3) ||
          PendPhaseCandidate::flag_pend_group_type(protected_image) == 5) &&
        pgrp == pgrp0 && flags == requested && wait_type == joined_mode &&
        timeout == delay && perr == errp && cpu_sr == joined_saved &&
        consume == joined_consume && result == joined_result &&
        PendPhaseCandidate::flag_pend_caller_masked_control(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg, entered_caller,
          entered, joined_saved, acquired, acquired) *
        data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
        data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
        PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image) *
        undef_data_at(&pend_stat, INT8U) * undef_data_at(&flags_rdy, OS_FLAGS) *
        undef_data_at(&node, OS_FLAG_NODE) * undef_data_at(perr, INT8U) * F
    */
    /*@ Given joined_saved joined_mode joined_consume joined_result */
    switch (wait_type) {
        case OS_FLAG_WAIT_SET_ALL:                         /* See if all required flags are set        */
             /*@ PendPhaseCandidate::flag_pend_valid_mode(original_mode) &&
                     pgrp0 != 0 && os_sched_ints(before) <= 0 && os_sched_locks(before) <= 0 &&
                     PendPhaseCandidate::flag_pend_group_lookup(before, i, observed) &&
                     PendPhaseCandidate::flag_pend_group_type(observed) == 5 &&
                     interrupt_saved_value(mask, joined_saved) &&
                     FlagPendActiveCaller::flag_pend_caller_save_observation(task_sw_hook_call_environment(base_environment), critical, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, caller, call, entered_caller, entered, mask, joined_saved, before, acquired) &&
                     FlagPendActiveCaller::flag_pend_caller_endpoint_observations(task_sw_hook_call_environment(base_environment), PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, caller, call, before, entered, acquired) &&
                     PendPhaseCandidate::flag_pend_caller_masked_control(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                       entered_caller, entered, joined_saved, acquired, acquired) *
                     data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
                     data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
                     PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                     which implies
                     FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
                     PendPhaseCandidate::flag_pend_caller_save_observation(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, entered_caller, entered, mask, joined_saved, before, acquired) &&
                     PendPhaseCandidate::flag_pend_call_source_observations(task_sw_hook_call_environment(base_environment), sg, caller, call, before, entered, acquired) &&
                     PendPhaseCandidate::flag_pend_caller_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, before, i, pgrp0, entered_caller, entered, joined_saved, acquired) &&
                     PendPhaseCandidate::flag_pend_caller_masked_control(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                       entered_caller, entered, joined_saved, acquired, acquired) *
                     data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
                     data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
                     PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                 */
             flags_rdy = (OS_FLAGS)(pgrp->OSFlagFlags & flags);   /* Extract only the bits we want     */
             if (flags_rdy == flags) {                     /* Must match ALL the bits that we want     */
                 if (consume == OS_TRUE) {                 /* See if we need to consume the flags      */
                     pgrp->OSFlagFlags &= (OS_FLAGS)~flags_rdy;   /* Clear ONLY the flags we wanted    */
                 }
                 /*@ FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     pgrp0 != 0 && os_sched_ints(before) <= 0 && os_sched_locks(before) <= 0 &&
                     PendPhaseCandidate::flag_pend_group_lookup(before, i, observed) && PendPhaseCandidate::flag_pend_group_type(observed) == 5 &&
                     PendPhaseCandidate::flag_pend_source_layout && PendPhaseCandidate::flag_pend_valid_mode(original_mode) &&
                     task_tcb_init_stack_source_preserved(call, before, acquired) &&
                     task_tcb_init_stack_same_call(entered, call) &&
                     PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                       &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                       &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
                     PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                     which implies exists (current_tid : Z) (current_task : TaskAbstractState),
                     PendPhaseCandidate::flag_pend_current_binding(acquired, current_tid, current_task) &&
                     data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, current_tid)) *
                     data_at(field_addr(task_slot_addr(sg, current_tid), OS_TCB, OSTCBFlagsRdy),
                       OS_FLAGS, tcbFlagsRdy(current_task)) *
                     PendPhaseCandidate::flag_pend_group_current_frame(sg, acquired, current_tid, current_task, i, protected_image)
                 */
                 /*@ Given current_tid current_task */
                 OSTCBCur->OSTCBFlagsRdy = flags_rdy;      /* Save flags that were ready               */
                 /*@ Assert exists (released : UCOS2_Verify_State)
                       (ready saved normalized original_result consumed : Z),
                     FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     PendPhaseCandidate::flag_pend_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask,
                       before, i, pgrp0, entered, saved, acquired) &&
                     PendPhaseCandidate::flag_pend_first_return(sg, i, requested, original_mode, delay,
                       acquired, ready, 0, released) &&
                     entered_caller == FlagPendTaskCaller(entered) &&
                     PendPhaseCandidate::flag_pend_task_stage(entered, released) &&
                     FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
                     PendPhaseCandidate::flag_pend_first_registration(original_mode, call, before, entered, released) &&
                     pgrp == pgrp0 && flags == requested && wait_type == normalized &&
                     timeout == delay && perr == errp && flags_rdy == ready &&
                     cpu_sr == saved && result == original_result && consume == consumed &&
                     ((os_sched_ints(released) == 0 && os_sched_locks(released) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), released)) &&
        PendPhaseCandidate::flag_pend_caller_fields_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local, sg, entered_caller,
                       entered, saved, acquired, released)) *
                     undef_data_at(&pend_stat, INT8U) * undef_data_at(&node, OS_FLAG_NODE) *
                     undef_data_at(perr, INT8U) * F
                 */
                 /*@ Given released ready saved normalized original_result consumed */
                 /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
                     PendPhaseCandidate::flag_pend_first_registration(original_mode, call, before, entered, released) &&
                     ((os_sched_ints(released) == 0 && os_sched_locks(released) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), released)) &&
        PendPhaseCandidate::flag_pend_caller_fields_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local, sg, entered_caller,
                       entered, saved, acquired, released))
                     which implies exists (release_heap : model),
                     os_sched_active_heap_cut(flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                       PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, entered_caller, entered, saved, acquired, released), release_heap)
                 */
                 /*@ Given release_heap */
                 OS_CPU_SR_Restore(cpu_sr)
        /*@ where environment=task_sw_hook_call_environment(base_environment),
          critical=critical,
          local=acquired_local,
          active=PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before),
          sg=sg,
           caller=entered_caller,
          call=entered,
          saved=saved,
          acquired=acquired,
          released=released,
          release_heap=release_heap */;
    /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
        FlagPendActiveCaller::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, entered_caller, entered, saved, acquired, released, release_heap)
        which implies
        SelectedCallerPhaseComponent::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, entered_caller, entered, saved, acquired, released, release_heap)
    */                       /* Yes, condition met, return to caller     */
                 *perr                   = OS_ERR_NONE;
                 OS_TRACE_FLAG_PEND_EXIT(*perr);
                 return (flags_rdy);
             } else {                                      /* Block task until events occur or timeout */
                 /*@ pgrp == pgrp0 && FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     pgrp0 != 0 && PendPhaseCandidate::flag_pend_source_layout &&
                     UCOS2_state_inv(sg, acquired) &&
                     PendPhaseCandidate::flag_pend_group_lookup(acquired, i, protected_image) &&
                     data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
                     data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
                     PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                     which implies
                     UCOS2_fields_inv(sg, acquired) * data_at(&pgrp, OS_FLAG_GRP *, pgrp0)
                 */
                 /*@ undef_data_at(&node, OS_FLAG_NODE)
                     which implies
                     undef_data_at(&(node.OSFlagNodeNext), void *) *
                     undef_data_at(&(node.OSFlagNodePrev), void *) *
                     undef_data_at(&(node.OSFlagNodeTCB), void *) *
                     undef_data_at(&(node.OSFlagNodeFlagGrp), void *) *
                     undef_data_at(&(node.OSFlagNodeFlags), OS_FLAGS) *
                     undef_data_at(&(node.OSFlagNodeWaitType), INT8U)
                 */
                 /*@ PendPhaseCandidate::flag_pend_source_layout &&
                     undef_data_at(&(node.OSFlagNodeNext), void *) *
                     undef_data_at(&(node.OSFlagNodePrev), void *) *
                     undef_data_at(&(node.OSFlagNodeTCB), void *) *
                     undef_data_at(&(node.OSFlagNodeFlagGrp), void *) *
                     undef_data_at(&(node.OSFlagNodeFlags), OS_FLAGS) *
                     undef_data_at(&(node.OSFlagNodeWaitType), INT8U)
                     which implies PendPhaseCandidate::flag_pend_node_fields(&node)
                 */
                 /*@ Assert exists (waiter : FlagWaiterState) (old_task : TaskAbstractState)
                                   (group : FlagGroupState)
                                   (saved normalized consumed original_result ready_seen : Z),
                     PendPhaseCandidate::flag_pend_source_layout && kernel_sched_ready_clients(critical) &&
                     PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                       &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                       &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
                     FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     PendPhaseCandidate::flag_pend_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask,
                       before, i, pgrp0, entered, saved, acquired) &&
                     PendPhaseCandidate::flag_pend_block_source_facts(sg, call, entered, acquired) &&
                     PendPhaseCandidate::flag_pend_first_unsatisfied(sg, protected_image, requested, original_mode) &&
                     PendPhaseCandidate::flag_pend_block_binding(sg, call, entered, acquired, i, &node, requested,
                       normalized, delay, waiter, old_task, group, protected_image) &&
                     PendPhaseCandidate::flag_pend_mode_parameters(original_mode, normalized, consumed) &&
                     pgrp == pgrp0 && flags == requested && wait_type == normalized &&
                     timeout == delay && perr == errp && cpu_sr == saved &&
                     consume == consumed && result == original_result && flags_rdy == ready_seen &&
                     pgrp == flag_block_call_group(sg, waiter) &&
                     &node == flag_block_call_node(waiter) &&
                     flags == flag_block_call_mask(waiter) &&
                     wait_type == flag_block_call_mode(waiter) &&
                     &OSTCBCur == g_OSTCBCur(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
                     &OSRdyGrp == g_OSRdyGrp(sg) &&
                     flag_block_call_fields_pre(sg, acquired, waiter, old_task, group, protected_image, delay) *
                      PendPhaseCandidate::flag_pend_block_callee_frame(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                        entered, saved, acquired, &pend_stat, perr, F)
                 */
                 /*@ Given waiter old_task group saved normalized consumed original_result ready_seen */
                 OS_FlagBlock(pgrp, &node, flags, wait_type, timeout)
                 /*@ where sg=sg, s=acquired, w=waiter, t=old_task, g=group,
                     v=protected_image, delay=delay,
                     F=PendPhaseCandidate::flag_pend_block_callee_frame(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                          entered, saved, acquired, &pend_stat, perr, F) */;
                 /*@ Assert exists (blocked : UCOS2_Verify_State),
                     PendPhaseCandidate::flag_pend_source_layout && kernel_sched_ready_clients(critical) &&
                     PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                       &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                       &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
                     FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     PendPhaseCandidate::flag_pend_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask,
                       before, i, pgrp0, entered, saved, acquired) &&
                     PendPhaseCandidate::flag_pend_first_waiting(sg, i, requested, original_mode, delay, acquired, &node, blocked) &&
                     PendPhaseCandidate::flag_pend_running_available(entered, blocked) &&
                     PendPhaseCandidate::flag_pend_mode_parameters(original_mode, normalized, consumed) &&
                     pgrp == pgrp0 && flags == requested && wait_type == normalized &&
                     timeout == delay && perr == errp && cpu_sr == saved &&
                     consume == consumed && result == original_result && flags_rdy == ready_seen &&
                     ((os_sched_ints(blocked) == 0 && os_sched_locks(blocked) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), blocked)) &&
        flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                       PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked)) * undef_data_at(&pend_stat, INT8U) *
                     undef_data_at(perr, INT8U) * F
                 */
                 /*@ Given blocked */
                 /*@ ((os_sched_ints(blocked) == 0 && os_sched_locks(blocked) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), blocked)) &&
        flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                       PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked))
                     which implies exists (release_heap : model),
                     os_sched_active_heap_cut(flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                       PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked), release_heap)
                 */
                 /*@ Given release_heap */
                 OS_CPU_SR_Restore(cpu_sr)
        /*@ where environment=task_sw_hook_call_environment(base_environment),
          critical=critical,
          local=acquired_local,
          active=PendPhaseCandidate::flag_pend_wait_active(sg, call, &node),
          sg=sg,
           caller=FlagPendTaskCaller(entered),
          call=entered,
          saved=saved,
          acquired=acquired,
          released=blocked,
          release_heap=release_heap */;
    /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_wait_active(sg, call, &node)) &&
        FlagPendActiveCaller::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked, release_heap)
        which implies
        SelectedCallerPhaseComponent::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked, release_heap)
    */
             }
             break;

        case OS_FLAG_WAIT_SET_ANY:
             /*@ PendPhaseCandidate::flag_pend_valid_mode(original_mode) &&
                     pgrp0 != 0 && os_sched_ints(before) <= 0 && os_sched_locks(before) <= 0 &&
                     PendPhaseCandidate::flag_pend_group_lookup(before, i, observed) &&
                     PendPhaseCandidate::flag_pend_group_type(observed) == 5 &&
                     interrupt_saved_value(mask, joined_saved) &&
                     FlagPendActiveCaller::flag_pend_caller_save_observation(task_sw_hook_call_environment(base_environment), critical, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, caller, call, entered_caller, entered, mask, joined_saved, before, acquired) &&
                     FlagPendActiveCaller::flag_pend_caller_endpoint_observations(task_sw_hook_call_environment(base_environment), PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, caller, call, before, entered, acquired) &&
                     PendPhaseCandidate::flag_pend_caller_masked_control(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                       entered_caller, entered, joined_saved, acquired, acquired) *
                     data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
                     data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
                     PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                     which implies
                     FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
                     PendPhaseCandidate::flag_pend_caller_save_observation(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, entered_caller, entered, mask, joined_saved, before, acquired) &&
                     PendPhaseCandidate::flag_pend_call_source_observations(task_sw_hook_call_environment(base_environment), sg, caller, call, before, entered, acquired) &&
                     PendPhaseCandidate::flag_pend_caller_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, before, i, pgrp0, entered_caller, entered, joined_saved, acquired) &&
                     PendPhaseCandidate::flag_pend_caller_masked_control(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                       entered_caller, entered, joined_saved, acquired, acquired) *
                     data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
                     data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
                     PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                 */
             flags_rdy = (OS_FLAGS)(pgrp->OSFlagFlags & flags);    /* Extract only the bits we want    */
             if (flags_rdy != (OS_FLAGS)0) {               /* See if any flag set                      */
                 if (consume == OS_TRUE) {                 /* See if we need to consume the flags      */
                     pgrp->OSFlagFlags &= (OS_FLAGS)~flags_rdy;    /* Clear ONLY the flags that we got */
                 }
                 /*@ FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     pgrp0 != 0 && os_sched_ints(before) <= 0 && os_sched_locks(before) <= 0 &&
                     PendPhaseCandidate::flag_pend_group_lookup(before, i, observed) && PendPhaseCandidate::flag_pend_group_type(observed) == 5 &&
                     PendPhaseCandidate::flag_pend_source_layout && PendPhaseCandidate::flag_pend_valid_mode(original_mode) &&
                     task_tcb_init_stack_source_preserved(call, before, acquired) &&
                     task_tcb_init_stack_same_call(entered, call) &&
                     PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                       &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                       &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
                     PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                     which implies exists (current_tid : Z) (current_task : TaskAbstractState),
                     PendPhaseCandidate::flag_pend_current_binding(acquired, current_tid, current_task) &&
                     data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, current_tid)) *
                     data_at(field_addr(task_slot_addr(sg, current_tid), OS_TCB, OSTCBFlagsRdy),
                       OS_FLAGS, tcbFlagsRdy(current_task)) *
                     PendPhaseCandidate::flag_pend_group_current_frame(sg, acquired, current_tid, current_task, i, protected_image)
                 */
                 /*@ Given current_tid current_task */
                 OSTCBCur->OSTCBFlagsRdy = flags_rdy;      /* Save flags that were ready               */
                 /*@ Assert exists (released : UCOS2_Verify_State)
                       (ready saved normalized original_result consumed : Z),
                     FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     PendPhaseCandidate::flag_pend_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask,
                       before, i, pgrp0, entered, saved, acquired) &&
                     PendPhaseCandidate::flag_pend_first_return(sg, i, requested, original_mode, delay,
                       acquired, ready, 0, released) &&
                     entered_caller == FlagPendTaskCaller(entered) &&
                     PendPhaseCandidate::flag_pend_task_stage(entered, released) &&
                     FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
                     PendPhaseCandidate::flag_pend_first_registration(original_mode, call, before, entered, released) &&
                     pgrp == pgrp0 && flags == requested && wait_type == normalized &&
                     timeout == delay && perr == errp && flags_rdy == ready &&
                     cpu_sr == saved && result == original_result && consume == consumed &&
                     ((os_sched_ints(released) == 0 && os_sched_locks(released) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), released)) &&
        PendPhaseCandidate::flag_pend_caller_fields_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local, sg, entered_caller,
                       entered, saved, acquired, released)) *
                     undef_data_at(&pend_stat, INT8U) * undef_data_at(&node, OS_FLAG_NODE) *
                     undef_data_at(perr, INT8U) * F
                 */
                 /*@ Given released ready saved normalized original_result consumed */
                 /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
                     PendPhaseCandidate::flag_pend_first_registration(original_mode, call, before, entered, released) &&
                     ((os_sched_ints(released) == 0 && os_sched_locks(released) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), released)) &&
        PendPhaseCandidate::flag_pend_caller_fields_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local, sg, entered_caller,
                       entered, saved, acquired, released))
                     which implies exists (release_heap : model),
                     os_sched_active_heap_cut(flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                       PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, entered_caller, entered, saved, acquired, released), release_heap)
                 */
                 /*@ Given release_heap */
                 OS_CPU_SR_Restore(cpu_sr)
        /*@ where environment=task_sw_hook_call_environment(base_environment),
          critical=critical,
          local=acquired_local,
          active=PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before),
          sg=sg,
           caller=entered_caller,
          call=entered,
          saved=saved,
          acquired=acquired,
          released=released,
          release_heap=release_heap */;
    /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
        FlagPendActiveCaller::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, entered_caller, entered, saved, acquired, released, release_heap)
        which implies
        SelectedCallerPhaseComponent::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, entered_caller, entered, saved, acquired, released, release_heap)
    */                       /* Yes, condition met, return to caller     */
                 *perr                   = OS_ERR_NONE;
                 OS_TRACE_FLAG_PEND_EXIT(*perr);
                 return (flags_rdy);
             } else {                                      /* Block task until events occur or timeout */
                 /*@ pgrp == pgrp0 && FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     pgrp0 != 0 && PendPhaseCandidate::flag_pend_source_layout &&
                     UCOS2_state_inv(sg, acquired) &&
                     PendPhaseCandidate::flag_pend_group_lookup(acquired, i, protected_image) &&
                     data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
                     data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
                     PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                     which implies
                     UCOS2_fields_inv(sg, acquired) * data_at(&pgrp, OS_FLAG_GRP *, pgrp0)
                 */
                 /*@ undef_data_at(&node, OS_FLAG_NODE)
                     which implies
                     undef_data_at(&(node.OSFlagNodeNext), void *) *
                     undef_data_at(&(node.OSFlagNodePrev), void *) *
                     undef_data_at(&(node.OSFlagNodeTCB), void *) *
                     undef_data_at(&(node.OSFlagNodeFlagGrp), void *) *
                     undef_data_at(&(node.OSFlagNodeFlags), OS_FLAGS) *
                     undef_data_at(&(node.OSFlagNodeWaitType), INT8U)
                 */
                 /*@ PendPhaseCandidate::flag_pend_source_layout &&
                     undef_data_at(&(node.OSFlagNodeNext), void *) *
                     undef_data_at(&(node.OSFlagNodePrev), void *) *
                     undef_data_at(&(node.OSFlagNodeTCB), void *) *
                     undef_data_at(&(node.OSFlagNodeFlagGrp), void *) *
                     undef_data_at(&(node.OSFlagNodeFlags), OS_FLAGS) *
                     undef_data_at(&(node.OSFlagNodeWaitType), INT8U)
                     which implies PendPhaseCandidate::flag_pend_node_fields(&node)
                 */
                 /*@ Assert exists (waiter : FlagWaiterState) (old_task : TaskAbstractState)
                                   (group : FlagGroupState)
                                   (saved normalized consumed original_result ready_seen : Z),
                     PendPhaseCandidate::flag_pend_source_layout && kernel_sched_ready_clients(critical) &&
                     PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                       &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                       &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
                     FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     PendPhaseCandidate::flag_pend_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask,
                       before, i, pgrp0, entered, saved, acquired) &&
                     PendPhaseCandidate::flag_pend_block_source_facts(sg, call, entered, acquired) &&
                     PendPhaseCandidate::flag_pend_first_unsatisfied(sg, protected_image, requested, original_mode) &&
                     PendPhaseCandidate::flag_pend_block_binding(sg, call, entered, acquired, i, &node, requested,
                       normalized, delay, waiter, old_task, group, protected_image) &&
                     PendPhaseCandidate::flag_pend_mode_parameters(original_mode, normalized, consumed) &&
                     pgrp == pgrp0 && flags == requested && wait_type == normalized &&
                     timeout == delay && perr == errp && cpu_sr == saved &&
                     consume == consumed && result == original_result && flags_rdy == ready_seen &&
                     pgrp == flag_block_call_group(sg, waiter) &&
                     &node == flag_block_call_node(waiter) &&
                     flags == flag_block_call_mask(waiter) &&
                     wait_type == flag_block_call_mode(waiter) &&
                     &OSTCBCur == g_OSTCBCur(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
                     &OSRdyGrp == g_OSRdyGrp(sg) &&
                     flag_block_call_fields_pre(sg, acquired, waiter, old_task, group, protected_image, delay) *
                      PendPhaseCandidate::flag_pend_block_callee_frame(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                        entered, saved, acquired, &pend_stat, perr, F)
                 */
                 /*@ Given waiter old_task group saved normalized consumed original_result ready_seen */
                 OS_FlagBlock(pgrp, &node, flags, wait_type, timeout)
                 /*@ where sg=sg, s=acquired, w=waiter, t=old_task, g=group,
                     v=protected_image, delay=delay,
                     F=PendPhaseCandidate::flag_pend_block_callee_frame(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                          entered, saved, acquired, &pend_stat, perr, F) */;
                 /*@ Assert exists (blocked : UCOS2_Verify_State),
                     PendPhaseCandidate::flag_pend_source_layout && kernel_sched_ready_clients(critical) &&
                     PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                       &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                       &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
                     FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     PendPhaseCandidate::flag_pend_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask,
                       before, i, pgrp0, entered, saved, acquired) &&
                     PendPhaseCandidate::flag_pend_first_waiting(sg, i, requested, original_mode, delay, acquired, &node, blocked) &&
                     PendPhaseCandidate::flag_pend_running_available(entered, blocked) &&
                     PendPhaseCandidate::flag_pend_mode_parameters(original_mode, normalized, consumed) &&
                     pgrp == pgrp0 && flags == requested && wait_type == normalized &&
                     timeout == delay && perr == errp && cpu_sr == saved &&
                     consume == consumed && result == original_result && flags_rdy == ready_seen &&
                     ((os_sched_ints(blocked) == 0 && os_sched_locks(blocked) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), blocked)) &&
        flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                       PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked)) * undef_data_at(&pend_stat, INT8U) *
                     undef_data_at(perr, INT8U) * F
                 */
                 /*@ Given blocked */
                 /*@ ((os_sched_ints(blocked) == 0 && os_sched_locks(blocked) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), blocked)) &&
        flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                       PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked))
                     which implies exists (release_heap : model),
                     os_sched_active_heap_cut(flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                       PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked), release_heap)
                 */
                 /*@ Given release_heap */
                 OS_CPU_SR_Restore(cpu_sr)
        /*@ where environment=task_sw_hook_call_environment(base_environment),
          critical=critical,
          local=acquired_local,
          active=PendPhaseCandidate::flag_pend_wait_active(sg, call, &node),
          sg=sg,
           caller=FlagPendTaskCaller(entered),
          call=entered,
          saved=saved,
          acquired=acquired,
          released=blocked,
          release_heap=release_heap */;
    /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_wait_active(sg, call, &node)) &&
        FlagPendActiveCaller::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked, release_heap)
        which implies
        SelectedCallerPhaseComponent::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked, release_heap)
    */
             }
             break;

#if OS_FLAG_WAIT_CLR_EN > 0u
        case OS_FLAG_WAIT_CLR_ALL:                         /* See if all required flags are cleared    */
             /*@ PendPhaseCandidate::flag_pend_valid_mode(original_mode) &&
                     pgrp0 != 0 && os_sched_ints(before) <= 0 && os_sched_locks(before) <= 0 &&
                     PendPhaseCandidate::flag_pend_group_lookup(before, i, observed) &&
                     PendPhaseCandidate::flag_pend_group_type(observed) == 5 &&
                     interrupt_saved_value(mask, joined_saved) &&
                     FlagPendActiveCaller::flag_pend_caller_save_observation(task_sw_hook_call_environment(base_environment), critical, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, caller, call, entered_caller, entered, mask, joined_saved, before, acquired) &&
                     FlagPendActiveCaller::flag_pend_caller_endpoint_observations(task_sw_hook_call_environment(base_environment), PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, caller, call, before, entered, acquired) &&
                     PendPhaseCandidate::flag_pend_caller_masked_control(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                       entered_caller, entered, joined_saved, acquired, acquired) *
                     data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
                     data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
                     PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                     which implies
                     FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
                     PendPhaseCandidate::flag_pend_caller_save_observation(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, entered_caller, entered, mask, joined_saved, before, acquired) &&
                     PendPhaseCandidate::flag_pend_call_source_observations(task_sw_hook_call_environment(base_environment), sg, caller, call, before, entered, acquired) &&
                     PendPhaseCandidate::flag_pend_caller_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, before, i, pgrp0, entered_caller, entered, joined_saved, acquired) &&
                     PendPhaseCandidate::flag_pend_caller_masked_control(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                       entered_caller, entered, joined_saved, acquired, acquired) *
                     data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
                     data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
                     PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                 */
             flags_rdy = (OS_FLAGS)~pgrp->OSFlagFlags & flags;    /* Extract only the bits we want     */
             if (flags_rdy == flags) {                     /* Must match ALL the bits that we want     */
                 if (consume == OS_TRUE) {                 /* See if we need to consume the flags      */
                     pgrp->OSFlagFlags |= flags_rdy;       /* Set ONLY the flags that we wanted        */
                 }
                 /*@ FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     pgrp0 != 0 && os_sched_ints(before) <= 0 && os_sched_locks(before) <= 0 &&
                     PendPhaseCandidate::flag_pend_group_lookup(before, i, observed) && PendPhaseCandidate::flag_pend_group_type(observed) == 5 &&
                     PendPhaseCandidate::flag_pend_source_layout && PendPhaseCandidate::flag_pend_valid_mode(original_mode) &&
                     task_tcb_init_stack_source_preserved(call, before, acquired) &&
                     task_tcb_init_stack_same_call(entered, call) &&
                     PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                       &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                       &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
                     PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                     which implies exists (current_tid : Z) (current_task : TaskAbstractState),
                     PendPhaseCandidate::flag_pend_current_binding(acquired, current_tid, current_task) &&
                     data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, current_tid)) *
                     data_at(field_addr(task_slot_addr(sg, current_tid), OS_TCB, OSTCBFlagsRdy),
                       OS_FLAGS, tcbFlagsRdy(current_task)) *
                     PendPhaseCandidate::flag_pend_group_current_frame(sg, acquired, current_tid, current_task, i, protected_image)
                 */
                 /*@ Given current_tid current_task */
                 OSTCBCur->OSTCBFlagsRdy = flags_rdy;      /* Save flags that were ready               */
                 /*@ Assert exists (released : UCOS2_Verify_State)
                       (ready saved normalized original_result consumed : Z),
                     FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     PendPhaseCandidate::flag_pend_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask,
                       before, i, pgrp0, entered, saved, acquired) &&
                     PendPhaseCandidate::flag_pend_first_return(sg, i, requested, original_mode, delay,
                       acquired, ready, 0, released) &&
                     entered_caller == FlagPendTaskCaller(entered) &&
                     PendPhaseCandidate::flag_pend_task_stage(entered, released) &&
                     FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
                     PendPhaseCandidate::flag_pend_first_registration(original_mode, call, before, entered, released) &&
                     pgrp == pgrp0 && flags == requested && wait_type == normalized &&
                     timeout == delay && perr == errp && flags_rdy == ready &&
                     cpu_sr == saved && result == original_result && consume == consumed &&
                     ((os_sched_ints(released) == 0 && os_sched_locks(released) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), released)) &&
        PendPhaseCandidate::flag_pend_caller_fields_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local, sg, entered_caller,
                       entered, saved, acquired, released)) *
                     undef_data_at(&pend_stat, INT8U) * undef_data_at(&node, OS_FLAG_NODE) *
                     undef_data_at(perr, INT8U) * F
                 */
                 /*@ Given released ready saved normalized original_result consumed */
                 /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
                     PendPhaseCandidate::flag_pend_first_registration(original_mode, call, before, entered, released) &&
                     ((os_sched_ints(released) == 0 && os_sched_locks(released) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), released)) &&
        PendPhaseCandidate::flag_pend_caller_fields_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local, sg, entered_caller,
                       entered, saved, acquired, released))
                     which implies exists (release_heap : model),
                     os_sched_active_heap_cut(flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                       PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, entered_caller, entered, saved, acquired, released), release_heap)
                 */
                 /*@ Given release_heap */
                 OS_CPU_SR_Restore(cpu_sr)
        /*@ where environment=task_sw_hook_call_environment(base_environment),
          critical=critical,
          local=acquired_local,
          active=PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before),
          sg=sg,
           caller=entered_caller,
          call=entered,
          saved=saved,
          acquired=acquired,
          released=released,
          release_heap=release_heap */;
    /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
        FlagPendActiveCaller::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, entered_caller, entered, saved, acquired, released, release_heap)
        which implies
        SelectedCallerPhaseComponent::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, entered_caller, entered, saved, acquired, released, release_heap)
    */                       /* Yes, condition met, return to caller     */
                 *perr                   = OS_ERR_NONE;
                 OS_TRACE_FLAG_PEND_EXIT(*perr);
                 return (flags_rdy);
             } else {                                      /* Block task until events occur or timeout */
                 /*@ pgrp == pgrp0 && FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     pgrp0 != 0 && PendPhaseCandidate::flag_pend_source_layout &&
                     UCOS2_state_inv(sg, acquired) &&
                     PendPhaseCandidate::flag_pend_group_lookup(acquired, i, protected_image) &&
                     data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
                     data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
                     PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                     which implies
                     UCOS2_fields_inv(sg, acquired) * data_at(&pgrp, OS_FLAG_GRP *, pgrp0)
                 */
                 /*@ undef_data_at(&node, OS_FLAG_NODE)
                     which implies
                     undef_data_at(&(node.OSFlagNodeNext), void *) *
                     undef_data_at(&(node.OSFlagNodePrev), void *) *
                     undef_data_at(&(node.OSFlagNodeTCB), void *) *
                     undef_data_at(&(node.OSFlagNodeFlagGrp), void *) *
                     undef_data_at(&(node.OSFlagNodeFlags), OS_FLAGS) *
                     undef_data_at(&(node.OSFlagNodeWaitType), INT8U)
                 */
                 /*@ PendPhaseCandidate::flag_pend_source_layout &&
                     undef_data_at(&(node.OSFlagNodeNext), void *) *
                     undef_data_at(&(node.OSFlagNodePrev), void *) *
                     undef_data_at(&(node.OSFlagNodeTCB), void *) *
                     undef_data_at(&(node.OSFlagNodeFlagGrp), void *) *
                     undef_data_at(&(node.OSFlagNodeFlags), OS_FLAGS) *
                     undef_data_at(&(node.OSFlagNodeWaitType), INT8U)
                     which implies PendPhaseCandidate::flag_pend_node_fields(&node)
                 */
                 /*@ Assert exists (waiter : FlagWaiterState) (old_task : TaskAbstractState)
                                   (group : FlagGroupState)
                                   (saved normalized consumed original_result ready_seen : Z),
                     PendPhaseCandidate::flag_pend_source_layout && kernel_sched_ready_clients(critical) &&
                     PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                       &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                       &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
                     FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     PendPhaseCandidate::flag_pend_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask,
                       before, i, pgrp0, entered, saved, acquired) &&
                     PendPhaseCandidate::flag_pend_block_source_facts(sg, call, entered, acquired) &&
                     PendPhaseCandidate::flag_pend_first_unsatisfied(sg, protected_image, requested, original_mode) &&
                     PendPhaseCandidate::flag_pend_block_binding(sg, call, entered, acquired, i, &node, requested,
                       normalized, delay, waiter, old_task, group, protected_image) &&
                     PendPhaseCandidate::flag_pend_mode_parameters(original_mode, normalized, consumed) &&
                     pgrp == pgrp0 && flags == requested && wait_type == normalized &&
                     timeout == delay && perr == errp && cpu_sr == saved &&
                     consume == consumed && result == original_result && flags_rdy == ready_seen &&
                     pgrp == flag_block_call_group(sg, waiter) &&
                     &node == flag_block_call_node(waiter) &&
                     flags == flag_block_call_mask(waiter) &&
                     wait_type == flag_block_call_mode(waiter) &&
                     &OSTCBCur == g_OSTCBCur(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
                     &OSRdyGrp == g_OSRdyGrp(sg) &&
                     flag_block_call_fields_pre(sg, acquired, waiter, old_task, group, protected_image, delay) *
                      PendPhaseCandidate::flag_pend_block_callee_frame(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                        entered, saved, acquired, &pend_stat, perr, F)
                 */
                 /*@ Given waiter old_task group saved normalized consumed original_result ready_seen */
                 OS_FlagBlock(pgrp, &node, flags, wait_type, timeout)
                 /*@ where sg=sg, s=acquired, w=waiter, t=old_task, g=group,
                     v=protected_image, delay=delay,
                     F=PendPhaseCandidate::flag_pend_block_callee_frame(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                          entered, saved, acquired, &pend_stat, perr, F) */;
                 /*@ Assert exists (blocked : UCOS2_Verify_State),
                     PendPhaseCandidate::flag_pend_source_layout && kernel_sched_ready_clients(critical) &&
                     PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                       &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                       &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
                     FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     PendPhaseCandidate::flag_pend_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask,
                       before, i, pgrp0, entered, saved, acquired) &&
                     PendPhaseCandidate::flag_pend_first_waiting(sg, i, requested, original_mode, delay, acquired, &node, blocked) &&
                     PendPhaseCandidate::flag_pend_running_available(entered, blocked) &&
                     PendPhaseCandidate::flag_pend_mode_parameters(original_mode, normalized, consumed) &&
                     pgrp == pgrp0 && flags == requested && wait_type == normalized &&
                     timeout == delay && perr == errp && cpu_sr == saved &&
                     consume == consumed && result == original_result && flags_rdy == ready_seen &&
                     ((os_sched_ints(blocked) == 0 && os_sched_locks(blocked) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), blocked)) &&
        flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                       PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked)) * undef_data_at(&pend_stat, INT8U) *
                     undef_data_at(perr, INT8U) * F
                 */
                 /*@ Given blocked */
                 /*@ ((os_sched_ints(blocked) == 0 && os_sched_locks(blocked) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), blocked)) &&
        flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                       PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked))
                     which implies exists (release_heap : model),
                     os_sched_active_heap_cut(flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                       PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked), release_heap)
                 */
                 /*@ Given release_heap */
                 OS_CPU_SR_Restore(cpu_sr)
        /*@ where environment=task_sw_hook_call_environment(base_environment),
          critical=critical,
          local=acquired_local,
          active=PendPhaseCandidate::flag_pend_wait_active(sg, call, &node),
          sg=sg,
           caller=FlagPendTaskCaller(entered),
          call=entered,
          saved=saved,
          acquired=acquired,
          released=blocked,
          release_heap=release_heap */;
    /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_wait_active(sg, call, &node)) &&
        FlagPendActiveCaller::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked, release_heap)
        which implies
        SelectedCallerPhaseComponent::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked, release_heap)
    */
             }
             break;

        case OS_FLAG_WAIT_CLR_ANY:
             /*@ PendPhaseCandidate::flag_pend_valid_mode(original_mode) &&
                     pgrp0 != 0 && os_sched_ints(before) <= 0 && os_sched_locks(before) <= 0 &&
                     PendPhaseCandidate::flag_pend_group_lookup(before, i, observed) &&
                     PendPhaseCandidate::flag_pend_group_type(observed) == 5 &&
                     interrupt_saved_value(mask, joined_saved) &&
                     FlagPendActiveCaller::flag_pend_caller_save_observation(task_sw_hook_call_environment(base_environment), critical, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, caller, call, entered_caller, entered, mask, joined_saved, before, acquired) &&
                     FlagPendActiveCaller::flag_pend_caller_endpoint_observations(task_sw_hook_call_environment(base_environment), PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, caller, call, before, entered, acquired) &&
                     PendPhaseCandidate::flag_pend_caller_masked_control(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                       entered_caller, entered, joined_saved, acquired, acquired) *
                     data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
                     data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
                     PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                     which implies
                     FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
                     PendPhaseCandidate::flag_pend_caller_save_observation(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, entered_caller, entered, mask, joined_saved, before, acquired) &&
                     PendPhaseCandidate::flag_pend_call_source_observations(task_sw_hook_call_environment(base_environment), sg, caller, call, before, entered, acquired) &&
                     PendPhaseCandidate::flag_pend_caller_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, before, i, pgrp0, entered_caller, entered, joined_saved, acquired) &&
                     PendPhaseCandidate::flag_pend_caller_masked_control(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                       entered_caller, entered, joined_saved, acquired, acquired) *
                     data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
                     data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
                     PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                 */
             flags_rdy = (OS_FLAGS)~pgrp->OSFlagFlags & flags;   /* Extract only the bits we want      */
             if (flags_rdy != (OS_FLAGS)0) {               /* See if any flag cleared                  */
                 if (consume == OS_TRUE) {                 /* See if we need to consume the flags      */
                     pgrp->OSFlagFlags |= flags_rdy;       /* Set ONLY the flags that we got           */
                 }
                 /*@ FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     pgrp0 != 0 && os_sched_ints(before) <= 0 && os_sched_locks(before) <= 0 &&
                     PendPhaseCandidate::flag_pend_group_lookup(before, i, observed) && PendPhaseCandidate::flag_pend_group_type(observed) == 5 &&
                     PendPhaseCandidate::flag_pend_source_layout && PendPhaseCandidate::flag_pend_valid_mode(original_mode) &&
                     task_tcb_init_stack_source_preserved(call, before, acquired) &&
                     task_tcb_init_stack_same_call(entered, call) &&
                     PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                       &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                       &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
                     PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                     which implies exists (current_tid : Z) (current_task : TaskAbstractState),
                     PendPhaseCandidate::flag_pend_current_binding(acquired, current_tid, current_task) &&
                     data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, current_tid)) *
                     data_at(field_addr(task_slot_addr(sg, current_tid), OS_TCB, OSTCBFlagsRdy),
                       OS_FLAGS, tcbFlagsRdy(current_task)) *
                     PendPhaseCandidate::flag_pend_group_current_frame(sg, acquired, current_tid, current_task, i, protected_image)
                 */
                 /*@ Given current_tid current_task */
                 OSTCBCur->OSTCBFlagsRdy = flags_rdy;      /* Save flags that were ready               */
                 /*@ Assert exists (released : UCOS2_Verify_State)
                       (ready saved normalized original_result consumed : Z),
                     FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     PendPhaseCandidate::flag_pend_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask,
                       before, i, pgrp0, entered, saved, acquired) &&
                     PendPhaseCandidate::flag_pend_first_return(sg, i, requested, original_mode, delay,
                       acquired, ready, 0, released) &&
                     entered_caller == FlagPendTaskCaller(entered) &&
                     PendPhaseCandidate::flag_pend_task_stage(entered, released) &&
                     FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
                     PendPhaseCandidate::flag_pend_first_registration(original_mode, call, before, entered, released) &&
                     pgrp == pgrp0 && flags == requested && wait_type == normalized &&
                     timeout == delay && perr == errp && flags_rdy == ready &&
                     cpu_sr == saved && result == original_result && consume == consumed &&
                     ((os_sched_ints(released) == 0 && os_sched_locks(released) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), released)) &&
        PendPhaseCandidate::flag_pend_caller_fields_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local, sg, entered_caller,
                       entered, saved, acquired, released)) *
                     undef_data_at(&pend_stat, INT8U) * undef_data_at(&node, OS_FLAG_NODE) *
                     undef_data_at(perr, INT8U) * F
                 */
                 /*@ Given released ready saved normalized original_result consumed */
                 /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
                     PendPhaseCandidate::flag_pend_first_registration(original_mode, call, before, entered, released) &&
                     ((os_sched_ints(released) == 0 && os_sched_locks(released) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), released)) &&
        PendPhaseCandidate::flag_pend_caller_fields_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local, sg, entered_caller,
                       entered, saved, acquired, released))
                     which implies exists (release_heap : model),
                     os_sched_active_heap_cut(flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                       PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, entered_caller, entered, saved, acquired, released), release_heap)
                 */
                 /*@ Given release_heap */
                 OS_CPU_SR_Restore(cpu_sr)
        /*@ where environment=task_sw_hook_call_environment(base_environment),
          critical=critical,
          local=acquired_local,
          active=PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before),
          sg=sg,
           caller=entered_caller,
          call=entered,
          saved=saved,
          acquired=acquired,
          released=released,
          release_heap=release_heap */;
    /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before)) &&
        FlagPendActiveCaller::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, entered_caller, entered, saved, acquired, released, release_heap)
        which implies
        SelectedCallerPhaseComponent::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, entered_caller, entered, saved, acquired, released, release_heap)
    */                       /* Yes, condition met, return to caller     */
                 *perr                   = OS_ERR_NONE;
                 OS_TRACE_FLAG_PEND_EXIT(*perr);
                 return (flags_rdy);
             } else {                                      /* Block task until events occur or timeout */
                 /*@ pgrp == pgrp0 && FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     pgrp0 != 0 && PendPhaseCandidate::flag_pend_source_layout &&
                     UCOS2_state_inv(sg, acquired) &&
                     PendPhaseCandidate::flag_pend_group_lookup(acquired, i, protected_image) &&
                     data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
                     data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
                     PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
                     which implies
                     UCOS2_fields_inv(sg, acquired) * data_at(&pgrp, OS_FLAG_GRP *, pgrp0)
                 */
                 /*@ undef_data_at(&node, OS_FLAG_NODE)
                     which implies
                     undef_data_at(&(node.OSFlagNodeNext), void *) *
                     undef_data_at(&(node.OSFlagNodePrev), void *) *
                     undef_data_at(&(node.OSFlagNodeTCB), void *) *
                     undef_data_at(&(node.OSFlagNodeFlagGrp), void *) *
                     undef_data_at(&(node.OSFlagNodeFlags), OS_FLAGS) *
                     undef_data_at(&(node.OSFlagNodeWaitType), INT8U)
                 */
                 /*@ PendPhaseCandidate::flag_pend_source_layout &&
                     undef_data_at(&(node.OSFlagNodeNext), void *) *
                     undef_data_at(&(node.OSFlagNodePrev), void *) *
                     undef_data_at(&(node.OSFlagNodeTCB), void *) *
                     undef_data_at(&(node.OSFlagNodeFlagGrp), void *) *
                     undef_data_at(&(node.OSFlagNodeFlags), OS_FLAGS) *
                     undef_data_at(&(node.OSFlagNodeWaitType), INT8U)
                     which implies PendPhaseCandidate::flag_pend_node_fields(&node)
                 */
                 /*@ Assert exists (waiter : FlagWaiterState) (old_task : TaskAbstractState)
                                   (group : FlagGroupState)
                                   (saved normalized consumed original_result ready_seen : Z),
                     PendPhaseCandidate::flag_pend_source_layout && kernel_sched_ready_clients(critical) &&
                     PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                       &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                       &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
                     FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     PendPhaseCandidate::flag_pend_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask,
                       before, i, pgrp0, entered, saved, acquired) &&
                     PendPhaseCandidate::flag_pend_block_source_facts(sg, call, entered, acquired) &&
                     PendPhaseCandidate::flag_pend_first_unsatisfied(sg, protected_image, requested, original_mode) &&
                     PendPhaseCandidate::flag_pend_block_binding(sg, call, entered, acquired, i, &node, requested,
                       normalized, delay, waiter, old_task, group, protected_image) &&
                     PendPhaseCandidate::flag_pend_mode_parameters(original_mode, normalized, consumed) &&
                     pgrp == pgrp0 && flags == requested && wait_type == normalized &&
                     timeout == delay && perr == errp && cpu_sr == saved &&
                     consume == consumed && result == original_result && flags_rdy == ready_seen &&
                     pgrp == flag_block_call_group(sg, waiter) &&
                     &node == flag_block_call_node(waiter) &&
                     flags == flag_block_call_mask(waiter) &&
                     wait_type == flag_block_call_mode(waiter) &&
                     &OSTCBCur == g_OSTCBCur(sg) && OSRdyTbl == g_OSRdyTbl(sg) &&
                     &OSRdyGrp == g_OSRdyGrp(sg) &&
                     flag_block_call_fields_pre(sg, acquired, waiter, old_task, group, protected_image, delay) *
                      PendPhaseCandidate::flag_pend_block_callee_frame(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                        entered, saved, acquired, &pend_stat, perr, F)
                 */
                 /*@ Given waiter old_task group saved normalized consumed original_result ready_seen */
                 OS_FlagBlock(pgrp, &node, flags, wait_type, timeout)
                 /*@ where sg=sg, s=acquired, w=waiter, t=old_task, g=group,
                     v=protected_image, delay=delay,
                     F=PendPhaseCandidate::flag_pend_block_callee_frame(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg,
                          entered, saved, acquired, &pend_stat, perr, F) */;
                 /*@ Assert exists (blocked : UCOS2_Verify_State),
                     PendPhaseCandidate::flag_pend_source_layout && kernel_sched_ready_clients(critical) &&
                     PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                       &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                       &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
                     FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     PendPhaseCandidate::flag_pend_saved_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask,
                       before, i, pgrp0, entered, saved, acquired) &&
                     PendPhaseCandidate::flag_pend_first_waiting(sg, i, requested, original_mode, delay, acquired, &node, blocked) &&
                     PendPhaseCandidate::flag_pend_running_available(entered, blocked) &&
                     PendPhaseCandidate::flag_pend_mode_parameters(original_mode, normalized, consumed) &&
                     pgrp == pgrp0 && flags == requested && wait_type == normalized &&
                     timeout == delay && perr == errp && cpu_sr == saved &&
                     consume == consumed && result == original_result && flags_rdy == ready_seen &&
                     ((os_sched_ints(blocked) == 0 && os_sched_locks(blocked) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), blocked)) &&
        flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                       PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked)) * undef_data_at(&pend_stat, INT8U) *
                     undef_data_at(perr, INT8U) * F
                 */
                 /*@ Given blocked */
                 /*@ ((os_sched_ints(blocked) == 0 && os_sched_locks(blocked) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), blocked)) &&
        flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                       PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked))
                     which implies exists (release_heap : model),
                     os_sched_active_heap_cut(flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                       PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked), release_heap)
                 */
                 /*@ Given release_heap */
                 OS_CPU_SR_Restore(cpu_sr)
        /*@ where environment=task_sw_hook_call_environment(base_environment),
          critical=critical,
          local=acquired_local,
          active=PendPhaseCandidate::flag_pend_wait_active(sg, call, &node),
          sg=sg,
           caller=FlagPendTaskCaller(entered),
          call=entered,
          saved=saved,
          acquired=acquired,
          released=blocked,
          release_heap=release_heap */;
    /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_wait_active(sg, call, &node)) &&
        FlagPendActiveCaller::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked, release_heap)
        which implies
        SelectedCallerPhaseComponent::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, acquired_local, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(entered), entered, saved, acquired, blocked, release_heap)
    */
             }
             break;
#endif

        default:
        /*@ pgrp == pgrp0 && pgrp0 != 0 && FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_source_layout &&
        PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
        UCOS2_state_inv(sg, acquired) &&
             FlagPendActiveCallerControl::flag_pend_caller_counters_zero(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), entered_caller, acquired) &&
             FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), acquired) &&
             PendPhaseCandidate::flag_pend_group_lookup(acquired, i, protected_image) &&
            PendPhaseCandidate::flag_pend_caller_masked_control(task_sw_hook_call_environment(base_environment), acquired_local, critical, sg, entered_caller,
              entered, cpu_sr, acquired, acquired) *
            data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(protected_image)) *
            data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(protected_image)) *
            PendPhaseCandidate::flag_pend_group_frame(sg, acquired, i, protected_image)
            which implies
            ((FlagPendActiveCallerControl::flag_pend_caller_counters_zero(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), entered_caller, acquired) &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), acquired)) &&
        PendPhaseCandidate::flag_pend_caller_fields_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local, sg, entered_caller,
              entered, cpu_sr, acquired, acquired)) *
            data_at(&pgrp, OS_FLAG_GRP *, pgrp0)
        */
             /*@ PendPhaseCandidate::flag_pend_first_registration(original_mode, call, before, entered, acquired) &&
                 ((FlagPendActiveCallerControl::flag_pend_caller_counters_zero(PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), entered_caller, acquired) &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), acquired)) &&
        PendPhaseCandidate::flag_pend_caller_fields_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local, sg, entered_caller,
                   entered, cpu_sr, acquired, acquired))
                 which implies exists (release_heap : model),
                 os_sched_active_heap_cut(flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, acquired_local,
                   PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before), sg, entered_caller, entered, cpu_sr, acquired, acquired), release_heap)
             */
             /*@ Given release_heap */
             OS_CPU_SR_Restore(cpu_sr)
        /*@ where environment=task_sw_hook_call_environment(base_environment),
          critical=critical,
          local=acquired_local,
          active=PendPhaseCandidate::flag_pend_first_observation(original_mode, call, before),
          sg=sg,
           caller=entered_caller,
          call=entered,
          saved=cpu_sr,
          acquired=acquired,
          released=acquired,
          release_heap=release_heap */;
             flags_rdy = (OS_FLAGS)0;
             *perr      = OS_ERR_FLAG_WAIT_TYPE;
             OS_TRACE_FLAG_PEND_EXIT(*perr);
             return (flags_rdy);
    }

    /*@ Assert exists (restored : OsSchedCallContext) (released : UCOS2_Verify_State)
                      (returned_local : Armv7aContinuation -> Assertion)
                      (saved normalized consumed original_result ready_seen : Z),
        os_sched_ints(released) == 0 && os_sched_locks(released) == 0 &&
                 PendPhaseCandidate::flag_pend_source_layout && kernel_sched_ready_clients(critical) &&
        PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
        FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_waiting_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask, before, i, pgrp0,
          requested, original_mode, delay, &node, restored, released) &&
        PendPhaseCandidate::flag_pend_mode_parameters(original_mode, normalized, consumed) &&
        FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_wait_active(sg, call, &node)) &&
        os_sched_active_local_stable(PendPhaseCandidate::flag_pend_wait_active(sg, call, &node)) &&
        PendPhaseCandidate::flag_pend_running_available(restored, released) &&
        pgrp == pgrp0 && flags == requested && wait_type == normalized && timeout == delay &&
        perr == errp && cpu_sr == saved && consume == consumed && result == original_result &&
        flags_rdy == ready_seen &&
        SchedulerCalleePhaseComponent::os_sched_task_call_pre(task_sw_hook_call_environment(base_environment), returned_local, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node),
          sg, restored, mask, released) *
        undef_data_at(&pend_stat, INT8U) * undef_data_at(perr, INT8U) * F
    */
    /*@ Given restored released returned_local saved normalized consumed original_result ready_seen */
    OS_Sched()
    /*@ where environment=base_environment, local=returned_local,
        active=PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), critical=critical,
        sg=sg, context=restored, mask=mask, before=released */; /* Find next HPT ready to run */
    /*@ SchedulerPhaseCandidate::os_sched_task_history_return_post(task_sw_hook_call_environment(base_environment), critical,
          PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, restored, mask, released)
        which implies exists (scheduled_call : OsSchedCallContext) (scheduled_state : UCOS2_Verify_State)
          (scheduled_local : Armv7aContinuation -> Assertion),
        PendPhaseCandidate::flag_pend_sched_return_observation(task_sw_hook_call_environment(base_environment), critical, sg, restored, mask, released,
          scheduled_call, scheduled_state) &&
        PendPhaseCandidate::flag_pend_ready_return_owned(task_sw_hook_call_environment(base_environment), scheduled_local, sg, scheduled_call, mask,
          scheduled_state, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node, scheduled_call, scheduled_state))
    */
    /*@ Assert exists (scheduled_call : OsSchedCallContext) (scheduled_state : UCOS2_Verify_State)
                      (scheduled_local : Armv7aContinuation -> Assertion),
        PendPhaseCandidate::flag_pend_source_layout && kernel_sched_ready_clients(critical) &&
        PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
        FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_scheduled_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask, before, i, pgrp0,
          requested, original_mode, delay, &node, scheduled_call, scheduled_state) &&
        flag_pend_current_ready(scheduled_call, scheduled_state) &&
        PendPhaseCandidate::flag_pend_running_available(scheduled_call, scheduled_state) &&
        PendPhaseCandidate::flag_pend_mode_parameters(original_mode, normalized, consumed) &&
        pgrp == pgrp0 && flags == requested && wait_type == normalized && timeout == delay &&
        perr == errp && cpu_sr == saved && consume == consumed && result == original_result &&
        flags_rdy == ready_seen &&
        ((os_sched_ints(scheduled_state) == 0 && os_sched_locks(scheduled_state) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), scheduled_state)) &&
        flag_pend_caller_save_input(task_sw_hook_call_environment(base_environment), critical, scheduled_local,
          PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(scheduled_call), scheduled_call, mask, scheduled_state)) * undef_data_at(&pend_stat, INT8U) * undef_data_at(perr, INT8U) * F
    */
    /*@ Given scheduled_call scheduled_state scheduled_local */
    /*@ ((os_sched_ints(scheduled_state) == 0 && os_sched_locks(scheduled_state) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), scheduled_state)) &&
        flag_pend_caller_save_input(task_sw_hook_call_environment(base_environment), critical, scheduled_local,
          PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(scheduled_call), scheduled_call, mask, scheduled_state))
        which implies exists (second_heap : model),
        os_sched_active_heap_cut(flag_pend_caller_save_input(task_sw_hook_call_environment(base_environment), critical, scheduled_local,
          PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(scheduled_call), scheduled_call, mask, scheduled_state), second_heap)
    */
    /*@ Given second_heap */
    cpu_sr = OS_CPU_SR_Save()
        /*@ where environment=task_sw_hook_call_environment(base_environment),
          critical=critical,
          local=scheduled_local,
          active=PendPhaseCandidate::flag_pend_wait_active(sg, call, &node),
          sg=sg,
           caller=FlagPendTaskCaller(scheduled_call),
          call=scheduled_call,
          mask=mask,
          before=scheduled_state,
          entry_heap=second_heap */;
    /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_wait_active(sg, call, &node)) &&
        FlagPendActiveCaller::flag_pend_selected_caller_save_output(task_sw_hook_call_environment(base_environment), critical, scheduled_local, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(scheduled_call), scheduled_call, mask, scheduled_state, second_heap, cpu_sr)
        which implies
        SelectedCallerPhaseComponent::flag_pend_selected_caller_save_output(task_sw_hook_call_environment(base_environment), critical, scheduled_local, PendPhaseCandidate::flag_pend_wait_active(sg, call, &node), sg, FlagPendTaskCaller(scheduled_call), scheduled_call, mask, scheduled_state, second_heap, cpu_sr)
    */
    /*@ Assert exists (reentered : OsSchedCallContext) (reacquired : UCOS2_Verify_State)
                      (resumed_local : Armv7aContinuation -> Assertion) (resaved current_tid : Z)
                      (resume_task : TaskAbstractState),
        os_sched_ints(reacquired) == 0 && os_sched_locks(reacquired) == 0 &&
                 PendPhaseCandidate::flag_pend_source_layout && kernel_sched_ready_clients(critical) &&
        PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
        FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_resumed_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask, before, i, pgrp0,
          requested, original_mode, delay, &node, reentered, resaved, reacquired) &&
        PendPhaseCandidate::flag_pend_mode_parameters(original_mode, normalized, consumed) &&
        UCOS2_state_inv(sg, reacquired) &&
        PendPhaseCandidate::flag_pend_current_binding(reacquired, current_tid, resume_task) &&
        flag_pend_current_ready(reentered, reacquired) &&
        PendPhaseCandidate::flag_pend_running_available(reentered, reacquired) &&
        PendPhaseCandidate::flag_pend_wait_outcome(call, &node, reacquired) &&
        pgrp == pgrp0 && flags == requested && wait_type == normalized && timeout == delay &&
        perr == errp && cpu_sr == resaved && consume == consumed && result == original_result &&
        flags_rdy == ready_seen &&
        PendPhaseCandidate::flag_pend_masked_control(task_sw_hook_call_environment(base_environment), resumed_local, critical, sg,
          reentered, resaved, reacquired, reacquired) *
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, current_tid)) *
        data_at(field_addr(task_slot_addr(sg, current_tid), OS_TCB, OSTCBStatPend),
          INT8U, encode_pend_status(statPend(resume_task))) *
        data_at(field_addr(task_slot_addr(sg, current_tid), OS_TCB, OSTCBStat),
          INT8U, encode_task_status(stat(resume_task))) *
        PendPhaseCandidate::flag_pend_resume_frame(sg, reacquired, current_tid, resume_task) *
        PendPhaseCandidate::flag_pend_wait_active(sg, call, &node, reentered, reacquired) *
        undef_data_at(&pend_stat, INT8U) * undef_data_at(perr, INT8U) * F
    */
    /*@ Given reentered reacquired resumed_local resaved current_tid resume_task */
    if (OSTCBCur->OSTCBStatPend != OS_STAT_PEND_OK) {      /* Have we timed-out or aborted?            */
        pend_stat                = OSTCBCur->OSTCBStatPend;
        OSTCBCur->OSTCBStatPend  = OS_STAT_PEND_OK;
        if (pend_stat != OS_STAT_PEND_ABORT) {            /* Delete already unlinked aborted waiters. */
            /*@ Assert exists (timeout_waiter : FlagWaiterState),
                os_sched_ints(reacquired) == 0 && os_sched_locks(reacquired) == 0 &&
                 PendPhaseCandidate::flag_pend_source_layout &&
                PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
                  &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
                  &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
                FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                  pgrp0, requested, original_mode, delay, before, X) &&
                PendPhaseCandidate::flag_pend_resumed_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask, before, i, pgrp0,
                  requested, original_mode, delay, &node, reentered, resaved, reacquired) &&
                PendPhaseCandidate::flag_pend_mode_parameters(original_mode, normalized, consumed) &&
                PendPhaseCandidate::flag_pend_current_binding(reacquired, current_tid, resume_task) &&
                PendPhaseCandidate::flag_pend_error_source_facts(sg, call, reentered, &node, reacquired, current_tid, resume_task) &&
                encode_pend_status(statPend(resume_task)) != 2 &&
                PendPhaseCandidate::flag_pend_timeout_waiter_binding(call, &node, current_tid, timeout_waiter) &&
                pgrp == pgrp0 && flags == requested && wait_type == normalized && timeout == delay &&
                perr == errp && cpu_sr == resaved && consume == consumed && result == original_result &&
                flags_rdy == ready_seen && pend_stat == encode_pend_status(statPend(resume_task)) &&
                flag_unlink_fields_pre(sg, FlagState(reacquired), &node, timeout_waiter,
                  PendPhaseCandidate::flag_pend_write_pend_ok(resume_task)) *
                PendPhaseCandidate::flag_pend_unlink_callee_frame(task_sw_hook_call_environment(base_environment), resumed_local, critical, sg,
                  reentered, resaved, reacquired, current_tid, &OSTCBCur, perr, F)
            */
            /*@ Given timeout_waiter */
            OS_FlagUnlink(&node)
            /*@ where sg=sg, flags=FlagState(reacquired), p=&node, w=timeout_waiter,
                t=PendPhaseCandidate::flag_pend_write_pend_ok(resume_task),
                F=PendPhaseCandidate::flag_pend_unlink_callee_frame(task_sw_hook_call_environment(base_environment), resumed_local, critical, sg,
                    reentered, resaved, reacquired, current_tid, &OSTCBCur, perr, F) */;
        }
        /*@ Assert exists (intermediate : UCOS2_Verify_State) (intermediate_task : TaskAbstractState),
            os_sched_ints(reacquired) == 0 && os_sched_locks(reacquired) == 0 &&
                 PendPhaseCandidate::flag_pend_source_layout &&
            PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
            FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
              pgrp0, requested, original_mode, delay, before, X) &&
            PendPhaseCandidate::flag_pend_resumed_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask, before, i, pgrp0,
              requested, original_mode, delay, &node, reentered, resaved, reacquired) &&
            PendPhaseCandidate::flag_pend_error_source_facts(sg, call, reentered, &node, reacquired, current_tid, resume_task) &&
            PendPhaseCandidate::flag_pend_error_intermediate(reacquired, &node, encode_pend_status(statPend(resume_task)), intermediate) &&
            PendPhaseCandidate::flag_pend_current_binding(intermediate, current_tid, intermediate_task) &&
            pgrp == pgrp0 && flags == requested && wait_type == normalized && timeout == delay &&
            perr == errp && cpu_sr == resaved && consume == consumed && result == original_result &&
            flags_rdy == ready_seen && pend_stat == encode_pend_status(statPend(resume_task)) &&
            data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, current_tid)) *
            data_at(field_addr(task_slot_addr(sg, current_tid), OS_TCB, OSTCBStat),
              INT8U, encode_task_status(stat(intermediate_task))) *
            PendPhaseCandidate::flag_pend_cleanup_stat_frame(sg, intermediate, current_tid, intermediate_task) *
            PendPhaseCandidate::flag_pend_masked_control(task_sw_hook_call_environment(base_environment), resumed_local, critical, sg,
              reentered, resaved, reacquired, intermediate) *
            PendPhaseCandidate::flag_pend_node_fields(&node) * undef_data_at(perr, INT8U) * F
        */
        /*@ Given intermediate intermediate_task */
        OSTCBCur->OSTCBStat      = OS_STAT_RDY;            /* Yes, make task ready-to-run              */
        /*@ Assert exists (cleaned : UCOS2_Verify_State),
            PendPhaseCandidate::flag_pend_source_layout &&
            FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
              pgrp0, requested, original_mode, delay, before, X) &&
            PendPhaseCandidate::flag_pend_resumed_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask, before, i, pgrp0,
              requested, original_mode, delay, &node, reentered, resaved, reacquired) &&
            PendPhaseCandidate::flag_pend_resume_result(sg, i, &node, original_mode, reacquired, 0,
              PendPhaseCandidate::flag_pend_resume_error(encode_pend_status(statPend(resume_task))), cleaned) &&
        flag_pend_current_ready(reentered, cleaned) &&
        PendPhaseCandidate::flag_pend_task_stage(reentered, cleaned) &&
            pgrp == pgrp0 && flags == requested && wait_type == normalized && timeout == delay &&
            perr == errp && cpu_sr == resaved && consume == consumed && result == original_result &&
            flags_rdy == ready_seen && pend_stat == encode_pend_status(statPend(resume_task)) &&
            ((os_sched_ints(cleaned) == 0 && os_sched_locks(cleaned) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_fresh_observation(call), cleaned)) &&
        flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, resumed_local,
              PendPhaseCandidate::flag_pend_fresh_observation(call), sg, FlagPendTaskCaller(reentered), reentered, resaved, reacquired, cleaned)) * PendPhaseCandidate::flag_pend_node_fields(&node) * undef_data_at(perr, INT8U) * F
        */
        /*@ Given cleaned */
        /*@ PendPhaseCandidate::flag_pend_source_layout && PendPhaseCandidate::flag_pend_node_fields(&node)
            which implies undef_data_at(&node, OS_FLAG_NODE)
        */
        /*@ ((os_sched_ints(cleaned) == 0 && os_sched_locks(cleaned) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_fresh_observation(call), cleaned)) &&
        flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, resumed_local,
              PendPhaseCandidate::flag_pend_fresh_observation(call), sg, FlagPendTaskCaller(reentered), reentered, resaved, reacquired, cleaned))
            which implies exists (final_heap : model),
            os_sched_active_heap_cut(flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, resumed_local,
              PendPhaseCandidate::flag_pend_fresh_observation(call), sg, FlagPendTaskCaller(reentered), reentered, resaved, reacquired, cleaned), final_heap)
        */
        /*@ Given final_heap */
        OS_CPU_SR_Restore(cpu_sr)
        /*@ where environment=task_sw_hook_call_environment(base_environment),
          critical=critical,
          local=resumed_local,
          active=PendPhaseCandidate::flag_pend_fresh_observation(call),
          sg=sg,
           caller=FlagPendTaskCaller(reentered),
          call=reentered,
          saved=resaved,
          acquired=reacquired,
          released=cleaned,
          release_heap=final_heap */;
    /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_fresh_observation(call)) &&
        FlagPendActiveCaller::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, resumed_local, PendPhaseCandidate::flag_pend_fresh_observation(call), sg, FlagPendTaskCaller(reentered), reentered, resaved, reacquired, cleaned, final_heap)
        which implies
        SelectedCallerPhaseComponent::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, resumed_local, PendPhaseCandidate::flag_pend_fresh_observation(call), sg, FlagPendTaskCaller(reentered), reentered, resaved, reacquired, cleaned, final_heap)
    */
        flags_rdy                = (OS_FLAGS)0;
        switch (pend_stat) {
            case OS_STAT_PEND_ABORT:
                 *perr = OS_ERR_PEND_ABORT;                /* Indicate that we aborted   waiting       */
                 break;

            case OS_STAT_PEND_TO:
            default:
                 *perr = OS_ERR_TIMEOUT;                   /* Indicate that we timed-out waiting       */
                 break;
        }
        OS_TRACE_FLAG_PEND_EXIT(*perr);
        return (flags_rdy);
    }
    /*@ Assert exists (resume_image : FlagGroupImage),
        os_sched_ints(reacquired) == 0 && os_sched_locks(reacquired) == 0 &&
                 PendPhaseCandidate::flag_pend_source_layout &&
        PendPhaseCandidate::flag_pend_global_addresses(sg, &OSIntNesting, &OSLockNesting,
          &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
          &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl, &OSTCBCur) &&
        FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_resumed_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask, before, i, pgrp0,
          requested, original_mode, delay, &node, reentered, resaved, reacquired) &&
        PendPhaseCandidate::flag_pend_mode_parameters(original_mode, normalized, consumed) &&
        PendPhaseCandidate::flag_pend_current_binding(reacquired, current_tid, resume_task) &&
        encode_pend_status(statPend(resume_task)) == 0 &&
        flag_pend_current_ready(reentered, reacquired) &&
        PendPhaseCandidate::flag_pend_running_available(reentered, reacquired) &&
        PendPhaseCandidate::flag_pend_group_lookup(reacquired, i, resume_image) && UCOS2_state_inv(sg, reacquired) &&
        pgrp == pgrp0 && flags == requested && wait_type == normalized && timeout == delay &&
        perr == errp && cpu_sr == resaved && consume == consumed && result == original_result &&
        flags_rdy == ready_seen &&
        PendPhaseCandidate::flag_pend_masked_control(task_sw_hook_call_environment(base_environment), resumed_local, critical, sg,
          reentered, resaved, reacquired, reacquired) *
        data_at(&OSTCBCur, OS_TCB *, task_slot_addr(sg, current_tid)) *
        data_at(field_addr(task_slot_addr(sg, current_tid), OS_TCB, OSTCBFlagsRdy),
          OS_FLAGS, tcbFlagsRdy(resume_task)) *
        data_at(&(pgrp->OSFlagType), INT8U, PendPhaseCandidate::flag_pend_group_type(resume_image)) *
        data_at(&(pgrp->OSFlagFlags), OS_FLAGS, PendPhaseCandidate::flag_pend_group_bits(resume_image)) *
        PendPhaseCandidate::flag_pend_group_current_frame(sg, reacquired, current_tid, resume_task, i, resume_image) *
        PendPhaseCandidate::flag_pend_wait_active(sg, call, &node, reentered, reacquired) *
        undef_data_at(&pend_stat, INT8U) * undef_data_at(perr, INT8U) * F
    */
    /*@ Given resume_image */
    flags_rdy = OSTCBCur->OSTCBFlagsRdy;
    if (consume == OS_TRUE) {                              /* See if we need to consume the flags      */
        switch (wait_type) {
            case OS_FLAG_WAIT_SET_ALL:
            case OS_FLAG_WAIT_SET_ANY:                     /* Clear ONLY the flags we got              */
                 pgrp->OSFlagFlags &= (OS_FLAGS)~flags_rdy;
                 break;

#if OS_FLAG_WAIT_CLR_EN > 0u
            case OS_FLAG_WAIT_CLR_ALL:
            case OS_FLAG_WAIT_CLR_ANY:                     /* Set   ONLY the flags we got              */
                 pgrp->OSFlagFlags |=  flags_rdy;
                 break;
#endif
            default:
                 /*@ Assert exists (cleaned : UCOS2_Verify_State) (saved_ready : Z),
                     PendPhaseCandidate::flag_pend_source_layout &&
                     FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
                       pgrp0, requested, original_mode, delay, before, X) &&
                     PendPhaseCandidate::flag_pend_resumed_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask, before, i, pgrp0,
                       requested, original_mode, delay, &node, reentered, resaved, reacquired) &&
                     PendPhaseCandidate::flag_pend_resume_result(sg, i, &node, original_mode, reacquired, 0, 111, cleaned) &&
        flag_pend_current_ready(reentered, cleaned) &&
        PendPhaseCandidate::flag_pend_task_stage(reentered, cleaned) &&
                     pgrp == pgrp0 && flags == requested && wait_type == normalized && timeout == delay &&
                     perr == errp && cpu_sr == resaved && consume == consumed && result == original_result &&
                     flags_rdy == saved_ready &&
                     ((os_sched_ints(cleaned) == 0 && os_sched_locks(cleaned) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_fresh_observation(call), cleaned)) &&
        flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, resumed_local,
                       PendPhaseCandidate::flag_pend_fresh_observation(call), sg, FlagPendTaskCaller(reentered), reentered, resaved, reacquired, cleaned)) * PendPhaseCandidate::flag_pend_node_fields(&node) *
                     undef_data_at(&pend_stat, INT8U) * undef_data_at(perr, INT8U) * F
                 */
                 /*@ Given cleaned saved_ready */
                 /*@ PendPhaseCandidate::flag_pend_source_layout && PendPhaseCandidate::flag_pend_node_fields(&node) which implies undef_data_at(&node, OS_FLAG_NODE) */
                 /*@ ((os_sched_ints(cleaned) == 0 && os_sched_locks(cleaned) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_fresh_observation(call), cleaned)) &&
        flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, resumed_local,
                       PendPhaseCandidate::flag_pend_fresh_observation(call), sg, FlagPendTaskCaller(reentered), reentered, resaved, reacquired, cleaned))
                     which implies exists (final_heap : model),
                     os_sched_active_heap_cut(flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, resumed_local,
                       PendPhaseCandidate::flag_pend_fresh_observation(call), sg, FlagPendTaskCaller(reentered), reentered, resaved, reacquired, cleaned), final_heap)
                 */
                 /*@ Given final_heap */
                 OS_CPU_SR_Restore(cpu_sr)
        /*@ where environment=task_sw_hook_call_environment(base_environment),
          critical=critical,
          local=resumed_local,
          active=PendPhaseCandidate::flag_pend_fresh_observation(call),
          sg=sg,
           caller=FlagPendTaskCaller(reentered),
          call=reentered,
          saved=resaved,
          acquired=reacquired,
          released=cleaned,
          release_heap=final_heap */;
    /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_fresh_observation(call)) &&
        FlagPendActiveCaller::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, resumed_local, PendPhaseCandidate::flag_pend_fresh_observation(call), sg, FlagPendTaskCaller(reentered), reentered, resaved, reacquired, cleaned, final_heap)
        which implies
        SelectedCallerPhaseComponent::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, resumed_local, PendPhaseCandidate::flag_pend_fresh_observation(call), sg, FlagPendTaskCaller(reentered), reentered, resaved, reacquired, cleaned, final_heap)
    */
                 *perr = OS_ERR_FLAG_WAIT_TYPE;
                 OS_TRACE_FLAG_PEND_EXIT(*perr);
                 return ((OS_FLAGS)0);
        }
    }
    /*@ Assert exists (cleaned : UCOS2_Verify_State) (saved_ready : Z),
        PendPhaseCandidate::flag_pend_source_layout &&
        FlagPendInactiveFirstProgram::flag_pend_public_entry(task_sw_hook_call_environment(base_environment), critical, sg, caller, call, mask, i,
          pgrp0, requested, original_mode, delay, before, X) &&
        PendPhaseCandidate::flag_pend_resumed_prefix(task_sw_hook_call_environment(base_environment), critical, sg, call, mask, before, i, pgrp0,
          requested, original_mode, delay, &node, reentered, resaved, reacquired) &&
        PendPhaseCandidate::flag_pend_resume_result(sg, i, &node, original_mode, reacquired, saved_ready, 0, cleaned) &&
        flag_pend_current_ready(reentered, cleaned) &&
        PendPhaseCandidate::flag_pend_task_stage(reentered, cleaned) &&
        pgrp == pgrp0 && flags == requested && wait_type == normalized && timeout == delay &&
        perr == errp && cpu_sr == resaved && consume == consumed && result == original_result &&
        flags_rdy == saved_ready &&
        ((os_sched_ints(cleaned) == 0 && os_sched_locks(cleaned) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_fresh_observation(call), cleaned)) &&
        flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, resumed_local,
          PendPhaseCandidate::flag_pend_fresh_observation(call), sg, FlagPendTaskCaller(reentered), reentered, resaved, reacquired, cleaned)) * PendPhaseCandidate::flag_pend_node_fields(&node) *
        undef_data_at(&pend_stat, INT8U) * undef_data_at(perr, INT8U) * F
    */
    /*@ Given cleaned saved_ready */
    /*@ PendPhaseCandidate::flag_pend_source_layout && PendPhaseCandidate::flag_pend_node_fields(&node) which implies undef_data_at(&node, OS_FLAG_NODE) */
    /*@ ((os_sched_ints(cleaned) == 0 && os_sched_locks(cleaned) == 0 &&
        FlagPendEntryControl::flag_pend_active_entry(sg, PendPhaseCandidate::flag_pend_fresh_observation(call), cleaned)) &&
        flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, resumed_local,
          PendPhaseCandidate::flag_pend_fresh_observation(call), sg, FlagPendTaskCaller(reentered), reentered, resaved, reacquired, cleaned))
        which implies exists (final_heap : model),
        os_sched_active_heap_cut(flag_pend_caller_restore_input(task_sw_hook_call_environment(base_environment), critical, resumed_local,
          PendPhaseCandidate::flag_pend_fresh_observation(call), sg, FlagPendTaskCaller(reentered), reentered, resaved, reacquired, cleaned), final_heap)
    */
    /*@ Given final_heap */
    OS_CPU_SR_Restore(cpu_sr)
        /*@ where environment=task_sw_hook_call_environment(base_environment),
          critical=critical,
          local=resumed_local,
          active=PendPhaseCandidate::flag_pend_fresh_observation(call),
          sg=sg,
           caller=FlagPendTaskCaller(reentered),
          call=reentered,
          saved=resaved,
          acquired=reacquired,
          released=cleaned,
          release_heap=final_heap */;
    /*@ FlagPendActiveCallerControl::flag_pend_active_requires_control(PendPhaseCandidate::flag_pend_fresh_observation(call)) &&
        FlagPendActiveCaller::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, resumed_local, PendPhaseCandidate::flag_pend_fresh_observation(call), sg, FlagPendTaskCaller(reentered), reentered, resaved, reacquired, cleaned, final_heap)
        which implies
        SelectedCallerPhaseComponent::flag_pend_selected_caller_restore_output(task_sw_hook_call_environment(base_environment), critical, resumed_local, PendPhaseCandidate::flag_pend_fresh_observation(call), sg, FlagPendTaskCaller(reentered), reentered, resaved, reacquired, cleaned, final_heap)
    */
    *perr = OS_ERR_NONE;                                   /* Event(s) must have occurred              */
    OS_TRACE_FLAG_PEND_EXIT(*perr);
    return (flags_rdy);
}
