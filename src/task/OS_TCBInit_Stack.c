/* Annotation carrier for OS_TCBInit, pinned uC/OS-II V2.93.01.
 * Original headers, configuration and callee declarations: ../../overlays/task/task_tcb_init_stack*.patch.
 * Reproduce the canonical translation unit using the module README; do not expand macros here.
 */
INT8U  OS_TCBInit (INT8U    prio,
                   OS_STK  *ptos,
                   OS_STK  *pbos,
                   INT16U   id,
                   INT32U   stk_size,
                   void    *pext,
                   INT16U   opt)
/*@ phase_call_spec
    With (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
         (saved_local : Armv7aContinuation -> Assertion)
         (sg : StableGlobVars) (args : TaskTCBInitArgs)
         (region : TaskStackRegion) (create_args : TaskCreateArgs) (task_return : Z)
         (lower upper : list (option Z)) (call : OsSchedCallContext)
         (invocation : nat) (origin : TaskInvocationOrigin)
         (mask : Z) (initial : UCOS2_Verify_State) (LitMap : String -> Z)
         (literals : list String)
    Require task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
              OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
            task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
            args == task_tcb_init_stack_call_args(create_args, LitMap("?")) &&
            kernel_sched_ready_clients(critical) &&
          task_create_default_name_binding(LitMap("?"), initial) && UCOS2_state_inv(sg, initial) &&
            task_tcb_init_continuation_call_pre(environment, critical, saved_local, sg, region, create_args,
              task_return, lower, upper, LitMap("?"), invocation, origin, mask, initial, call) *
            GlobalStrings_missing(LitMap, literals)
    Ensure task_tcb_init_modular_phase_call_post(environment, critical, saved_local, sg, region, create_args,
              task_return, lower, upper, LitMap("?"), invocation, origin, mask, initial, call, __return) *
           GlobalStrings_missing(LitMap, literals)
*/{
    OS_TCB    *ptcb;
#if OS_CRITICAL_METHOD == 3u                               /* Allocate storage for CPU status register */
    OS_CPU_SR  cpu_sr = 0u;
#endif
#if OS_TASK_REG_TBL_SIZE > 0u
    INT8U      i;
#endif
#if OS_TASK_CREATE_EXT_EN > 0u
#if defined(OS_TLS_TBL_SIZE) && (OS_TLS_TBL_SIZE > 0u)
    INT8U      j;
#endif
#endif


/*@ task_tcb_init_continuation_call_pre(environment, critical, saved_local, sg, region, create_args,
          task_return, lower, upper, LitMap("?"), invocation, origin, mask, initial, call)
        which implies
          os_sched_call_invocation(call) == invocation && os_sched_call_origin(call) == origin &&
          task_tcb_init_entry(sg, task_tcb_init_stack_call_args(create_args, LitMap("?")), invocation, origin, initial) &&
          task_create_stack_layout(TaskStackNoVFP, region, create_args, lower, upper) &&
          task_tcb_init_continuation_save_input(environment, critical, saved_local, sg, call, mask, initial) *
          task_stack_storage(region, task_create_stack_image(TaskStackNoVFP, create_args, task_return, lower, upper))
    */    OS_ENTER_CRITICAL();
/*@ Assert exists (first_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          task_tcb_init_stack_same_call(first_call, call) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_tcb_init_runtime_history(sg, call, initial, first_call, acquired) &&
          task_tcb_init_timer_phase_eq(initial, acquired) &&
          kernel_sched_ready_clients(critical) &&
          task_create_default_name_binding(LitMap("?"), initial) && UCOS2_state_inv(sg, initial) &&
          os_sched_call_invocation(first_call) == invocation &&
          os_sched_call_origin(first_call) == origin &&
          args == task_tcb_init_stack_call_args(create_args, LitMap("?")) &&
          os_sched_call_invocation(call) == invocation && os_sched_call_origin(call) == origin &&
          task_create_stack_layout(TaskStackNoVFP, region, create_args, lower, upper) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          task_tcb_init_call_preserved(sg, invocation, initial, acquired) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
          task_stack_live_coverage(TskState(acquired), task_stack_call_active_key(first_call)) &&
          critical_region_masked(task_stack_call_platform(environment), critical, sg, invocation, origin, cpu_sr, acquired) *
          task_tcb_init_stack_context(environment, first_call) *
          task_tcb_init_continuation_capsules(environment, saved_local, acquired) *
          task_stack_storage(region, task_create_stack_image(TaskStackNoVFP, create_args, task_return, lower, upper)) *
          data_at(&OSTCBFreeList, OS_TCB *, task_tcb_init_free_root(sg, acquired)) *
          task_tcb_init_public_without_free_root(sg, acquired) * GlobalStrings_missing(LitMap, literals) *
          undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&i, INT8U)
    */    ptcb = OSTCBFreeList;                                  /* Get a free TCB from the free TCB list    */
    if (ptcb != (OS_TCB *)0) {
/*@ Assert exists (first_call : OsSchedCallContext) (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage) (next_free : Z),
          task_tcb_init_stack_same_call(first_call, call) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_tcb_init_runtime_history(sg, call, initial, first_call, acquired) &&
          task_tcb_init_timer_phase_eq(initial, acquired) &&
          kernel_sched_ready_clients(critical) &&
          task_create_default_name_binding(LitMap("?"), initial) && UCOS2_state_inv(sg, initial) &&
          os_sched_call_invocation(first_call) == invocation &&
          os_sched_call_origin(first_call) == origin &&
          args == task_tcb_init_stack_call_args(create_args, LitMap("?")) &&
          os_sched_call_invocation(call) == invocation && os_sched_call_origin(call) == origin &&
          task_create_stack_layout(TaskStackNoVFP, region, create_args, lower, upper) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
              task_tcb_init_call_preserved(sg, invocation, initial, acquired) &&
              interrupt_saved_value(mask, cpu_sr) &&
              task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
              task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
              task_tcb_init_free_next_image(free_image, next_free) &&
              next_free == task_tcb_init_free_next(sg, rest) &&
              ptcb == tcb64_addr(sg, slot) &&
              task_stack_live_coverage(TskState(acquired), task_stack_call_active_key(first_call)) &&
              critical_region_masked(task_stack_call_platform(environment), critical, sg, invocation, origin, cpu_sr, acquired) *
          task_tcb_init_stack_context(environment, first_call) *
          task_tcb_init_continuation_capsules(environment, saved_local, acquired) *
          task_stack_storage(region, task_create_stack_image(TaskStackNoVFP, create_args, task_return, lower, upper)) *
              data_at(&OSTCBFreeList, OS_TCB *, ptcb) *
              data_at(&ptcb->OSTCBNext, OS_TCB *, next_free) *
              tcb64_storage_without(ptcb, TCBNext, tcb_layout_common_image(free_image)) *
              task_tcb_init_public_without_free_head(sg, acquired, rest) * GlobalStrings_missing(LitMap, literals) *
              undef_data_at(&i, INT8U)
        */        OSTCBFreeList            = ptcb->OSTCBNext;        /* Update pointer to free TCB list          */
/*@ Assert exists (first_call : OsSchedCallContext) (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage),
          task_tcb_init_stack_same_call(first_call, call) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_tcb_init_runtime_history(sg, call, initial, first_call, acquired) &&
          task_tcb_init_timer_phase_eq(initial, acquired) &&
          kernel_sched_ready_clients(critical) &&
          task_create_default_name_binding(LitMap("?"), initial) && UCOS2_state_inv(sg, initial) &&
          os_sched_call_invocation(first_call) == invocation &&
          os_sched_call_origin(first_call) == origin &&
          args == task_tcb_init_stack_call_args(create_args, LitMap("?")) &&
          os_sched_call_invocation(call) == invocation && os_sched_call_origin(call) == origin &&
          task_create_stack_layout(TaskStackNoVFP, region, create_args, lower, upper) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
              task_tcb_init_call_preserved(sg, invocation, initial, acquired) &&
              interrupt_saved_value(mask, cpu_sr) &&
              task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
              task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
              ptcb == tcb64_addr(sg, slot) &&
              task_stack_live_coverage(TskState(task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image)), task_stack_call_active_key(first_call)) &&
              critical_region_masked(task_stack_call_platform(environment), critical, sg, invocation, origin, cpu_sr, acquired) *
          task_tcb_init_stack_context(environment, first_call) *
          task_tcb_init_continuation_capsules(environment, saved_local,
            task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image)) *
          task_stack_storage(region, task_create_stack_image(TaskStackNoVFP, create_args, task_return, lower, upper)) *
              UCOS2_inv(sg,
                task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image)) *
              tcb64_storage_rep(ptcb, tcb_layout_common_image(free_image)) * GlobalStrings_missing(LitMap, literals) *
              undef_data_at(&i, INT8U)
        *//*@ exists (first_call : OsSchedCallContext) (acquired : UCOS2_Verify_State)
          (slot : Z) (rest : list Z) (free_image : TCBLayoutImage),
          os_sched_call_invocation(first_call) == invocation &&
          os_sched_call_origin(first_call) == origin &&
          task_stack_live_coverage(TskState(task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image)), task_stack_call_active_key(first_call)) &&
          critical_region_masked(task_stack_call_platform(environment), critical, sg, invocation, origin, cpu_sr, acquired) *
          task_tcb_init_stack_context(environment, first_call) *
          UCOS2_inv(sg, task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image)) *
          task_tcb_init_continuation_capsules(environment, saved_local, task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image))
        which implies
          task_tcb_init_continuation_restore_input(environment, critical, saved_local, sg, first_call, cpu_sr,
            acquired, task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image))
        */        OS_EXIT_CRITICAL();
/*@ Assert exists (first_call : OsSchedCallContext) (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage),
          task_tcb_init_stack_same_call(first_call, call) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_tcb_init_runtime_history(sg, call, initial, first_call, acquired) &&
          task_tcb_init_timer_phase_eq(initial, acquired) &&
          kernel_sched_ready_clients(critical) &&
          task_create_default_name_binding(LitMap("?"), initial) && UCOS2_state_inv(sg, initial) &&
          os_sched_call_invocation(first_call) == invocation &&
          os_sched_call_origin(first_call) == origin &&
          args == task_tcb_init_stack_call_args(create_args, LitMap("?")) &&
          os_sched_call_invocation(call) == invocation && os_sched_call_origin(call) == origin &&
          task_create_stack_layout(TaskStackNoVFP, region, create_args, lower, upper) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          task_tcb_init_call_preserved(sg, invocation, initial, acquired) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
          task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
          ptcb == tcb64_addr(sg, slot) &&
          task_tcb_init_modular_restore_output(environment, critical, saved_local, sg, first_call, cpu_sr,
            task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image)) *
          task_stack_storage(region, task_create_stack_image(TaskStackNoVFP, create_args, task_return, lower, upper)) *
          task_tcb_init_retained_storage(ptcb, tcb_layout_common_image(free_image)) *
          undef_data_at(&ptcb->OSTCBStkPtr, OS_STK *) *
          undef_data_at(&ptcb->OSTCBPrio, INT8U) *
          undef_data_at(&ptcb->OSTCBStat, INT8U) *
          undef_data_at(&ptcb->OSTCBStatPend, INT8U) *
          undef_data_at(&ptcb->OSTCBDly, INT32U) *
          undef_data_at(&ptcb->OSTCBExtPtr, void *) *
          undef_data_at(&ptcb->OSTCBStkSize, INT32U) *
          undef_data_at(&ptcb->OSTCBStkBottom, OS_STK *) *
          undef_data_at(&ptcb->OSTCBOpt, INT16U) *
          undef_data_at(&ptcb->OSTCBId, INT16U) *
          undef_data_at(&ptcb->OSTCBDelReq, INT8U) *
          undef_data_at(&ptcb->OSTCBY, INT8U) *
          undef_data_at(&ptcb->OSTCBX, INT8U) *
          undef_data_at(&ptcb->OSTCBBitY, OS_PRIO) *
          undef_data_at(&ptcb->OSTCBBitX, OS_PRIO) *
          undef_data_at(&ptcb->OSTCBEventPtr, OS_EVENT *) *
          undef_data_at(&ptcb->OSTCBFlagNode, OS_FLAG_NODE *) *
          undef_data_at(&ptcb->OSTCBMsg, void *) *
          undef_data_at(&ptcb->OSTCBTaskName, INT8U *) *
          UIntArray::undef_full(ptcb->OSTCBRegTbl, 1) * GlobalStrings_missing(LitMap, literals) *
          undef_data_at(&i, INT8U)
        */        ptcb->OSTCBStkPtr        = ptos;                   /* Load Stack pointer in TCB                */
        ptcb->OSTCBPrio          = prio;                   /* Load task priority into TCB              */
        ptcb->OSTCBStat          = OS_STAT_RDY;            /* Task is ready to run                     */
        ptcb->OSTCBStatPend      = OS_STAT_PEND_OK;        /* Clear pend status                        */
        ptcb->OSTCBDly           = 0u;                     /* Task is not delayed                      */

#if OS_TASK_CREATE_EXT_EN > 0u
        ptcb->OSTCBExtPtr        = pext;                   /* Store pointer to TCB extension           */
        ptcb->OSTCBStkSize       = stk_size;               /* Store stack size                         */
        ptcb->OSTCBStkBottom     = pbos;                   /* Store pointer to bottom of stack         */
        ptcb->OSTCBOpt           = opt;                    /* Store task options                       */
        ptcb->OSTCBId            = id;                     /* Store task ID                            */
#else
        pext                     = pext;                   /* Prevent compiler warning if not used     */
        stk_size                 = stk_size;
        pbos                     = pbos;
        opt                      = opt;
        id                       = id;
#endif

#if OS_TASK_DEL_EN > 0u
        ptcb->OSTCBDelReq        = OS_ERR_NONE;
#endif

#if OS_LOWEST_PRIO <= 63u                                         /* Pre-compute X, Y                  */
        ptcb->OSTCBY             = (INT8U)(prio >> 3u);
        ptcb->OSTCBX             = (INT8U)(prio & 0x07u);
#else                                                             /* Pre-compute X, Y                  */
        ptcb->OSTCBY             = (INT8U)((INT8U)(prio >> 4u) & 0xFFu);
        ptcb->OSTCBX             = (INT8U) (prio & 0x0Fu);
#endif
                                                                  /* Pre-compute BitX and BitY         */
        ptcb->OSTCBBitY          = (OS_PRIO)(1uL << ptcb->OSTCBY);
        ptcb->OSTCBBitX          = (OS_PRIO)(1uL << ptcb->OSTCBX);

#if (OS_EVENT_EN)
        ptcb->OSTCBEventPtr      = (OS_EVENT  *)0;         /* Task is not pending on an  event         */
#if (OS_EVENT_MULTI_EN > 0u)
        ptcb->OSTCBEventMultiPtr = (OS_EVENT **)0;         /* Task is not pending on any events        */
        ptcb->OSTCBEventMultiRdy = (OS_EVENT  *)0;         /* No events readied for Multipend          */
#endif
#endif

#if (OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u) && (OS_TASK_DEL_EN > 0u)
        ptcb->OSTCBFlagNode      = (OS_FLAG_NODE *)0;      /* Task is not pending on an event flag     */
#endif

#if (OS_MBOX_EN > 0u) || ((OS_Q_EN > 0u) && (OS_MAX_QS > 0u))
        ptcb->OSTCBMsg           = (void *)0;              /* No message received                      */
#endif

#if OS_TASK_PROFILE_EN > 0u
        ptcb->OSTCBCtxSwCtr      = 0uL;                    /* Initialize profiling variables           */
        ptcb->OSTCBCyclesStart   = 0uL;
        ptcb->OSTCBCyclesTot     = 0uL;
        ptcb->OSTCBStkBase       = (OS_STK *)0;
        ptcb->OSTCBStkUsed       = 0uL;
#endif

#if OS_TASK_NAME_EN > 0u
        /*@ Given first_call */
        /*@ Given acquired */
        /*@ Given slot */
        /*@ Given rest */
        /*@ Given free_image */
        /*@ task_create_default_name_binding(LitMap("?"), initial) &&
            UCOS2_state_inv(sg, initial) &&
            task_tcb_init_call_preserved(sg, invocation, initial, acquired) &&
            task_tcb_init_modular_restore_output(environment, critical, saved_local, sg, first_call, cpu_sr,
              task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image))
            which implies
            task_create_default_name_binding(LitMap("?"), initial) &&
            UCOS2_state_inv(sg, initial) &&
            task_tcb_init_call_preserved(sg, invocation, initial, acquired) &&
            store_stringLit(LitMap("?"), "?") *
            task_tcb_init_literal_restore_output(environment, critical, saved_local, sg, first_call, cpu_sr,
              task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image), LitMap("?"))
        */
        ptcb->OSTCBTaskName      = (INT8U *)(void *)"?";
        /*@ store_stringLit(LitMap("?"), "?") *
            task_tcb_init_literal_restore_output(environment, critical, saved_local, sg, first_call, cpu_sr,
              task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image), LitMap("?"))
            which implies
            task_tcb_init_modular_restore_output(environment, critical, saved_local, sg, first_call, cpu_sr,
              task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image))
        */
#endif

#if OS_TASK_REG_TBL_SIZE > 0u                              /* Initialize the task variables            */
/*@ Inv Assert exists (first_call : OsSchedCallContext) (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage),
          task_tcb_init_stack_same_call(first_call, call) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_tcb_init_runtime_history(sg, call, initial, first_call, acquired) &&
          task_tcb_init_timer_phase_eq(initial, acquired) &&
          kernel_sched_ready_clients(critical) &&
          task_create_default_name_binding(LitMap("?"), initial) && UCOS2_state_inv(sg, initial) &&
          os_sched_call_invocation(first_call) == invocation &&
          os_sched_call_origin(first_call) == origin &&
          args == task_tcb_init_stack_call_args(create_args, LitMap("?")) &&
          os_sched_call_invocation(call) == invocation && os_sched_call_origin(call) == origin &&
          task_create_stack_layout(TaskStackNoVFP, region, create_args, lower, upper) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          task_tcb_init_call_preserved(sg, invocation, initial, acquired) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
          task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
          ptcb == tcb64_addr(sg, slot) &&
          0 <= i && i <= 1 &&
          task_tcb_init_modular_restore_output(environment, critical, saved_local, sg, first_call, cpu_sr,
            task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image)) *
          task_stack_storage(region, task_create_stack_image(TaskStackNoVFP, create_args, task_return, lower, upper)) *
          task_tcb_init_retained_storage(ptcb, tcb_layout_common_image(free_image)) *
          data_at(&ptcb->OSTCBStkPtr, OS_STK *, ptos) *
          data_at(&ptcb->OSTCBPrio, INT8U, prio) *
          data_at(&ptcb->OSTCBStat, INT8U, 0) *
          data_at(&ptcb->OSTCBStatPend, INT8U, 0) *
          data_at(&ptcb->OSTCBDly, INT32U, 0) *
          data_at(&ptcb->OSTCBExtPtr, void *, pext) *
          data_at(&ptcb->OSTCBStkSize, INT32U, stk_size) *
          data_at(&ptcb->OSTCBStkBottom, OS_STK *, pbos) *
          data_at(&ptcb->OSTCBOpt, INT16U, opt) *
          data_at(&ptcb->OSTCBId, INT16U, id) *
          data_at(&ptcb->OSTCBDelReq, INT8U, 0) *
          data_at(&ptcb->OSTCBY, INT8U, prio / 8) *
          data_at(&ptcb->OSTCBX, INT8U, prio % 8) *
          data_at(&ptcb->OSTCBBitY, OS_PRIO, 1 << (prio / 8)) *
          data_at(&ptcb->OSTCBBitX, OS_PRIO, 1 << (prio % 8)) *
          data_at(&ptcb->OSTCBEventPtr, OS_EVENT *, 0) *
          data_at(&ptcb->OSTCBFlagNode, OS_FLAG_NODE *, 0) *
          data_at(&ptcb->OSTCBMsg, void *, 0) *
          data_at(&ptcb->OSTCBTaskName, INT8U *, LitMap("?")) *
          UIntArray::seg(ptcb->OSTCBRegTbl, 0, i, zeros(i)) *
          UIntArray::undef_seg(ptcb->OSTCBRegTbl, i, 1) * GlobalStrings_missing(LitMap, literals)
        */        for (i = 0u; i < OS_TASK_REG_TBL_SIZE; i++) {
            ptcb->OSTCBRegTbl[i] = 0u;
        }
#endif

/*@ Assert exists (first_call : OsSchedCallContext) (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage),
          task_tcb_init_stack_same_call(first_call, call) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_tcb_init_runtime_history(sg, call, initial, first_call, acquired) &&
          task_tcb_init_timer_phase_eq(initial, acquired) &&
          kernel_sched_ready_clients(critical) &&
          task_create_default_name_binding(LitMap("?"), initial) && UCOS2_state_inv(sg, initial) &&
          os_sched_call_invocation(first_call) == invocation &&
          os_sched_call_origin(first_call) == origin &&
          args == task_tcb_init_stack_call_args(create_args, LitMap("?")) &&
          os_sched_call_invocation(call) == invocation && os_sched_call_origin(call) == origin &&
          task_create_stack_layout(TaskStackNoVFP, region, create_args, lower, upper) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          task_tcb_init_call_preserved(sg, invocation, initial, acquired) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
          task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
          ptcb == tcb64_addr(sg, slot) &&
          i == 1 &&
          task_tcb_init_modular_restore_output(environment, critical, saved_local, sg, first_call, cpu_sr,
            task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image)) *
          task_stack_storage(region, task_create_stack_image(TaskStackNoVFP, create_args, task_return, lower, upper)) *
          tcb64_storage_rep(ptcb, task_tcb_init_raw_image(args, tcb_layout_common_image(free_image))) *
          GlobalStrings_missing(LitMap, literals)
        */        OSTCBInitHook(ptcb)/*@ where frame = GlobalStrings_missing(LitMap, literals) */;

        OSTaskCreateHook(ptcb)/*@ where frame = GlobalStrings_missing(LitMap, literals) */;                            /* Call user defined hook                   */

#if OS_TASK_CREATE_EXT_EN > 0u
#if defined(OS_TLS_TBL_SIZE) && (OS_TLS_TBL_SIZE > 0u)
        for (j = 0u; j < OS_TLS_TBL_SIZE; j++) {
            ptcb->OSTCBTLSTbl[j] = (OS_TLS)0;
        }
        OS_TLS_TaskCreate(ptcb);                           /* Call TLS hook                            */
#endif
#endif

/*@ exists (first_call : OsSchedCallContext) (acquired : UCOS2_Verify_State)
          (slot : Z) (rest : list Z) (free_image : TCBLayoutImage),
          task_tcb_init_stack_same_call(first_call, call) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_tcb_init_runtime_history(sg, call, initial, first_call, acquired) &&
          task_tcb_init_timer_phase_eq(initial, acquired) &&
          kernel_sched_ready_clients(critical) &&
          task_create_default_name_binding(LitMap("?"), initial) && UCOS2_state_inv(sg, initial) &&
          os_sched_call_invocation(call) == invocation && os_sched_call_origin(call) == origin &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
          task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
          task_tcb_init_modular_restore_output(environment, critical, saved_local, sg, first_call, cpu_sr,
            task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image))
        which implies exists (checkpoint_call : OsSchedCallContext) (checkpoint : UCOS2_Verify_State),
          task_tcb_init_stack_same_call(checkpoint_call, call) &&
          task_tcb_init_stack_source_preserved(call, initial, checkpoint) &&
          task_tcb_init_runtime_history(sg, call, initial, checkpoint_call, checkpoint) &&
          task_tcb_init_timer_phase_eq(initial, checkpoint) &&
          kernel_sched_ready_clients(critical) &&
          task_create_default_name_binding(LitMap("?"), initial) && UCOS2_state_inv(sg, initial) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_call_preserved(sg, invocation,
            task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image), checkpoint) &&
          task_tcb_init_continuation_save_input(environment, critical, saved_local, sg, checkpoint_call, mask, checkpoint)
        */        OS_ENTER_CRITICAL();
/*@ Assert exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage) (current : UCOS2_Verify_State),
          task_tcb_init_stack_same_call(current_call, call) &&
          task_tcb_init_stack_source_preserved(call, initial, current) &&
          task_tcb_init_runtime_history(sg, call, initial, current_call, current) &&
          task_tcb_init_timer_phase_eq(initial, current) &&
          kernel_sched_ready_clients(critical) &&
          task_create_default_name_binding(LitMap("?"), initial) && UCOS2_state_inv(sg, initial) &&
          os_sched_call_invocation(current_call) == invocation &&
          os_sched_call_origin(current_call) == origin &&
          args == task_tcb_init_stack_call_args(create_args, LitMap("?")) &&
          os_sched_call_invocation(call) == invocation && os_sched_call_origin(call) == origin &&
          task_create_stack_layout(TaskStackNoVFP, region, create_args, lower, upper) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          task_tcb_init_call_preserved(sg, invocation, initial, acquired) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
          task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
          ptcb == tcb64_addr(sg, slot) &&
          i == 1 && 0 <= prio && prio < 64 &&
          0 <= prio / 8 && prio / 8 < 8 && 0 <= prio % 8 && prio % 8 < 8 &&
          task_tcb_init_call_preserved(sg, invocation,
            task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image), current) &&
          task_tcb_init_commit_binding(args, invocation, origin, acquired, current, slot) &&
          UCOS2_state_inv(sg, current) &&
          task_stack_live_coverage(TskState(current), task_stack_call_active_key(current_call)) &&
          critical_region_masked(task_stack_call_platform(environment), critical, sg, invocation, origin, cpu_sr, current) *
          task_tcb_init_stack_context(environment, current_call) *
          task_tcb_init_continuation_capsules(environment, saved_local, current) *
          task_stack_storage(region, task_create_stack_image(TaskStackNoVFP, create_args, task_return, lower, upper)) *
          task_tcb_init_retained_without_links(ptcb, tcb_layout_common_image(free_image)) *
          data_at(&ptcb->OSTCBStkPtr, OS_STK *, ptos) *
          data_at(&ptcb->OSTCBPrio, INT8U, prio) *
          data_at(&ptcb->OSTCBStat, INT8U, 0) *
          data_at(&ptcb->OSTCBStatPend, INT8U, 0) *
          data_at(&ptcb->OSTCBDly, INT32U, 0) *
          data_at(&ptcb->OSTCBExtPtr, void *, pext) *
          data_at(&ptcb->OSTCBStkSize, INT32U, stk_size) *
          data_at(&ptcb->OSTCBStkBottom, OS_STK *, pbos) *
          data_at(&ptcb->OSTCBOpt, INT16U, opt) *
          data_at(&ptcb->OSTCBId, INT16U, id) *
          data_at(&ptcb->OSTCBDelReq, INT8U, 0) *
          data_at(&ptcb->OSTCBY, INT8U, prio / 8) *
          data_at(&ptcb->OSTCBX, INT8U, prio % 8) *
          data_at(&ptcb->OSTCBBitY, OS_PRIO, 1 << (prio / 8)) *
          data_at(&ptcb->OSTCBBitX, OS_PRIO, 1 << (prio % 8)) *
          data_at(&ptcb->OSTCBEventPtr, OS_EVENT *, 0) *
          data_at(&ptcb->OSTCBFlagNode, OS_FLAG_NODE *, 0) *
          data_at(&ptcb->OSTCBMsg, void *, 0) *
          data_at(&ptcb->OSTCBTaskName, INT8U *, LitMap("?")) *
          UIntArray::full(ptcb->OSTCBRegTbl, 1, zeros(1)) *
          undef_data_at(&ptcb->OSTCBNext, OS_TCB *) *
          undef_data_at(&ptcb->OSTCBPrev, OS_TCB *) *
          data_at(&OSTCBList, OS_TCB *, task_tcb_init_active_head(sg, current)) *
          task_tcb_init_used_storage(sg, current) *
          data_at(&OSTaskCtr, INT8U, task_tcb_init_count(current)) *
          data_at(&OSRdyGrp, OS_PRIO, task_tcb_init_ready_group(current)) *
          UCharArray::full(OSRdyTbl, 8, task_tcb_init_ready_rows(current)) *
          PtrArray::full(OSTCBPrioTbl, 64, task_tcb_init_priority_table(sg, current)) *
          task_tcb_init_publication_other(sg, current) * GlobalStrings_missing(LitMap, literals)
        */        ptcb->OSTCBNext = OSTCBList;                       /* Link into TCB chain                      */
        ptcb->OSTCBPrev = (OS_TCB *)0;
        if (OSTCBList != (OS_TCB *)0) {
/*@ Assert exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage) (current : UCOS2_Verify_State)
                         (head : Z) (previous : Z),
          task_tcb_init_stack_same_call(current_call, call) &&
          task_tcb_init_stack_source_preserved(call, initial, current) &&
          task_tcb_init_runtime_history(sg, call, initial, current_call, current) &&
          task_tcb_init_timer_phase_eq(initial, current) &&
          kernel_sched_ready_clients(critical) &&
          task_create_default_name_binding(LitMap("?"), initial) && UCOS2_state_inv(sg, initial) &&
          os_sched_call_invocation(current_call) == invocation &&
          os_sched_call_origin(current_call) == origin &&
          args == task_tcb_init_stack_call_args(create_args, LitMap("?")) &&
          os_sched_call_invocation(call) == invocation && os_sched_call_origin(call) == origin &&
          task_create_stack_layout(TaskStackNoVFP, region, create_args, lower, upper) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          task_tcb_init_call_preserved(sg, invocation, initial, acquired) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
          task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
          ptcb == tcb64_addr(sg, slot) &&
          i == 1 && 0 <= prio && prio < 64 &&
          0 <= prio / 8 && prio / 8 < 8 && 0 <= prio % 8 && prio % 8 < 8 &&
          task_tcb_init_call_preserved(sg, invocation,
            task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image), current) &&
          task_tcb_init_commit_binding(args, invocation, origin, acquired, current, slot) &&
          UCOS2_state_inv(sg, current) &&
          head == task_tcb_init_active_head(sg, current) && head != 0 &&
          task_stack_live_coverage(TskState(current), task_stack_call_active_key(current_call)) &&
          critical_region_masked(task_stack_call_platform(environment), critical, sg, invocation, origin, cpu_sr, current) *
          task_tcb_init_stack_context(environment, current_call) *
          task_tcb_init_continuation_capsules(environment, saved_local, current) *
          task_stack_storage(region, task_create_stack_image(TaskStackNoVFP, create_args, task_return, lower, upper)) *
          task_tcb_init_retained_without_links(ptcb, tcb_layout_common_image(free_image)) *
          data_at(&ptcb->OSTCBStkPtr, OS_STK *, ptos) *
          data_at(&ptcb->OSTCBPrio, INT8U, prio) *
          data_at(&ptcb->OSTCBStat, INT8U, 0) *
          data_at(&ptcb->OSTCBStatPend, INT8U, 0) *
          data_at(&ptcb->OSTCBDly, INT32U, 0) *
          data_at(&ptcb->OSTCBExtPtr, void *, pext) *
          data_at(&ptcb->OSTCBStkSize, INT32U, stk_size) *
          data_at(&ptcb->OSTCBStkBottom, OS_STK *, pbos) *
          data_at(&ptcb->OSTCBOpt, INT16U, opt) *
          data_at(&ptcb->OSTCBId, INT16U, id) *
          data_at(&ptcb->OSTCBDelReq, INT8U, 0) *
          data_at(&ptcb->OSTCBY, INT8U, prio / 8) *
          data_at(&ptcb->OSTCBX, INT8U, prio % 8) *
          data_at(&ptcb->OSTCBBitY, OS_PRIO, 1 << (prio / 8)) *
          data_at(&ptcb->OSTCBBitX, OS_PRIO, 1 << (prio % 8)) *
          data_at(&ptcb->OSTCBEventPtr, OS_EVENT *, 0) *
          data_at(&ptcb->OSTCBFlagNode, OS_FLAG_NODE *, 0) *
          data_at(&ptcb->OSTCBMsg, void *, 0) *
          data_at(&ptcb->OSTCBTaskName, INT8U *, LitMap("?")) *
          UIntArray::full(ptcb->OSTCBRegTbl, 1, zeros(1)) *
          data_at(&ptcb->OSTCBNext, OS_TCB *, task_tcb_init_active_head(sg, current)) *
          data_at(&ptcb->OSTCBPrev, OS_TCB *, 0) *
          data_at(&OSTCBList, OS_TCB *, head) *
          data_at(&((OS_TCB *)head)->OSTCBPrev, OS_TCB *, previous) *
          task_tcb_init_used_without_head_prev(sg, current) *
          data_at(&OSTaskCtr, INT8U, task_tcb_init_count(current)) *
          data_at(&OSRdyGrp, OS_PRIO, task_tcb_init_ready_group(current)) *
          UCharArray::full(OSRdyTbl, 8, task_tcb_init_ready_rows(current)) *
          PtrArray::full(OSTCBPrioTbl, 64, task_tcb_init_priority_table(sg, current)) *
          task_tcb_init_publication_other(sg, current) * GlobalStrings_missing(LitMap, literals)
            */            OSTCBList->OSTCBPrev = ptcb;
        }
/*@ Assert exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage) (current : UCOS2_Verify_State),
          task_tcb_init_stack_same_call(current_call, call) &&
          task_tcb_init_stack_source_preserved(call, initial, current) &&
          task_tcb_init_runtime_history(sg, call, initial, current_call, current) &&
          task_tcb_init_timer_phase_eq(initial, current) &&
          kernel_sched_ready_clients(critical) &&
          task_create_default_name_binding(LitMap("?"), initial) && UCOS2_state_inv(sg, initial) &&
          os_sched_call_invocation(current_call) == invocation &&
          os_sched_call_origin(current_call) == origin &&
          args == task_tcb_init_stack_call_args(create_args, LitMap("?")) &&
          os_sched_call_invocation(call) == invocation && os_sched_call_origin(call) == origin &&
          task_create_stack_layout(TaskStackNoVFP, region, create_args, lower, upper) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          task_tcb_init_call_preserved(sg, invocation, initial, acquired) &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_entry(sg, args, invocation, origin, acquired) &&
          task_tcb_init_detach_observation(args, invocation, origin, acquired, slot, rest, free_image) &&
          ptcb == tcb64_addr(sg, slot) &&
          i == 1 && 0 <= prio && prio < 64 &&
          0 <= prio / 8 && prio / 8 < 8 && 0 <= prio % 8 && prio % 8 < 8 &&
          task_tcb_init_call_preserved(sg, invocation,
            task_tcb_init_detached_state(args, invocation, origin, acquired, slot, rest, free_image), current) &&
          task_tcb_init_commit_binding(args, invocation, origin, acquired, current, slot) &&
          UCOS2_state_inv(sg, current) &&
          task_stack_live_coverage(TskState(current), task_stack_call_active_key(current_call)) &&
          critical_region_masked(task_stack_call_platform(environment), critical, sg, invocation, origin, cpu_sr, current) *
          task_tcb_init_stack_context(environment, current_call) *
          task_tcb_init_continuation_capsules(environment, saved_local, current) *
          task_stack_storage(region, task_create_stack_image(TaskStackNoVFP, create_args, task_return, lower, upper)) *
          task_tcb_init_retained_without_links(ptcb, tcb_layout_common_image(free_image)) *
          data_at(&ptcb->OSTCBStkPtr, OS_STK *, ptos) *
          data_at(&ptcb->OSTCBPrio, INT8U, prio) *
          data_at(&ptcb->OSTCBStat, INT8U, 0) *
          data_at(&ptcb->OSTCBStatPend, INT8U, 0) *
          data_at(&ptcb->OSTCBDly, INT32U, 0) *
          data_at(&ptcb->OSTCBExtPtr, void *, pext) *
          data_at(&ptcb->OSTCBStkSize, INT32U, stk_size) *
          data_at(&ptcb->OSTCBStkBottom, OS_STK *, pbos) *
          data_at(&ptcb->OSTCBOpt, INT16U, opt) *
          data_at(&ptcb->OSTCBId, INT16U, id) *
          data_at(&ptcb->OSTCBDelReq, INT8U, 0) *
          data_at(&ptcb->OSTCBY, INT8U, prio / 8) *
          data_at(&ptcb->OSTCBX, INT8U, prio % 8) *
          data_at(&ptcb->OSTCBBitY, OS_PRIO, 1 << (prio / 8)) *
          data_at(&ptcb->OSTCBBitX, OS_PRIO, 1 << (prio % 8)) *
          data_at(&ptcb->OSTCBEventPtr, OS_EVENT *, 0) *
          data_at(&ptcb->OSTCBFlagNode, OS_FLAG_NODE *, 0) *
          data_at(&ptcb->OSTCBMsg, void *, 0) *
          data_at(&ptcb->OSTCBTaskName, INT8U *, LitMap("?")) *
          UIntArray::full(ptcb->OSTCBRegTbl, 1, zeros(1)) *
          data_at(&ptcb->OSTCBNext, OS_TCB *, task_tcb_init_active_head(sg, current)) *
          data_at(&ptcb->OSTCBPrev, OS_TCB *, 0) *
          data_at(&OSTCBList, OS_TCB *, task_tcb_init_active_head(sg, current)) *
          task_tcb_init_used_with_head_prev(sg, current, slot) *
          data_at(&OSTaskCtr, INT8U, task_tcb_init_count(current)) *
          data_at(&OSRdyGrp, OS_PRIO, task_tcb_init_ready_group(current)) *
          UCharArray::full(OSRdyTbl, 8, task_tcb_init_ready_rows(current)) *
          PtrArray::full(OSTCBPrioTbl, 64, task_tcb_init_priority_table(sg, current)) *
          task_tcb_init_publication_other(sg, current) * GlobalStrings_missing(LitMap, literals)
        */        OSTCBList               = ptcb;
        OSRdyGrp               |= ptcb->OSTCBBitY;         /* Make task ready to run                   */
        OSRdyTbl[ptcb->OSTCBY] |= ptcb->OSTCBBitX;
        OSTaskCtr++;                                       /* Increment the #tasks counter             */
        OSTCBPrioTbl[prio] = ptcb;                         /* Publish only the fully linked ready TCB  */
        OS_TRACE_TASK_READY(ptcb);
/*@ Assert exists (current_call : OsSchedCallContext) (acquired : UCOS2_Verify_State) (slot : Z)
                          (rest : list Z) (free_image : TCBLayoutImage) (current : UCOS2_Verify_State) (lease : TaskStackLease),
          task_tcb_init_stack_same_call(current_call, call) &&
          task_tcb_init_stack_source_preserved(call, initial, current) &&
          task_tcb_init_runtime_history(sg, call, initial, current_call, current) &&
          task_tcb_init_timer_phase_eq(initial, current) &&
          kernel_sched_ready_clients(critical) &&
          task_create_default_name_binding(LitMap("?"), initial) && UCOS2_state_inv(sg, initial) &&
          os_sched_call_invocation(current_call) == invocation &&
          os_sched_call_origin(current_call) == origin &&
          args == task_tcb_init_stack_call_args(create_args, LitMap("?")) &&
          os_sched_call_invocation(call) == invocation && os_sched_call_origin(call) == origin &&
          task_create_stack_layout(TaskStackNoVFP, region, create_args, lower, upper) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          interrupt_saved_value(mask, cpu_sr) && i == 1 &&
          task_tcb_init_stack_call_result(critical, sg, region, create_args, task_return, lower, upper,
            LitMap("?"), invocation, origin, initial, 0,
            task_create_stack_publication_state(sg, task_tcb_init_stack_publication(region, create_args, task_return, lower, upper, LitMap("?"), invocation, origin, acquired, slot, free_image, lease), current)) &&
          UCOS2_state_inv(sg, task_create_stack_publication_state(sg, task_tcb_init_stack_publication(region, create_args, task_return, lower, upper, LitMap("?"), invocation, origin, acquired, slot, free_image, lease), current)) &&
          task_tcb_init_stack_source_preserved(call, initial, task_create_stack_publication_state(sg, task_tcb_init_stack_publication(region, create_args, task_return, lower, upper, LitMap("?"), invocation, origin, acquired, slot, free_image, lease), current)) &&
          task_tcb_init_publication_call_observation(sg,
            task_tcb_init_stack_publication(region, create_args, task_return, lower, upper, LitMap("?"), invocation, origin, acquired, slot, free_image, lease), current_call, current) &&
          task_stack_live_coverage(TskState(task_create_stack_publication_state(sg, task_tcb_init_stack_publication(region, create_args, task_return, lower, upper, LitMap("?"), invocation, origin, acquired, slot, free_image, lease), current)), task_stack_call_active_key(current_call)) &&
          critical_region_masked(task_stack_call_platform(environment), critical, sg, invocation, origin, cpu_sr, current) *
          task_tcb_init_stack_context(environment, current_call) *
          UCOS2_inv(sg, task_create_stack_publication_state(sg, task_tcb_init_stack_publication(region, create_args, task_return, lower, upper, LitMap("?"), invocation, origin, acquired, slot, free_image, lease), current)) *
          task_tcb_init_continuation_capsules(environment, saved_local, task_create_stack_publication_state(sg, task_tcb_init_stack_publication(region, create_args, task_return, lower, upper, LitMap("?"), invocation, origin, acquired, slot, free_image, lease), current)) *
          GlobalStrings_missing(LitMap, literals) * undef_data_at(&ptcb, OS_TCB *)
        *//*@ exists (current_call : OsSchedCallContext) (acquired current : UCOS2_Verify_State)
          (slot : Z) (free_image : TCBLayoutImage) (lease : TaskStackLease),
          os_sched_call_invocation(current_call) == invocation &&
          os_sched_call_origin(current_call) == origin &&
          task_stack_live_coverage(TskState(task_create_stack_publication_state(sg, task_tcb_init_stack_publication(region, create_args, task_return, lower, upper, LitMap("?"), invocation, origin, acquired, slot, free_image, lease), current)), task_stack_call_active_key(current_call)) &&
          critical_region_masked(task_stack_call_platform(environment), critical, sg, invocation, origin, cpu_sr, current) *
          task_tcb_init_stack_context(environment, current_call) *
          UCOS2_inv(sg, task_create_stack_publication_state(sg, task_tcb_init_stack_publication(region, create_args, task_return, lower, upper, LitMap("?"), invocation, origin, acquired, slot, free_image, lease), current)) *
          task_tcb_init_continuation_capsules(environment, saved_local, task_create_stack_publication_state(sg, task_tcb_init_stack_publication(region, create_args, task_return, lower, upper, LitMap("?"), invocation, origin, acquired, slot, free_image, lease), current))
        which implies
          task_tcb_init_continuation_restore_input(environment, critical, saved_local, sg, current_call, cpu_sr,
            current, task_create_stack_publication_state(sg, task_tcb_init_stack_publication(region, create_args, task_return, lower, upper, LitMap("?"), invocation, origin, acquired, slot, free_image, lease), current))
        */        OS_EXIT_CRITICAL();
        return (OS_ERR_NONE);
    }
/*@ Assert exists (first_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          task_tcb_init_stack_same_call(first_call, call) &&
          task_tcb_init_stack_source_preserved(call, initial, acquired) &&
          task_tcb_init_runtime_history(sg, call, initial, first_call, acquired) &&
          task_tcb_init_timer_phase_eq(initial, acquired) &&
          kernel_sched_ready_clients(critical) &&
          task_create_default_name_binding(LitMap("?"), initial) && UCOS2_state_inv(sg, initial) &&
          os_sched_call_invocation(first_call) == invocation &&
          os_sched_call_origin(first_call) == origin &&
          args == task_tcb_init_stack_call_args(create_args, LitMap("?")) &&
          os_sched_call_invocation(call) == invocation && os_sched_call_origin(call) == origin &&
          task_create_stack_layout(TaskStackNoVFP, region, create_args, lower, upper) &&
          task_tcb_init_global_addresses(sg, &OSTCBFreeList, &OSTCBList,
            OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
          task_tcb_init_arguments(args, prio, ptos, pbos, id, stk_size, pext, opt, LitMap("?")) &&
          prio == prio@pre && ptos == ptos@pre && pbos == pbos@pre &&
          id == id@pre && stk_size == stk_size@pre && pext == pext@pre && opt == opt@pre &&
          interrupt_saved_value(mask, cpu_sr) &&
          task_tcb_init_call_result(sg, args, invocation, origin, initial, 66, acquired) &&
          UCOS2_state_inv(sg, acquired) &&
          task_stack_live_coverage(TskState(acquired), task_stack_call_active_key(first_call)) &&
          critical_region_masked(task_stack_call_platform(environment), critical, sg, invocation, origin, cpu_sr, acquired) *
          task_tcb_init_stack_context(environment, first_call) *
          task_tcb_init_continuation_capsules(environment, saved_local, acquired) *
          task_stack_storage(region, task_create_stack_image(TaskStackNoVFP, create_args, task_return, lower, upper)) *
          UCOS2_inv(sg, acquired) * GlobalStrings_missing(LitMap, literals) *
          undef_data_at(&ptcb, OS_TCB *) * undef_data_at(&i, INT8U)
    *//*@ exists (first_call : OsSchedCallContext) (acquired : UCOS2_Verify_State),
          os_sched_call_invocation(first_call) == invocation &&
          os_sched_call_origin(first_call) == origin &&
          task_stack_live_coverage(TskState(acquired), task_stack_call_active_key(first_call)) &&
          critical_region_masked(task_stack_call_platform(environment), critical, sg, invocation, origin, cpu_sr, acquired) *
          task_tcb_init_stack_context(environment, first_call) *
          UCOS2_inv(sg, acquired) *
          task_tcb_init_continuation_capsules(environment, saved_local, acquired)
        which implies
          task_tcb_init_continuation_restore_input(environment, critical, saved_local, sg, first_call, cpu_sr,
            acquired, acquired)
        */    OS_EXIT_CRITICAL();
    return (OS_ERR_TASK_NO_MORE_TCB);
}
