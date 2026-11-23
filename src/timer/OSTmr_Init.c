/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSTmr_Init (void)
/*@ With (p : TmrInitContext) (call : OsSchedCallContext)
         (initial : UCOS2_Verify_State) (LitMap : String -> Z) (X : unit -> UCOS2_Verify_State -> Prop)
    Require LitMap == tmr_init_literals(p) && tmr_init_pre(p, call, initial, X)
    Ensure tmr_init_post(p, call, X)
*/
{
#if OS_EVENT_NAME_EN > 0u
    INT8U    err;
#endif
    INT16U   ix;
    INT16U   ix_next;
    OS_TMR  *ptmr1;
    OS_TMR  *ptmr2;


    /*@ tmr_init_pre(p, call, initial, X)
        which implies
        0 <= sizeof(struct os_tmr[16]) && sizeof(struct os_tmr[16]) <= 65535 &&
        0 <= pointer_offset(&OSTmrTbl, 0, struct os_tmr) &&
        pointer_offset(pointer_offset(&OSTmrTbl, 0, struct os_tmr), sizeof(struct os_tmr[16]), unsigned char) <= 4294967295 &&
        0 <= sizeof(struct os_tmr_wheel[7]) && sizeof(struct os_tmr_wheel[7]) <= 65535 &&
        0 <= pointer_offset(&OSTmrWheelTbl, 0, struct os_tmr_wheel) &&
        pointer_offset(pointer_offset(&OSTmrWheelTbl, 0, struct os_tmr_wheel), sizeof(struct os_tmr_wheel[7]), unsigned char) <= 4294967295 &&
        mem_clr_pre(pointer_offset(&OSTmrTbl, 0, struct os_tmr), sizeof(struct os_tmr[16])) *
        mem_clr_pre(pointer_offset(&OSTmrWheelTbl, 0, struct os_tmr_wheel), sizeof(struct os_tmr_wheel[7])) *
        tmr_init_globals(tmr_init_sg(p), 0, 0, 0, 0, 0, 0) *
        tmr_init_pool_context(p, call, initial, X)
    */
    OS_MemClr((INT8U *)&OSTmrTbl[0],      sizeof(OSTmrTbl));            /* Clear all the TMRs                         */
    OS_MemClr((INT8U *)&OSTmrWheelTbl[0], sizeof(OSTmrWheelTbl));       /* Clear the timer wheel                      */

    /*@ LitMap == tmr_init_literals(p) &&
        mem_clr_post(pointer_offset(&OSTmrTbl, 0, struct os_tmr), sizeof(struct os_tmr[16])) *
        mem_clr_post(pointer_offset(&OSTmrWheelTbl, 0, struct os_tmr_wheel), sizeof(struct os_tmr_wheel[7])) *
        tmr_init_globals(tmr_init_sg(p), 0, 0, 0, 0, 0, 0) *
        tmr_init_pool_context(p, call, initial, X)
        which implies
        tmr_init_loop(tmr_init_sg(p), tmr_init_question(p), 0) *
        store_stringLit(LitMap("?"), "?") *
        GlobalStrings_missing(LitMap, tmr_init_missing_literals(p)) *
        tmr_init_pool_literal_residual(p, call, initial, X)
    */
    /*@ Inv Assert LitMap == tmr_init_literals(p) && 0 <= ix && ix <= 15 &&
        tmr_init_loop(tmr_init_sg(p), tmr_init_question(p), ix) *
        store_stringLit(LitMap("?"), "?") *
        GlobalStrings_missing(LitMap, tmr_init_missing_literals(p)) *
        tmr_init_pool_literal_residual(p, call, initial, X) *
        has_permission(&ix_next) * has_permission(&ptmr1) * has_permission(&ptmr2)
    */
    for (ix = 0u; ix < (OS_TMR_CFG_MAX - 1u); ix++) {                   /* Init. list of free TMRs                    */
        ix_next = ix + 1u;
        ptmr1 = &OSTmrTbl[ix];
        ptmr2 = &OSTmrTbl[ix_next];
        /*@ 0 <= ix && ix < 15 &&
            ptmr1 == pointer_offset(&OSTmrTbl, ix, struct os_tmr) &&
            ptmr2 == pointer_offset(&OSTmrTbl, ix + 1, struct os_tmr) &&
            tmr_init_loop(tmr_init_sg(p), tmr_init_question(p), ix) *
            tmr_init_pool_literal_residual(p, call, initial, X)
            which implies
            ptmr1 == pointer_offset(&OSTmrTbl, ix, struct os_tmr) &&
            ptmr2 == pointer_offset(&OSTmrTbl, ix + 1, struct os_tmr) &&
            data_at(&ptmr1->OSTmrType, INT8U, 0) * data_at(&ptmr1->OSTmrState, INT8U, 0) *
            data_at(&ptmr1->OSTmrNext, void *, 0) * data_at(&ptmr1->OSTmrName, INT8U *, 0) *
            tmr_init_slot_context(tmr_init_sg(p), tmr_init_question(p), ix) *
            tmr_init_pool_literal_residual(p, call, initial, X)
        */
        ptmr1->OSTmrType    = OS_TMR_TYPE;
        ptmr1->OSTmrState   = OS_TMR_STATE_UNUSED;                      /* Indicate that timer is inactive            */
        ptmr1->OSTmrNext    = (void *)ptmr2;                            /* Link to next timer                         */
#if OS_TMR_CFG_NAME_EN > 0u
        ptmr1->OSTmrName    = (INT8U *)(void *)"?";
#endif
        /*@ LitMap == tmr_init_literals(p) && 0 <= ix && ix < 15 &&
            ptmr1 == pointer_offset(&OSTmrTbl, ix, struct os_tmr) &&
            ptmr2 == pointer_offset(&OSTmrTbl, ix + 1, struct os_tmr) &&
            data_at(&ptmr1->OSTmrType, INT8U, 100) * data_at(&ptmr1->OSTmrState, INT8U, 0) *
            data_at(&ptmr1->OSTmrNext, void *, ptmr2) *
            data_at(&ptmr1->OSTmrName, INT8U *, pointer_offset(LitMap("?"), 0, char)) *
            tmr_init_slot_context(tmr_init_sg(p), tmr_init_question(p), ix) *
            tmr_init_pool_literal_residual(p, call, initial, X)
            which implies
            ptmr1 == pointer_offset(&OSTmrTbl, ix, struct os_tmr) &&
            ptmr2 == pointer_offset(&OSTmrTbl, ix + 1, struct os_tmr) &&
            tmr_init_loop(tmr_init_sg(p), tmr_init_question(p), ix + 1) *
            tmr_init_pool_literal_residual(p, call, initial, X)
        */
    }
    ptmr1               = &OSTmrTbl[ix];
    /*@ 0 <= ix && ix <= 15 && ix >= 15 &&
        ptmr1 == pointer_offset(&OSTmrTbl, ix, struct os_tmr) &&
        tmr_init_loop(tmr_init_sg(p), tmr_init_question(p), ix) *
        tmr_init_pool_literal_residual(p, call, initial, X)
        which implies ix == 15 && ptmr1 == pointer_offset(&OSTmrTbl, ix, struct os_tmr) &&
        data_at(&ptmr1->OSTmrType, INT8U, 0) * data_at(&ptmr1->OSTmrState, INT8U, 0) *
        data_at(&ptmr1->OSTmrNext, void *, 0) * data_at(&ptmr1->OSTmrName, INT8U *, 0) *
        tmr_init_slot_context(tmr_init_sg(p), tmr_init_question(p), ix) *
        tmr_init_pool_literal_residual(p, call, initial, X)
    */
    ptmr1->OSTmrType    = OS_TMR_TYPE;
    ptmr1->OSTmrState   = OS_TMR_STATE_UNUSED;                          /* Indicate that timer is inactive            */
    ptmr1->OSTmrNext    = (void *)0;                                    /* Last OS_TMR                                */
#if OS_TMR_CFG_NAME_EN > 0u
    ptmr1->OSTmrName    = (INT8U *)(void *)"?";
#endif
    /*@ LitMap == tmr_init_literals(p) && 0 <= ix && ix <= 15 && ix >= 15 &&
        ptmr1 == pointer_offset(&OSTmrTbl, ix, struct os_tmr) &&
        data_at(&ptmr1->OSTmrType, INT8U, 100) * data_at(&ptmr1->OSTmrState, INT8U, 0) *
        data_at(&ptmr1->OSTmrNext, void *, 0) *
        data_at(&ptmr1->OSTmrName, INT8U *, pointer_offset(LitMap("?"), 0, char)) *
        tmr_init_slot_context(tmr_init_sg(p), tmr_init_question(p), ix) *
        store_stringLit(LitMap("?"), "?") *
        GlobalStrings_missing(LitMap, tmr_init_missing_literals(p)) *
        tmr_init_pool_literal_residual(p, call, initial, X)
        which implies
        ptmr1 == pointer_offset(&OSTmrTbl, ix, struct os_tmr) &&
        tmr_init_globals_context(tmr_init_sg(p), tmr_init_question(p)) *
        data_at(&OSTmrTime, INT32U, 0) * data_at(&OSTmrUsed, INT16U, 0) *
        data_at(&OSTmrFree, INT16U, 0) * data_at(&OSTmrFreeList, OS_TMR *, 0) *
        data_at(&OSTmrSem, OS_EVENT *, 0) * data_at(&OSTmrSemSignal, OS_EVENT *, 0) *
        tmr_init_pool_context(p, call, initial, X)
    */
    OSTmrTime           = 0u;
    OSTmrUsed           = 0u;
    OSTmrFree           = OS_TMR_CFG_MAX;
    OSTmrFreeList       = &OSTmrTbl[0];
    /*@ tmr_init_globals_context(tmr_init_sg(p), tmr_init_question(p)) *
        data_at(&OSTmrTime, INT32U, 0) * data_at(&OSTmrUsed, INT16U, 0) *
        data_at(&OSTmrFree, INT16U, 16) *
        data_at(&OSTmrFreeList, OS_TMR *, pointer_offset(&OSTmrTbl, 0, struct os_tmr)) *
        data_at(&OSTmrSem, OS_EVENT *, 0) * data_at(&OSTmrSemSignal, OS_EVENT *, 0) *
        tmr_init_pool_context(p, call, initial, X)
        which implies coq_prop(tmr_init_source_binding(p)) &&
        tmr_init_sem_pre(p, call, tmr_init_after_pool(p, initial), true,
          tmr_init_sem_continuation(p, call, true, X)) * tmr_init_static_resources(p)
    */
    OSTmrSem            = OSSemCreate(1u)
    /*@ where(timer_lock_spec) p=p, call=call, before=tmr_init_after_pool(p, initial),
        K=tmr_init_sem_continuation(p, call, true, X) */;
    /*@ exists (returned : OsSchedCallContext) (current : UCOS2_Verify_State) (lock_result : Z),
        coq_prop(tmr_init_sem_return_facts(p, call, tmr_init_after_pool(p, initial), true,
          tmr_init_sem_continuation(p, call, true, X), lock_result, returned, current)) &&
        data_at(&OSTmrSem, OS_EVENT *, lock_result) * tmr_init_sem_return_frame(p, returned, current, true)
        which implies exists (lock_call : OsSchedCallContext) (lock_state : UCOS2_Verify_State),
        coq_prop(task_tcb_init_stack_same_call(lock_call, call)) &&
        tmr_init_sem_pre(p, lock_call, lock_state, false, tmr_init_sem_continuation(p, call, false, X))
    */
    /*@ Given lock_call lock_state */
    OSTmrSemSignal      = OSSemCreate(0u)
    /*@ where(timer_signal_spec) p=p, call=lock_call, before=lock_state,
        K=tmr_init_sem_continuation(p, call, false, X) */;

#if OS_EVENT_NAME_EN > 0u                                               /* Assign names to semaphores                 */
    OSEventNameSet(OSTmrSem,       (INT8U *)(void *)"uC/OS-II TmrLock",   &err);
    OSEventNameSet(OSTmrSemSignal, (INT8U *)(void *)"uC/OS-II TmrSignal", &err);
#endif

    /*@ coq_prop(task_tcb_init_stack_same_call(lock_call, call)) &&
        exists (returned : OsSchedCallContext) (current : UCOS2_Verify_State) (signal_result : Z),
        coq_prop(tmr_init_sem_return_facts(p, lock_call, lock_state, false,
          tmr_init_sem_continuation(p, call, false, X), signal_result, returned, current)) &&
        data_at(&OSTmrSemSignal, OS_EVENT *, signal_result) *
        tmr_init_sem_return_frame(p, returned, current, false) * tmr_init_static_resources(p)
        which implies exists (task_call : OsSchedCallContext) (task_state : UCOS2_Verify_State),
        coq_prop(task_tcb_init_stack_same_call(task_call, call)) &&
        tmr_init_task_pre(p, task_call, task_state, X)
    */
    /*@ Given task_call task_state */
    OSTmr_InitTask()
    /*@ where(timer_init_spec) p=p, call=task_call, before=task_state, X=X */;
    /*@ coq_prop(task_tcb_init_stack_same_call(task_call, call)) &&
        tmr_init_task_return(p, task_call, task_state, X)
        which implies tmr_init_post(p, call, X)
    */
}
