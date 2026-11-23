/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSInit (void)
/*@ With (p : OsInitContext) (X : unit -> OsInitState -> Prop)
    Require os_init_pre(p, X)
    Ensure os_init_post(p, X)
*/
{
#if OS_TASK_CREATE_EXT_EN > 0u
#if defined(OS_TLS_TBL_SIZE) && (OS_TLS_TBL_SIZE > 0u)
    INT8U  err;
#endif
#endif

    /*@ os_init_pre(p, X)
        which implies
        os_init_hook_port_pre(&OS_CPU_ExceptStk, &OS_CPU_ExceptStkBase, &OS_CPU_ARM_DRegCnt, os_init_exception_initial(p), os_init_raw_call_frame(p, O, X)) * GlobalStrings(os_init_literals(p))
    */
    OSInitHookBegin()/*@ where base=&OS_CPU_ExceptStk, initial=os_init_exception_initial(p), R=os_init_raw_call_frame(p, O, X) */;
    /*@ os_init_hook_port_post(&OS_CPU_ExceptStk, &OS_CPU_ExceptStkBase, &OS_CPU_ARM_DRegCnt, os_init_raw_call_frame(p, O, X)) * GlobalStrings(os_init_literals(p))
        which implies
        os_init_raw_stage(p, S(O), X)
    */                                           /* Call port specific initialization code   */

    /*@ os_init_raw_stage(p, S(O), X)
        which implies
        &OSTime == g_OSTime(os_init_sg(p)) &&
        &OSIntNesting == g_OSIntNesting(os_init_sg(p)) &&
        &OSLockNesting == g_OSLockNesting(os_init_sg(p)) &&
        &OSTaskCtr == g_OSTaskCtr(os_init_sg(p)) &&
        &OSRunning == g_OSRunning(os_init_sg(p)) &&
        &OSCtxSwCtr == g_OSCtxSwCtr(os_init_sg(p)) &&
        &OSIdleCtr == g_OSIdleCtr(os_init_sg(p)) &&
        &OSIdleCtrRun == g_OSIdleCtrRun(os_init_sg(p)) &&
        &OSIdleCtrMax == g_OSIdleCtrMax(os_init_sg(p)) &&
        &OSStatRdy == g_OSStatRdy(os_init_sg(p)) &&
        &OSTaskRegNextAvailID == g_OSTaskRegNextAvailID(os_init_sg(p)) &&
        undef_data_at(&OSTime, INT32U) *
        undef_data_at(&OSIntNesting, INT8U) *
        undef_data_at(&OSLockNesting, INT8U) *
        undef_data_at(&OSTaskCtr, INT8U) *
        undef_data_at(&OSRunning, BOOLEAN) *
        undef_data_at(&OSCtxSwCtr, INT32U) *
        undef_data_at(&OSIdleCtr, INT32U) *
        undef_data_at(&OSIdleCtrRun, INT32U) *
        undef_data_at(&OSIdleCtrMax, INT32U) *
        undef_data_at(&OSStatRdy, BOOLEAN) *
        undef_data_at(&OSTaskRegNextAvailID, INT8U) * os_init_raw_call_frame(p, S(O), X) * GlobalStrings(os_init_literals(p))
    */
    OS_InitMisc()/*@ where sg=os_init_sg(p), R=os_init_raw_call_frame(p, S(O), X) */;
    /*@ init_misc_zero(os_init_sg(p)) * os_init_raw_call_frame(p, S(O), X) * GlobalStrings(os_init_literals(p))
        which implies
        os_init_raw_stage(p, S(S(O)), X)
    */                                               /* Initialize miscellaneous variables       */

    /*@ os_init_raw_stage(p, S(S(O)), X)
        which implies
        init_rdy_list_pre(&OSRdyGrp, &OSRdyTbl, &OSPrioCur, &OSPrioHighRdy, &OSTCBHighRdy, &OSTCBCur) * os_init_raw_call_frame(p, S(S(O)), X) * GlobalStrings(os_init_literals(p))
    */
    OS_InitRdyList();
    /*@ init_rdy_list_post(&OSRdyGrp, &OSRdyTbl, &OSPrioCur, &OSPrioHighRdy, &OSTCBHighRdy, &OSTCBCur) * os_init_raw_call_frame(p, S(S(O)), X) * GlobalStrings(os_init_literals(p))
        which implies
        os_init_raw_stage(p, S(S(S(O))), X)
    */                                            /* Initialize the Ready List                */

    /*@ os_init_raw_stage(p, S(S(S(O))), X)
        which implies
        init_tcb_list_profile(os_init_sg(p)) && init_tcb_list_global_addresses(os_init_sg(p), OSTCBTbl, OSTCBPrioTbl, &OSTCBList, &OSTCBFreeList) && init_tcb_list_layout(os_init_sg(p)) &&
        init_tcb_list_pre(os_init_sg(p)) * GlobalStrings(os_init_literals(p)) * os_init_raw_call_frame(p, S(S(S(O))), X)
    */
    OS_InitTCBList()/*@ where sg=os_init_sg(p), LitMap=os_init_literals(p) */;
    /*@ init_tcb_list_post(os_init_sg(p), os_init_literals(p)("?")) * GlobalStrings(os_init_literals(p)) * os_init_raw_call_frame(p, S(S(S(O))), X)
        which implies
        os_init_raw_stage(p, S(S(S(S(O)))), X)
    */                                            /* Initialize the free list of OS_TCBs      */

    /*@ os_init_raw_stage(p, S(S(S(S(O)))), X)
        which implies
        osMaxEvents(os_init_sg(p)) == 10 && g_OSEventTbl(os_init_sg(p)) == OSEventTbl && g_OSEventFreeList(os_init_sg(p)) == &OSEventFreeList && sizeof(struct os_event) == 20 && sizeof(struct os_event[10]) == 200 && 0 <= g_OSEventTbl(os_init_sg(p)) && g_OSEventTbl(os_init_sg(p)) + 200 <= 4294967295 && g_OSEventTbl(os_init_sg(p)) % 4 == 0 && event_table_layout_prop(os_init_sg(p)) && init_event_list_profile(os_init_sg(p)) &&
        init_event_list_pre(os_init_sg(p)) * GlobalStrings(os_init_literals(p)) * os_init_raw_call_frame(p, S(S(S(S(O)))), X)
    */
    OS_InitEventList()/*@ where sg=os_init_sg(p) */;
    /*@ init_event_list_post(os_init_sg(p)) * GlobalStrings(os_init_literals(p)) * os_init_raw_call_frame(p, S(S(S(S(O)))), X)
        which implies
        os_init_raw_stage(p, S(S(S(S(S(O))))), X)
    */                                          /* Initialize the free list of OS_EVENTs    */

#if (OS_FLAG_EN > 0u) && (OS_MAX_FLAGS > 0u)
    /*@ os_init_raw_stage(p, S(S(S(S(S(O))))), X)
        which implies
        flag_init_profile(os_init_sg(p)) && flag_init_global_addresses(os_init_sg(p), OSFlagTbl, &OSFlagFreeList) && flag_init_layout(os_init_sg(p)) && sizeof(struct os_flag_grp[5]) == 80 &&
        flag_init_pre(os_init_sg(p)) * GlobalStrings(os_init_literals(p)) * os_init_raw_call_frame(p, S(S(S(S(S(O))))), X)
    */
    OS_FlagInit()/*@ where sg=os_init_sg(p), LitMap=os_init_literals(p), frame=os_init_raw_call_frame(p, S(S(S(S(S(O))))), X) */;
    /*@ flag_init_post(os_init_sg(p), os_init_literals(p)("?")) * GlobalStrings(os_init_literals(p)) * os_init_raw_call_frame(p, S(S(S(S(S(O))))), X)
        which implies
        os_init_raw_stage(p, S(S(S(S(S(S(O)))))), X)
    */                                               /* Initialize the event flag structures     */
#endif

#if (OS_MEM_EN > 0u) && (OS_MAX_MEM_PART > 0u)
    /*@ os_init_raw_stage(p, S(S(S(S(S(S(O)))))), X)
        which implies
        mem_init_profile(os_init_sg(p)) && mem_init_global_addresses(os_init_sg(p), OSMemTbl, &OSMemFreeList) && mem_init_layout(os_init_sg(p)) && sizeof(struct os_mem[5]) == 120 &&
        mem_init_pre(os_init_sg(p)) * GlobalStrings(os_init_literals(p)) * os_init_raw_call_frame(p, S(S(S(S(S(S(O)))))), X)
    */
    OS_MemInit()/*@ where sg=os_init_sg(p), LitMap=os_init_literals(p), frame=os_init_raw_call_frame(p, S(S(S(S(S(S(O)))))), X) */;
    /*@ mem_init_post(os_init_sg(p), os_init_literals(p)("?")) * GlobalStrings(os_init_literals(p)) * os_init_raw_call_frame(p, S(S(S(S(S(S(O)))))), X)
        which implies
        os_init_raw_stage(p, S(S(S(S(S(S(S(O))))))), X)
    */                                                /* Initialize the memory manager            */
#endif

#if (OS_Q_EN > 0u) && (OS_MAX_QS > 0u)
    /*@ os_init_raw_stage(p, S(S(S(S(S(S(S(O))))))), X)
        which implies
        valid_stable_glob_vars(os_init_sg(p)) && queue_first_round_profile(os_init_sg(p)) && os_q_table_addr(os_init_sg(p), OSQTbl) && os_q_free_list_addr(os_init_sg(p), &OSQFreeList) && queue_table_layout_prop(os_init_sg(p), OSQTbl) && q_init_table_endpoint_in_range(os_init_sg(p)) &&
        queue_init_pre(os_init_sg(p)) * GlobalStrings(os_init_literals(p)) * os_init_raw_call_frame(p, S(S(S(S(S(S(S(O))))))), X)
    */
    OS_QInit()/*@ where sg=os_init_sg(p) */;
    /*@ OS_QInit_spec(os_init_sg(p)) * GlobalStrings(os_init_literals(p)) * os_init_raw_call_frame(p, S(S(S(S(S(S(S(O))))))), X)
        which implies
        os_init_raw_stage(p, S(S(S(S(S(S(S(S(O)))))))), X)
    */                                                  /* Initialize the message queue structures  */
#endif

#if OS_TASK_CREATE_EXT_EN > 0u
#if defined(OS_TLS_TBL_SIZE) && (OS_TLS_TBL_SIZE > 0u)
    OS_TLS_Init(&err);                                           /* Initialize TLS, before creating tasks    */
    if (err != OS_ERR_NONE) {
        return;
    }
#endif
#endif

    /*@ os_init_raw_stage(p, S(S(S(S(S(S(S(S(O)))))))), X)
        which implies
        os_init_before_idle(p, X)
    */
    /*@ os_init_before_idle(p, X)
        which implies
        task_create_stack_global_addresses(os_init_sg(p), &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
        task_tcb_init_global_addresses(os_init_sg(p), &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
        os_sched_global_addresses(os_init_sg(p), &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        coq_prop(task_name_set_addresses(os_init_sg(p), OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
        coq_prop(task_name_set_layout(os_init_sg(p))) && kernel_sched_ready_clients(os_init_critical(p)) && kernel_tcb_stack_field_layout(os_init_sg(p)) &&
        task_create_runtime_call_input(init_task_idle_create_args(&OS_TaskIdle, OSTaskIdleStk), os_init_call(p), os_init_registered_state(p)) && init_task_idle_stopped(os_init_registered_state(p)) &&
        init_task_idle_continuation_safe(os_init_environment(p), os_init_critical(p), os_init_sg(p), &OS_TaskIdle, OSTaskIdleStk, &OS_TaskReturn, os_init_idle_lower(p), os_init_idle_frame(p), os_init_idle_upper(p), os_init_call(p), os_init_mask(p), os_init_literals(p), os_init_registered_state(p), os_init_idle_continuation(p, X)) &&
        init_task_idle_entry(os_init_environment(p), os_init_critical(p), tmr_init_empty_local, os_init_sg(p), &OS_TaskIdle, OSTaskIdleStk, &OS_TaskReturn, os_init_idle_lower(p), os_init_idle_frame(p), os_init_idle_upper(p), os_init_call(p), os_init_mask(p), os_init_literals(p), os_init_literal_keys, os_init_registered_state(p)) * os_init_idle_call_frame(p)
    */
    OS_InitTaskIdle()/*@ where environment=os_init_environment(p), critical=os_init_critical(p), saved_local=tmr_init_empty_local, sg=os_init_sg(p), entry=&OS_TaskIdle, base=OSTaskIdleStk, task_return=&OS_TaskReturn, mask=os_init_mask(p), lower=os_init_idle_lower(p), old_frame=os_init_idle_frame(p), upper=os_init_idle_upper(p), call=os_init_call(p), initial=os_init_registered_state(p), LitMap=os_init_literals(p), literals=os_init_literal_keys, X=os_init_idle_continuation(p, X) */;
    /*@ init_task_idle_continuation_post(os_init_environment(p), os_init_critical(p), tmr_init_empty_local, os_init_sg(p), &OS_TaskIdle, OSTaskIdleStk, &OS_TaskReturn, os_init_idle_lower(p), os_init_idle_frame(p), os_init_idle_upper(p), os_init_call(p), os_init_mask(p), os_init_literals(p), os_init_literal_keys, os_init_registered_state(p), os_init_idle_continuation(p, X)) * os_init_idle_call_frame(p)
        which implies
        exists (idle : OsInitTaskResult), os_init_before_stat(p, idle, X)
    */
    /*@ Given idle */                                           /* Create the Idle Task                     */
#if OS_TASK_STAT_EN > 0u
    /*@ os_init_before_stat(p, idle, X)
        which implies
        task_create_stack_global_addresses(os_init_sg(p), &OSIntNesting, OSTCBPrioTbl, &OSRunning) &&
        task_tcb_init_global_addresses(os_init_sg(p), &OSTCBFreeList, &OSTCBList, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSTaskCtr) &&
        os_sched_global_addresses(os_init_sg(p), &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
        coq_prop(task_name_set_addresses(os_init_sg(p), OSTCBPrioTbl, &OSTCBCur, &OSIntNesting)) &&
        coq_prop(task_name_set_layout(os_init_sg(p))) && kernel_sched_ready_clients(os_init_critical(p)) && kernel_tcb_stack_field_layout(os_init_sg(p)) &&
        task_create_runtime_call_input(init_task_stat_create_args(&OS_TaskStat, OSTaskStatStk), os_init_named_call(idle), os_init_named_state(idle)) && init_task_stat_stopped(os_init_named_state(idle)) &&
        init_task_stat_continuation_safe(os_init_environment(p), os_init_critical(p), os_init_sg(p), &OS_TaskStat, OSTaskStatStk, &OS_TaskReturn, os_init_stat_lower(p), os_init_stat_frame(p), os_init_stat_upper(p), os_init_named_call(idle), os_init_mask(p), os_init_literals(p), os_init_named_state(idle), os_init_stat_continuation(p, X)) &&
        init_task_stat_entry(os_init_environment(p), os_init_critical(p), tmr_init_empty_local, os_init_sg(p), &OS_TaskStat, OSTaskStatStk, &OS_TaskReturn, os_init_stat_lower(p), os_init_stat_frame(p), os_init_stat_upper(p), os_init_named_call(idle), os_init_mask(p), os_init_literals(p), os_init_literal_keys, os_init_named_state(idle)) * os_init_stat_call_frame(p, idle, X)
    */
    OS_InitTaskStat()/*@ where environment=os_init_environment(p), critical=os_init_critical(p), saved_local=tmr_init_empty_local, sg=os_init_sg(p), entry=&OS_TaskStat, base=OSTaskStatStk, task_return=&OS_TaskReturn, mask=os_init_mask(p), lower=os_init_stat_lower(p), old_frame=os_init_stat_frame(p), upper=os_init_stat_upper(p), call=os_init_named_call(idle), initial=os_init_named_state(idle), LitMap=os_init_literals(p), literals=os_init_literal_keys, X=os_init_stat_continuation(p, X) */;
    /*@ init_task_stat_continuation_post(os_init_environment(p), os_init_critical(p), tmr_init_empty_local, os_init_sg(p), &OS_TaskStat, OSTaskStatStk, &OS_TaskReturn, os_init_stat_lower(p), os_init_stat_frame(p), os_init_stat_upper(p), os_init_named_call(idle), os_init_mask(p), os_init_literals(p), os_init_literal_keys, os_init_named_state(idle), os_init_stat_continuation(p, X)) * os_init_stat_call_frame(p, idle, X)
        which implies
        exists (stat : OsInitTaskResult), os_init_before_timer(p, idle, stat, X)
    */
    /*@ Given stat */                                           /* Create the Statistic Task                */
#endif

#if OS_TMR_EN > 0u
    /*@ os_init_before_timer(p, idle, stat, X)
        which implies
        tmr_init_pre(os_init_timer(p), os_init_named_call(stat), os_init_named_state(stat), os_init_timer_continuation(X)) * os_init_timer_call_frame(p, idle, stat, X)
    */
    OSTmr_Init()/*@ where p=os_init_timer(p), call=os_init_named_call(stat), initial=os_init_named_state(stat), LitMap=os_init_literals(p), X=os_init_timer_continuation(X) */;
    /*@ tmr_init_post(os_init_timer(p), os_init_named_call(stat), os_init_timer_continuation(X)) * os_init_timer_call_frame(p, idle, stat, X)
        which implies
        exists (timer : OsInitTimerResult), os_init_after_timer_stage(p, idle, stat, timer, X)
    */
    /*@ Given timer */                                                /* Initialize the Timer Manager             */
#endif

    OSInitHookEnd()/*@ where P=os_init_after_timer_stage(p, idle, stat, timer, X) */;
    /*@ os_init_after_timer_stage(p, idle, stat, timer, X)
        which implies
        os_init_after_end_stage(p, idle, stat, timer, X)
    */                                             /* Call port specific init. code            */

#if OS_DEBUG_EN > 0u
    OSDebugInit()/*@ where frame=os_init_after_end_stage(p, idle, stat, timer, X) */;
    /*@ os_init_after_end_stage(p, idle, stat, timer, X)
        which implies
        os_init_return_stage(p, idle, stat, timer, X)
    */
#endif
}
