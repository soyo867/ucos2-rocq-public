/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OS_TaskStat (void *p_arg)
/*@ With (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
 saved_local (sg : StableGlobVars) (original : TaskSuspendCaller) (initial_mask : Z)
 (before : UCOS2_Verify_State) (frame : Assertion) (argument : Z)
 (X : TaskStatPoint -> UCOS2_Verify_State -> Prop)
 Require p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatReady, original, initial_mask, before, X)
 Ensure 0 == 1
*/
{
    INT32U idle_pct;
    INT32U idle_max;
    INT32U idle_run;
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif



    p_arg = p_arg;                               /* Prevent compiler warning for not using 'p_arg'     */
    /*@ p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatReady, original, initial_mask, before, X)
 which implies p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatReady, original, initial_mask), before, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(before)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(before)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(before)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(before)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(before)) *
 task_stat_closed_statistics_frame(environment, saved_local, sg, original, initial_mask, before) * frame
    */
    /*@ Inv exists (rc : TaskSuspendCaller) (rm : Z) (rs : UCOS2_Verify_State),
 p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatReady, rc, rm), rs, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(rs)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(rs)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(rs)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(rs)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(rs)) *
 task_stat_closed_statistics_frame(environment, saved_local, sg, rc, rm, rs) * frame * undef_data_at(&idle_pct, INT32U) * undef_data_at(&idle_max, INT32U) * undef_data_at(&idle_run, INT32U) * undef_data_at(&cpu_sr, OS_CPU_SR)
    */
    while (OSStatRdy == OS_FALSE) {
    /*@ Given rc rm rs
    */
    /*@ task_stat_ready(rs) == 0 && p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatReady, rc, rm), rs, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(rs)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(rs)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(rs)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(rs)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(rs)) *
 task_stat_closed_statistics_frame(environment, saved_local, sg, rc, rm, rs) * frame
 which implies p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatReadyDelay, rc, rm, rs, X)
    */
    /*@ task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatReadyDelay, rc, rm, rs, X)
 which implies time_dly_safe(environment, critical, sg, rc, rm, 20, rs, task_stat_delay_continuation(environment, critical, saved_local, sg, frame, TaskStatReadyDelay, rc, rm, 20, TaskStatReady, rs, X)) &&
 time_dly_call_pre(environment, critical, saved_local, sg, rc, rm, 20, rs, frame)
    */
        OSTimeDly(2u * OS_TICKS_PER_SEC / 10u) /*@ where X = task_stat_delay_continuation(environment, critical, saved_local, sg, frame, TaskStatReadyDelay, rc, rm, 20, TaskStatReady, rs, X), environment = environment, critical = critical, saved_local = saved_local, sg = sg, caller = rc, mask = rm, request = 20, before = rs, frame = frame */;  /* Wait until statistic task is ready                 */
    /*@ time_dly_call_post(environment, critical, saved_local, sg, rc, rm, 20, rs, frame, task_stat_delay_continuation(environment, critical, saved_local, sg, frame, TaskStatReadyDelay, rc, rm, 20, TaskStatReady, rs, X))
 which implies exists (ready_returned : TaskSuspendCaller) (ready_current : UCOS2_Verify_State), task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatReady, ready_returned, rm, ready_current, X)
    */
    /*@ Given ready_returned ready_current
    */
    /*@ p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatReady, ready_returned, rm, ready_current, X)
 which implies p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatReady, ready_returned, rm), ready_current, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(ready_current)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(ready_current)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(ready_current)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(ready_current)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(ready_current)) *
 task_stat_closed_statistics_frame(environment, saved_local, sg, ready_returned, rm, ready_current) * frame
    */
    }
    /*@ Given rc rm rs
    */
    /*@ task_stat_ready(rs) != 0 && p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatReady, rc, rm), rs, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(rs)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(rs)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(rs)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(rs)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(rs)) *
 task_stat_closed_statistics_frame(environment, saved_local, sg, rc, rm, rs) * frame
 which implies p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatScaleLoad, rc, rm), rs, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(rs)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(rs)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(rs)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(rs)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(rs)) *
 task_stat_closed_statistics_frame(environment, saved_local, sg, rc, rm, rs) * frame
    */
    OSIdleCtrMax /= 100uL;
    /*@ Assert exists (scaled_caller : TaskSuspendCaller) (scaled_mask : Z) (scaled : UCOS2_Verify_State), p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatZeroTest, scaled_caller, scaled_mask), scaled, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(scaled)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(scaled)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(scaled)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(scaled)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(scaled)) *
 task_stat_closed_statistics_frame(environment, saved_local, sg, scaled_caller, scaled_mask, scaled) * frame * undef_data_at(&idle_pct, INT32U) * undef_data_at(&idle_max, INT32U) * undef_data_at(&idle_run, INT32U) * undef_data_at(&cpu_sr, OS_CPU_SR)
    */
    /*@ Inv exists (zc : TaskSuspendCaller) (zm : Z) (zs : UCOS2_Verify_State),
 p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatZeroTest, zc, zm), zs, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(zs)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(zs)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(zs)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(zs)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(zs)) *
 task_stat_closed_statistics_frame(environment, saved_local, sg, zc, zm, zs) * frame * undef_data_at(&idle_pct, INT32U) * undef_data_at(&idle_max, INT32U) * undef_data_at(&idle_run, INT32U) * undef_data_at(&cpu_sr, OS_CPU_SR)
    */
    while (OSIdleCtrMax == 0uL) {
    /*@ Given zc zm zs
    */
    /*@ task_stat_maximum(zs) == 0 && p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatZeroTest, zc, zm), zs, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(zs)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(zs)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(zs)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(zs)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(zs)) *
 task_stat_closed_statistics_frame(environment, saved_local, sg, zc, zm, zs) * frame
 which implies p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatZeroUsage, zc, zm), zs, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(zs)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(zs)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(zs)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(zs)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(zs)) *
 task_stat_closed_statistics_frame(environment, saved_local, sg, zc, zm, zs) * frame
    */
        OSCPUUsage = 0u;
    /*@ Assert exists (zero_written : UCOS2_Verify_State), p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatSelfSuspend, zc, zm, zero_written, X) * undef_data_at(&idle_pct, INT32U) * undef_data_at(&idle_max, INT32U) * undef_data_at(&idle_run, INT32U) * undef_data_at(&cpu_sr, OS_CPU_SR)
    */
    /*@ Given zero_written
    */
#if OS_TASK_SUSPEND_EN > 0u
    /*@ task_stat_configuration(sg) && task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatSelfSuspend, zc, zm, zero_written, X)
 which implies task_stat_configuration(sg) &&
 task_suspend_safe(environment, critical, sg, zc, zm, 255, zero_written, task_stat_suspend_observation(environment, critical, sg, zc, zm, 255, zero_written, task_stat_suspend_continuation(environment, critical, saved_local, sg, frame, zc, zm, zero_written, X))) &&
 task_suspend_call_pre(environment, critical, saved_local, sg, zc, zm, zero_written, 255, frame)
    */
        (void)OSTaskSuspend(OS_PRIO_SELF) /*@ where X = task_stat_suspend_observation(environment, critical, sg, zc, zm, 255, zero_written, task_stat_suspend_continuation(environment, critical, saved_local, sg, frame, zc, zm, zero_written, X)), environment = environment, critical = critical, saved_local = saved_local, sg = sg, caller = zc, mask = zm, request = 255, before = zero_written, frame = frame */;
    /*@ Assert exists (suspend_returned : TaskSuspendCaller) (suspend_current : UCOS2_Verify_State), p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatZeroTest, suspend_returned, zm), suspend_current, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(suspend_current)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(suspend_current)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(suspend_current)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(suspend_current)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(suspend_current)) *
 task_stat_closed_statistics_frame(environment, saved_local, sg, suspend_returned, zm, suspend_current) * frame * undef_data_at(&idle_pct, INT32U) * undef_data_at(&idle_max, INT32U) * undef_data_at(&idle_run, INT32U) * undef_data_at(&cpu_sr, OS_CPU_SR)
    */
#else
        for (; 1;) {
            OSTimeDly(OS_TICKS_PER_SEC);
        }
#endif
    }
    /*@ Given zc zm zs
    */
    /*@ task_stat_maximum(zs) != 0 && p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatZeroTest, zc, zm), zs, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(zs)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(zs)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(zs)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(zs)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(zs)) *
 task_stat_closed_statistics_frame(environment, saved_local, sg, zc, zm, zs) * frame
 which implies p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatAcquire(TaskStatInitialize), zc, zm, zs, X)
    */
    /*@ task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatAcquire(TaskStatInitialize), zc, zm, zs, X)
 which implies task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatAcquire(TaskStatInitialize), zc, zm), zs, X) &&
 task_suspend_closed(environment, critical, saved_local, sg, zc, zm, zs) * frame
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (init_caller : TaskSuspendCaller) (init_acquired : UCOS2_Verify_State),
 p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatProtected(TaskStatInitialize, cpu_sr, init_acquired), init_caller, zm), init_acquired, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(init_acquired)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(init_acquired)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(init_acquired)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(init_acquired)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(init_acquired)) * task_stat_masked_statistics_frame(environment, critical, saved_local, sg, init_caller, cpu_sr, init_acquired, init_acquired) * frame * undef_data_at(&idle_pct, INT32U) * undef_data_at(&idle_max, INT32U) * undef_data_at(&idle_run, INT32U)
    */
    /*@ Given init_caller init_acquired
    */
    OSIdleCtr = OSIdleCtrMax * 100uL;            /* Set initial CPU usage as 0%                        */
    /*@ Assert exists (init_released : UCOS2_Verify_State), p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
 task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatRelease(TaskStatInitialize, cpu_sr, init_acquired, task_stat_sample(0, 0)), init_caller, zm), init_released, X) && 
 task_suspend_masked(environment, critical, saved_local, sg, init_caller, cpu_sr, init_acquired, init_released) * frame * undef_data_at(&idle_pct, INT32U) * undef_data_at(&idle_max, INT32U) * undef_data_at(&idle_run, INT32U)
    */
    /*@ Given init_released
    */
    OS_EXIT_CRITICAL();
    /*@ Assert exists (initial_returned : TaskSuspendCaller) (initial_current : UCOS2_Verify_State) (initial_after_mask : Z), p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatOneTick, initial_returned, initial_after_mask, initial_current, X) * undef_data_at(&idle_pct, INT32U) * undef_data_at(&idle_max, INT32U) * undef_data_at(&idle_run, INT32U) * undef_data_at(&cpu_sr, OS_CPU_SR)
    */
    /*@ Inv exists (lc : TaskSuspendCaller) (lm : Z) (ls : UCOS2_Verify_State), p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
 task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatOneTick, lc, lm, ls, X) * undef_data_at(&idle_pct, INT32U) * undef_data_at(&idle_max, INT32U) * undef_data_at(&idle_run, INT32U) * undef_data_at(&cpu_sr, OS_CPU_SR)
    */
    for (; 1;) {
    /*@ Given lc lm ls
    */
    /*@ task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatOneTick, lc, lm, ls, X)
 which implies time_dly_safe(environment, critical, sg, lc, lm, 1, ls, task_stat_delay_continuation(environment, critical, saved_local, sg, frame, TaskStatOneTick, lc, lm, 1, TaskStatAcquire(TaskStatReset), ls, X)) &&
 time_dly_call_pre(environment, critical, saved_local, sg, lc, lm, 1, ls, frame)
    */
        OSTimeDly(1) /*@ where X = task_stat_delay_continuation(environment, critical, saved_local, sg, frame, TaskStatOneTick, lc, lm, 1, TaskStatAcquire(TaskStatReset), ls, X), environment = environment, critical = critical, saved_local = saved_local, sg = sg, caller = lc, mask = lm, request = 1, before = ls, frame = frame */;                            /* Synchronize with clock tick                        */
    /*@ time_dly_call_post(environment, critical, saved_local, sg, lc, lm, 1, ls, frame, task_stat_delay_continuation(environment, critical, saved_local, sg, frame, TaskStatOneTick, lc, lm, 1, TaskStatAcquire(TaskStatReset), ls, X))
 which implies exists (one_returned : TaskSuspendCaller) (one_current : UCOS2_Verify_State), task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatAcquire(TaskStatReset), one_returned, lm, one_current, X)
    */
    /*@ Given one_returned one_current
    */

    /*@ task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatAcquire(TaskStatReset), one_returned, lm, one_current, X)
 which implies task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatAcquire(TaskStatReset), one_returned, lm), one_current, X) &&
 task_suspend_closed(environment, critical, saved_local, sg, one_returned, lm, one_current) * frame
    */
        OS_ENTER_CRITICAL();
    /*@ Assert exists (reset_caller : TaskSuspendCaller) (reset_acquired : UCOS2_Verify_State),
 p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatProtected(TaskStatReset, cpu_sr, reset_acquired), reset_caller, lm), reset_acquired, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(reset_acquired)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(reset_acquired)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(reset_acquired)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(reset_acquired)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(reset_acquired)) * task_stat_masked_statistics_frame(environment, critical, saved_local, sg, reset_caller, cpu_sr, reset_acquired, reset_acquired) * frame * undef_data_at(&idle_pct, INT32U) * undef_data_at(&idle_max, INT32U) * undef_data_at(&idle_run, INT32U)
    */
    /*@ Given reset_caller reset_acquired
    */
        OSIdleCtr = 0uL;                        /* Reset the idle counter for the next second         */
    /*@ Assert exists (reset_released : UCOS2_Verify_State), p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
 task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatRelease(TaskStatReset, cpu_sr, reset_acquired, task_stat_sample(0, 0)), reset_caller, lm), reset_released, X) && 
 task_suspend_masked(environment, critical, saved_local, sg, reset_caller, cpu_sr, reset_acquired, reset_released) * frame * undef_data_at(&idle_pct, INT32U) * undef_data_at(&idle_max, INT32U) * undef_data_at(&idle_run, INT32U)
    */
    /*@ Given reset_released
    */
        OS_EXIT_CRITICAL();
    /*@ Assert exists (window_caller : TaskSuspendCaller) (window_state : UCOS2_Verify_State) (window_mask : Z), p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatSampleWindow, window_caller, window_mask, window_state, X) * undef_data_at(&idle_pct, INT32U) * undef_data_at(&idle_max, INT32U) * undef_data_at(&idle_run, INT32U) * undef_data_at(&cpu_sr, OS_CPU_SR)
    */
    /*@ Given window_caller window_state window_mask
    */

    /*@ task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatSampleWindow, window_caller, window_mask, window_state, X)
 which implies time_dly_safe(environment, critical, sg, window_caller, window_mask, 10, window_state, task_stat_delay_continuation(environment, critical, saved_local, sg, frame, TaskStatSampleWindow, window_caller, window_mask, 10, TaskStatAcquire(TaskStatCapture), window_state, X)) &&
 time_dly_call_pre(environment, critical, saved_local, sg, window_caller, window_mask, 10, window_state, frame)
    */
        OSTimeDly(OS_TICKS_PER_SEC / 10u) /*@ where X = task_stat_delay_continuation(environment, critical, saved_local, sg, frame, TaskStatSampleWindow, window_caller, window_mask, 10, TaskStatAcquire(TaskStatCapture), window_state, X), environment = environment, critical = critical, saved_local = saved_local, sg = sg, caller = window_caller, mask = window_mask, request = 10, before = window_state, frame = frame */;       /* Accumulate OSIdleCtr for the next 1/10 second      */
    /*@ time_dly_call_post(environment, critical, saved_local, sg, window_caller, window_mask, 10, window_state, frame, task_stat_delay_continuation(environment, critical, saved_local, sg, frame, TaskStatSampleWindow, window_caller, window_mask, 10, TaskStatAcquire(TaskStatCapture), window_state, X))
 which implies exists (window_returned : TaskSuspendCaller) (window_current : UCOS2_Verify_State), task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatAcquire(TaskStatCapture), window_returned, window_mask, window_current, X)
    */
    /*@ Given window_returned window_current
    */

    /*@ task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatAcquire(TaskStatCapture), window_returned, window_mask, window_current, X)
 which implies task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatAcquire(TaskStatCapture), window_returned, window_mask), window_current, X) &&
 task_suspend_closed(environment, critical, saved_local, sg, window_returned, window_mask, window_current) * frame
    */
        OS_ENTER_CRITICAL();
    /*@ Assert exists (capture_caller : TaskSuspendCaller) (capture_acquired : UCOS2_Verify_State),
 p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) && task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatProtected(TaskStatCapture, cpu_sr, capture_acquired), capture_caller, window_mask), capture_acquired, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(capture_acquired)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(capture_acquired)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(capture_acquired)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(capture_acquired)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(capture_acquired)) * task_stat_masked_statistics_frame(environment, critical, saved_local, sg, capture_caller, cpu_sr, capture_acquired, capture_acquired) * frame * undef_data_at(&idle_pct, INT32U) * undef_data_at(&idle_max, INT32U) * undef_data_at(&idle_run, INT32U)
    */
    /*@ Given capture_caller capture_acquired
    */
        OSIdleCtrRun = OSIdleCtr;                /* Store number of cycles which elapsed while idle    */
        idle_run     = OSIdleCtrRun;
        idle_max     = OSIdleCtrMax;
    /*@ Assert exists (capture_released : UCOS2_Verify_State), p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
 task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatRelease(TaskStatCapture, cpu_sr, capture_acquired, task_stat_sample(task_stat_counter(capture_acquired), task_stat_maximum(capture_acquired))), capture_caller, window_mask), capture_released, X) && idle_run == task_stat_counter(capture_acquired) && idle_max == task_stat_maximum(capture_acquired) && valid_statistics_sample(task_stat_sample(task_stat_counter(capture_acquired), task_stat_maximum(capture_acquired))) && 
 task_suspend_masked(environment, critical, saved_local, sg, capture_caller, cpu_sr, capture_acquired, capture_released) * frame * undef_data_at(&idle_pct, INT32U)
    */
    /*@ Given capture_released
    */
        OS_EXIT_CRITICAL();
    /*@ Assert exists (sample_caller : TaskSuspendCaller) (sample_state : UCOS2_Verify_State) (sample_mask : Z), p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
 idle_run == task_stat_counter(capture_acquired) && idle_max == task_stat_maximum(capture_acquired) && valid_statistics_sample(task_stat_sample(task_stat_counter(capture_acquired), task_stat_maximum(capture_acquired))) &&
 task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatUsage(task_stat_sample(task_stat_counter(capture_acquired), task_stat_maximum(capture_acquired))), sample_caller, sample_mask), sample_state, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(sample_state)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(sample_state)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(sample_state)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(sample_state)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(sample_state)) *
 task_stat_closed_statistics_frame(environment, saved_local, sg, sample_caller, sample_mask, sample_state) * frame * undef_data_at(&idle_pct, INT32U) * undef_data_at(&cpu_sr, OS_CPU_SR)
    */
    /*@ Given sample_caller sample_state sample_mask
    */

        if (idle_max == 0uL) {                  /* Recalibration must not introduce a zero divisor    */
            OSCPUUsage = 0u;
        } else {
            idle_pct = idle_run / idle_max;
            if (idle_pct <= 100uL) {
                OSCPUUsage = (INT8U)(100uL - idle_pct);
            } else {
                OSCPUUsage   = 0u;
    /*@ Assert exists (usage_written : UCOS2_Verify_State), p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
 idle_run == task_stat_counter(capture_acquired) && idle_max == task_stat_maximum(capture_acquired) &&
 valid_statistics_sample(task_stat_sample(task_stat_counter(capture_acquired), task_stat_maximum(capture_acquired))) && idle_pct == idle_run / idle_max && idle_pct > 100 &&
 task_stat_context(environment, critical, saved_local, sg, frame, task_stat_at(TaskStatRecalibrate(task_stat_sample(task_stat_counter(capture_acquired), task_stat_maximum(capture_acquired))), sample_caller, sample_mask), usage_written, X) &&
 data_at(&OSIdleCtr, unsigned int, task_stat_counter(usage_written)) *
 data_at(&OSIdleCtrMax, unsigned int, task_stat_maximum(usage_written)) *
 data_at(&OSIdleCtrRun, unsigned int, task_stat_run(usage_written)) *
 data_at(&OSCPUUsage, unsigned char, task_stat_usage(usage_written)) *
 data_at(&OSStatRdy, unsigned char, task_stat_ready(usage_written)) *
 task_stat_closed_statistics_frame(environment, saved_local, sg, sample_caller, sample_mask, usage_written) * frame * undef_data_at(&cpu_sr, OS_CPU_SR)
    */
                OSIdleCtrMax = idle_run / 100uL; /* Update from the same sampled counter              */
            }
        }

    /*@ Assert exists (hook_caller : TaskSuspendCaller) (hook_mask : Z) (hook_state : UCOS2_Verify_State), p_arg == argument && task_stat_configuration(sg) &&
 task_stat_statistics_addresses(sg, &OSIdleCtr, &OSIdleCtrMax, &OSIdleCtrRun, &OSCPUUsage, &OSStatRdy) &&
 task_suspend_addresses(sg, &OSTCBCur, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy,
   &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
 task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
 task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatHook, hook_caller, hook_mask, hook_state, X) * undef_data_at(&idle_pct, INT32U) * undef_data_at(&idle_max, INT32U) * undef_data_at(&idle_run, INT32U) * undef_data_at(&cpu_sr, OS_CPU_SR)
    */
    /*@ Given hook_caller hook_mask hook_state
    */
        OSTaskStatHook() /*@ where frame = task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatHook, hook_caller, hook_mask, hook_state, X) */;                        /* Invoke user definable hook                         */
    /*@ task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatHook, hook_caller, hook_mask, hook_state, X)
 which implies task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatStack, hook_caller, hook_mask, hook_state, X)
    */
#if (OS_TASK_STAT_STK_CHK_EN > 0u) && (OS_TASK_CREATE_EXT_EN > 0u)
    /*@ task_stat_configuration(sg) && task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatStack, hook_caller, hook_mask, hook_state, X)
 which implies task_stat_configuration(sg) && task_stat_stk_chk_configuration(sg) && UCOS2_state_inv(sg, hook_state) &&
 task_stat_stk_chk_continuation_protocol(environment, critical, saved_local, sg, hook_caller, hook_mask, frame, hook_state) &&
 task_stat_stk_chk_continuation_safe(environment, critical, saved_local, sg, hook_caller, hook_mask, frame, hook_state, task_stat_stack_continuation(environment, critical, saved_local, sg, frame, hook_caller, hook_mask, hook_state, X)) &&
 task_suspend_closed(environment, critical, saved_local, sg, hook_caller, hook_mask, hook_state) * frame
    */
        OS_TaskStatStkChk() /*@ where environment = environment, critical = critical, saved_local = saved_local, sg = sg, original = hook_caller, mask = hook_mask, before = hook_state, caller_frame = frame, X = task_stat_stack_continuation(environment, critical, saved_local, sg, frame, hook_caller, hook_mask, hook_state, X) */;                     /* Check the stacks for each task                     */
    /*@ task_stat_stk_chk_continuation_post(environment, critical, saved_local, sg, hook_caller, hook_mask, frame, hook_state, task_stat_stack_continuation(environment, critical, saved_local, sg, frame, hook_caller, hook_mask, hook_state, X))
 which implies exists (stack_returned : TaskSuspendCaller) (stack_current : UCOS2_Verify_State),
 task_stat_closed_checkpoint(environment, critical, saved_local, sg, frame, TaskStatOneTick, stack_returned, hook_mask, stack_current, X)
    */
#endif
    }
}
