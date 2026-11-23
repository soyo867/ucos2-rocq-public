/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OS_TaskStatStkChk (void)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
    (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
    (mask : Z) (before : UCOS2_Verify_State) (caller : Assertion)
    Require task_stat_stk_chk_configuration(sg) &&
      task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
      task_stat_stk_chk_protocol(critical, sg, invocation, mask, caller, before) &&
      UCOS2_state_inv(sg, before) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      critical_region_outside(critical, sg, invocation, before) * caller
    Ensure exists after,
      task_stat_stk_chk_post(critical, sg, invocation, mask, caller, before, after) &&
      UCOS2_state_inv(sg, after) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      critical_region_outside(critical, sg, invocation, after) * caller
*/
{
    OS_TCB      *ptcb;
    OS_STK_DATA  stk_data;
    INT8U        err;
    INT8U        prio;


    /*@ undef_data_at(&(stk_data.OSFree), unsigned int) *
      undef_data_at(&(stk_data.OSUsed), unsigned int)
      which implies &stk_data != 0 && task_stk_chk_output_undef(&stk_data)
    */
    /*@ Inv exists current history,
      UCOS2_state_inv(sg, before) && task_stat_stk_chk_configuration(sg) &&
      task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
      task_stat_stk_chk_protocol(critical, sg, invocation, mask, caller, before) &&
      &stk_data != 0 && 0 <= prio && prio <= 64 &&
      task_stat_stk_chk_prefix(critical, sg, invocation, mask, caller, &stk_data,
        before, prio, current, history) && UCOS2_state_inv(sg, current) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      critical_region_outside(critical, sg, invocation, current) * caller *
      task_stk_chk_output_undef(&stk_data)
    */
    for (prio = 0u; prio <= OS_TASK_IDLE_PRIO; prio++) {
        /*@ Given current history */
        /*@ task_stat_stk_chk_configuration(sg) && &stk_data != 0 &&
          0 <= prio && prio < 64 &&
          task_stat_stk_chk_protocol(critical, sg, invocation, mask, caller, before) &&
          task_stat_stk_chk_prefix(critical, sg, invocation, mask, caller, &stk_data,
            before, prio, current, history) && task_stk_chk_output_undef(&stk_data)
          which implies task_stat_stk_chk_configuration(sg) &&
          task_stk_chk_configuration(sg) && &stk_data != 0 && 0 <= prio && prio < 64 &&
          task_stat_stk_chk_protocol(critical, sg, invocation, mask, caller, before) &&
          task_stat_stk_chk_prefix(critical, sg, invocation, mask, caller, &stk_data,
            before, prio, current, history) &&
          task_stk_chk_admission(critical, sg, invocation, current, caller, prio, &stk_data) &&
          task_stk_chk_safe(critical, sg, invocation, current, caller, prio, &stk_data,
            task_stat_stk_chk_observe_call(critical, sg, invocation, current, caller, prio, &stk_data)) &&
          task_stk_chk_output_pre(sg, prio, &stk_data)
        */
        err = OSTaskStkChk(prio, &stk_data)
        /*@ where platform=platform, critical=critical, sg=sg, invocation=invocation,
          origin=origin, mask=mask, before=current, caller=caller,
          X=task_stat_stk_chk_observe_call(critical, sg, invocation, current, caller, prio, &stk_data) */;
        /*@ Assert exists after data,
          UCOS2_state_inv(sg, before) && task_stat_stk_chk_configuration(sg) &&
          task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          task_stat_stk_chk_protocol(critical, sg, invocation, mask, caller, before) &&
          &stk_data != 0 && 0 <= prio && prio < 64 &&
          task_stat_stk_chk_prefix(critical, sg, invocation, mask, caller, &stk_data,
            before, prio, current, history) &&
          task_stat_stk_chk_call_result(critical, sg, invocation, mask, current,
            caller, prio, &stk_data, err, data, after) && UCOS2_state_inv(sg, after) &&
          interrupt_platform_running(platform, invocation, origin, mask) *
          critical_region_outside(critical, sg, invocation, after) * caller *
          task_stk_chk_output_post(&stk_data, data) * undef_data_at(&ptcb, OS_TCB *)
        */
        /*@ Given after data */
        if (err == OS_ERR_NONE) {
            /*@ UCOS2_state_inv(sg, after) &&
              task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
              0 <= prio && prio < 64 &&
              critical_region_outside(critical, sg, invocation, after)
              which implies UCOS2_state_inv(sg, after) &&
              task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
              0 <= prio && prio < 64 &&
              data_at(pointer_offset(&OSTCBPrioTbl, prio, void *), void *,
                task_stk_chk_table_pointer(sg, after, prio)) *
              task_stk_chk_table_frame(sg, after, prio)
            */
            ptcb = OSTCBPrioTbl[prio];
            /*@ UCOS2_state_inv(sg, after) &&
              task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
              0 <= prio && prio < 64 && ptcb == task_stk_chk_table_pointer(sg, after, prio) &&
              data_at(pointer_offset(&OSTCBPrioTbl, prio, void *), void *,
                task_stk_chk_table_pointer(sg, after, prio)) *
              task_stk_chk_table_frame(sg, after, prio)
              which implies UCOS2_state_inv(sg, after) &&
              task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
              0 <= prio && prio < 64 && ptcb == task_stk_chk_table_pointer(sg, after, prio) &&
              critical_region_outside(critical, sg, invocation, after)
            */
            if (ptcb != (OS_TCB *)0) {                               /* Make sure task 'ptcb' is ...   */
                if (ptcb != ((OS_TCB *)1)) {                       /* ... still valid.               */
#if OS_TASK_PROFILE_EN > 0u
                    #if OS_STK_GROWTH == 1u
                    ptcb->OSTCBStkBase = ptcb->OSTCBStkBottom + ptcb->OSTCBStkSize;
                    #else
                    ptcb->OSTCBStkBase = ptcb->OSTCBStkBottom - ptcb->OSTCBStkSize;
                    #endif
                    ptcb->OSTCBStkUsed = stk_data.OSUsed;            /* Store number of entries used   */
#endif
                }
            }
        }
        /*@ Assert exists next_history,
          UCOS2_state_inv(sg, before) && task_stat_stk_chk_configuration(sg) &&
          task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          task_stat_stk_chk_protocol(critical, sg, invocation, mask, caller, before) &&
          &stk_data != 0 && 0 <= prio && prio < 64 &&
          task_stat_stk_chk_prefix(critical, sg, invocation, mask, caller, &stk_data,
            before, prio + 1, after, next_history) && UCOS2_state_inv(sg, after) &&
          interrupt_platform_running(platform, invocation, origin, mask) *
          critical_region_outside(critical, sg, invocation, after) * caller *
          task_stk_chk_output_undef(&stk_data) * undef_data_at(&ptcb, OS_TCB *) *
          undef_data_at(&err, unsigned char)
        */
    }
    /*@ Given current history */
    /*@ task_stk_chk_output_undef(&stk_data)
      which implies undef_data_at(&(stk_data.OSFree), unsigned int) *
        undef_data_at(&(stk_data.OSUsed), unsigned int)
    */
}
