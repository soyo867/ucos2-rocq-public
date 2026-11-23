/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OS_TaskStatStkChk (void)
/*@ With (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
    saved_local (sg : StableGlobVars) (original : TaskSuspendCaller)
    (mask : Z) (before : UCOS2_Verify_State) (caller_frame : Assertion)
    (X : unit -> UCOS2_Verify_State -> Prop)
    Require task_stat_stk_chk_configuration(sg) &&
      task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
      UCOS2_state_inv(sg, before) &&
      task_stat_stk_chk_continuation_protocol(environment, critical, saved_local, sg,
        original, mask, caller_frame, before) &&
      task_stat_stk_chk_continuation_safe(environment, critical, saved_local, sg,
        original, mask, caller_frame, before, X) &&
      task_suspend_closed(environment, critical, saved_local, sg, original, mask, before) *
      caller_frame
    Ensure task_stat_stk_chk_continuation_post(environment, critical, saved_local, sg,
      original, mask, caller_frame, before, X)
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
    /*@ Inv exists current_caller current history,
      UCOS2_state_inv(sg, before) && task_stat_stk_chk_configuration(sg) &&
      task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
      task_stat_stk_chk_continuation_protocol(environment, critical, saved_local, sg,
        original, mask, caller_frame, before) &&
      task_stat_stk_chk_continuation_safe(environment, critical, saved_local, sg,
        original, mask, caller_frame, before, X) &&
      &stk_data != 0 && 0 <= prio && prio <= 64 &&
      task_stat_stk_chk_continuation_prefix(environment, critical, saved_local, sg, mask,
        caller_frame, &stk_data, original, before, prio, history, current_caller, current) &&
      UCOS2_state_inv(sg, current) &&
      task_suspend_closed(environment, critical, saved_local, sg, current_caller, mask, current) *
      caller_frame * task_stk_chk_output_undef(&stk_data)
    */
    for (prio = 0u; prio <= OS_TASK_IDLE_PRIO; prio++) {
        /*@ Given current_caller current history */
        /*@ task_stat_stk_chk_configuration(sg) && &stk_data != 0 &&
          0 <= prio && prio < 64 &&
          task_stat_stk_chk_continuation_protocol(environment, critical, saved_local, sg,
            original, mask, caller_frame, before) &&
          task_stat_stk_chk_continuation_prefix(environment, critical, saved_local, sg, mask,
            caller_frame, &stk_data, original, before, prio, history, current_caller, current) &&
          task_stk_chk_output_undef(&stk_data)
          which implies task_stat_stk_chk_configuration(sg) &&
          task_stk_chk_configuration(sg) && &stk_data != 0 && 0 <= prio && prio < 64 &&
          task_stat_stk_chk_continuation_protocol(environment, critical, saved_local, sg,
            original, mask, caller_frame, before) &&
          task_stat_stk_chk_continuation_prefix(environment, critical, saved_local, sg, mask,
            caller_frame, &stk_data, original, before, prio, history, current_caller, current) &&
          task_stk_chk_continuation_admission(environment, critical, saved_local, sg,
            current_caller, mask, caller_frame, prio, &stk_data, current) &&
          task_stk_chk_continuation_safe(environment, critical, saved_local, sg,
            current_caller, mask, caller_frame, prio, &stk_data, current,
            task_stat_stk_chk_continuation_observe_call(environment, critical, saved_local, sg,
              current_caller, mask, caller_frame, prio, &stk_data, current)) &&
          task_stk_chk_output_pre(sg, prio, &stk_data)
        */
        err = OSTaskStkChk(prio, &stk_data)
        /*@ where environment=environment, critical=critical, saved_local=saved_local,
          sg=sg, original=current_caller, mask=mask, before=current, caller_frame=caller_frame,
          X=task_stat_stk_chk_continuation_observe_call(environment, critical, saved_local, sg,
            current_caller, mask, caller_frame, prio, &stk_data, current) */;
        /*@ Assert exists returned data after,
          UCOS2_state_inv(sg, before) && task_stat_stk_chk_configuration(sg) &&
          task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          task_stat_stk_chk_continuation_protocol(environment, critical, saved_local, sg,
            original, mask, caller_frame, before) &&
          task_stat_stk_chk_continuation_safe(environment, critical, saved_local, sg,
            original, mask, caller_frame, before, X) &&
          &stk_data != 0 && 0 <= prio && prio < 64 &&
          task_stat_stk_chk_continuation_prefix(environment, critical, saved_local, sg, mask,
            caller_frame, &stk_data, original, before, prio, history, current_caller, current) &&
          task_stat_stk_chk_continuation_call_result(environment, critical, saved_local, sg,
            current_caller, mask, caller_frame, prio, &stk_data, current, err, data, returned, after) &&
          UCOS2_state_inv(sg, after) &&
          task_suspend_closed(environment, critical, saved_local, sg, returned, mask, after) *
          caller_frame * task_stk_chk_output_post(&stk_data, data) * undef_data_at(&ptcb, OS_TCB *)
        */
        /*@ Given returned data after */
        if (err == OS_ERR_NONE) {
            /*@ UCOS2_state_inv(sg, after) &&
              task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
              0 <= prio && prio < 64 &&
              task_suspend_closed(environment, critical, saved_local, sg, returned, mask, after)
              which implies UCOS2_state_inv(sg, after) &&
              task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
              0 <= prio && prio < 64 &&
              data_at(pointer_offset(&OSTCBPrioTbl, prio, void *), void *,
                task_stk_chk_table_pointer(sg, after, prio)) *
              task_stat_stk_chk_continuation_table_frame(environment, saved_local, sg,
                returned, mask, after, prio)
            */
            ptcb = OSTCBPrioTbl[prio];
            /*@ UCOS2_state_inv(sg, after) &&
              task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
              0 <= prio && prio < 64 && ptcb == task_stk_chk_table_pointer(sg, after, prio) &&
              data_at(pointer_offset(&OSTCBPrioTbl, prio, void *), void *,
                task_stk_chk_table_pointer(sg, after, prio)) *
              task_stat_stk_chk_continuation_table_frame(environment, saved_local, sg,
                returned, mask, after, prio)
              which implies UCOS2_state_inv(sg, after) &&
              task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
              0 <= prio && prio < 64 && ptcb == task_stk_chk_table_pointer(sg, after, prio) &&
              task_suspend_closed(environment, critical, saved_local, sg, returned, mask, after)
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
        /*@ Assert exists observed,
          UCOS2_state_inv(sg, before) && task_stat_stk_chk_configuration(sg) &&
          task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          task_stat_stk_chk_continuation_protocol(environment, critical, saved_local, sg,
            original, mask, caller_frame, before) &&
          task_stat_stk_chk_continuation_safe(environment, critical, saved_local, sg,
            original, mask, caller_frame, before, X) &&
          &stk_data != 0 && 0 <= prio && prio < 64 &&
          task_stat_stk_chk_continuation_prefix(environment, critical, saved_local, sg, mask,
            caller_frame, &stk_data, original, before, prio, history, current_caller, current) &&
          task_stat_stk_chk_continuation_call_result(environment, critical, saved_local, sg,
            current_caller, mask, caller_frame, prio, &stk_data, current, err, data, returned, after) &&
          task_stat_stk_chk_continuation_table_result(sg, prio, err, after, observed) &&
          UCOS2_state_inv(sg, after) &&
          task_suspend_closed(environment, critical, saved_local, sg, returned, mask, after) *
          caller_frame * task_stk_chk_output_post(&stk_data, data) * undef_data_at(&ptcb, OS_TCB *)
        */
        /*@ Given observed */
        /*@ Assert exists next_history,
          UCOS2_state_inv(sg, before) && task_stat_stk_chk_configuration(sg) &&
          task_stk_chk_global_addresses(sg, &OSTCBCur, &OSTCBPrioTbl) &&
          task_stat_stk_chk_continuation_protocol(environment, critical, saved_local, sg,
            original, mask, caller_frame, before) &&
          task_stat_stk_chk_continuation_safe(environment, critical, saved_local, sg,
            original, mask, caller_frame, before, X) &&
          &stk_data != 0 && 0 <= prio && prio < 64 &&
          task_stat_stk_chk_continuation_prefix(environment, critical, saved_local, sg, mask,
            caller_frame, &stk_data, original, before, prio + 1, next_history, returned, after) &&
          UCOS2_state_inv(sg, after) &&
          task_suspend_closed(environment, critical, saved_local, sg, returned, mask, after) *
          caller_frame * task_stk_chk_output_undef(&stk_data) * undef_data_at(&ptcb, OS_TCB *) *
          undef_data_at(&err, unsigned char)
        */
    }
    /*@ Given current_caller current history */
    /*@ task_stk_chk_output_undef(&stk_data)
      which implies undef_data_at(&(stk_data.OSFree), unsigned int) *
        undef_data_at(&(stk_data.OSUsed), unsigned int)
    */
}
