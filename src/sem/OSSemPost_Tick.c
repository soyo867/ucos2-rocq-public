/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSSemPost (OS_EVENT *pevent)

/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
    (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
    (region_entry before : UCOS2_Verify_State) (pe : Z)
    Require pevent == pe && sem_post_profile(sg) &&
      time_tick_post_readable(sg, before, pe) && event_table_layout_prop(sg) &&
      time_tick_internal_addresses(sg, &OSIntNesting, &OSTCBPrioTbl, &OSUnMapTbl, &OSRdyGrp, &OSRdyTbl) &&
      os_sched_ints(before) > 0 &&
      time_tick_sched_owned(platform, critical, sg, invocation, origin, region_entry, before)
    Ensure exists (after : UCOS2_Verify_State), time_tick_sem_result(sg, pe, before, __return, after) &&
      time_tick_sched_owned(platform, critical, sg, invocation, origin, region_entry, after)
*/
{
#if OS_CRITICAL_METHOD == 3u
    OS_CPU_SR cpu_sr = 0u;
#endif
#if OS_ARG_CHK_EN > 0u
    if (pevent == (OS_EVENT *)0) {
        return (OS_ERR_PEVENT_NULL);
    }
#endif
    /*@ time_tick_sched_owned(platform, critical, sg, invocation, origin, region_entry, before)
      which implies UCOS2_state_inv(sg, before) &&
      interrupt_platform_running(platform, invocation, origin, 192) *
      critical_region_inside(critical, sg, invocation, region_entry) * UCOS2_inv(sg, before) * unmap_table_rep(sg) */
    OS_TRACE_SEM_POST_ENTER(pevent);
    
    
    /*@ pevent == pe && pevent != 0 && time_tick_post_readable(sg, before, pe) &&
      event_table_layout_prop(sg) && UCOS2_state_inv(sg, before) && UCOS2_inv(sg, before)
      which implies exists (eid : Z) (node : OSEventAbstractState),
      pevent == pe && pevent != 0 && pevent == event_addr(sg, eid) && valid_event_id(sg, eid) &&
      event_object_layout_prop(sg, eid) && UCOS2_state_inv(sg, before) &&
      sem_post_lookup(before, eid, node) &&
      0 <= time_tick_sem_type(node) && time_tick_sem_type(node) <= 255 &&
      data_at(&pevent->OSEventType, INT8U, time_tick_sem_type(node)) * sem_post_type_frame(sg, before, eid, node) */
    /*@ Given eid node */
    if (pevent->OSEventType != OS_EVENT_TYPE_SEM) {
        OS_TRACE_SEM_POST_EXIT(OS_ERR_EVENT_TYPE);
        /*@ 
          pevent == pe && pevent != 0 && pevent == event_addr(sg, eid) &&
          event_object_layout_prop(sg, eid) && UCOS2_state_inv(sg, before) &&
          sem_post_lookup(before, eid, node) && time_tick_sem_type(node) != 3 &&
          data_at(&pevent->OSEventType, INT8U, time_tick_sem_type(node)) * sem_post_type_frame(sg, before, eid, node)
          which implies pevent == pe && time_tick_sem_result(sg, pe, before, 1, before) && UCOS2_inv(sg, before) */
        return (OS_ERR_EVENT_TYPE);
    }
    
    /*@ 
      pevent == pe && pevent != 0 && pevent == event_addr(sg, eid) &&
      event_object_layout_prop(sg, eid) && UCOS2_state_inv(sg, before) &&
      sem_post_lookup(before, eid, node) && time_tick_sem_type(node) == 3 &&
      data_at(&pevent->OSEventType, INT8U, time_tick_sem_type(node)) * sem_post_type_frame(sg, before, eid, node)
      which implies 
      pevent == pe && pevent != 0 && pevent == event_addr(sg, eid) &&
      event_object_layout_prop(sg, eid) && UCOS2_state_inv(sg, before) &&
      sem_post_lookup(before, eid, node) && time_tick_sem_type(node) == 3 && UCOS2_inv(sg, before) */
    OS_ENTER_CRITICAL();
    
    /*@ 
      pevent == event_addr(sg, eid) && event_object_layout_prop(sg, eid) &&
      sem_post_lookup(before, eid, node) && UCOS2_inv(sg, before)
      which implies 
      pevent == event_addr(sg, eid) && event_object_layout_prop(sg, eid) &&
      sem_post_lookup(before, eid, node) && UCOS2_state_inv(sg, before) &&
      data_at(&pevent->OSEventGrp, INT8U, sem_post_group(before, node)) * sem_post_group_frame(sg, before, eid, node) */
    if (pevent->OSEventGrp != 0u) {
        
        /*@ 
          pevent == event_addr(sg, eid) && event_object_layout_prop(sg, eid) &&
          UCOS2_state_inv(sg, before) && sem_post_lookup(before, eid, node) &&
          time_tick_sem_type(node) == 3 && sem_post_group(before, node) != 0 &&
          data_at(&pevent->OSEventGrp, INT8U, sem_post_group(before, node)) *
          sem_post_group_frame(sg, before, eid, node) * unmap_table_rep(sg)
          which implies exists (tid : Z) (old : TaskAbstractState),
          pevent == event_addr(sg, eid) && UCOS2_state_inv(sg, before) &&
          sem_post_lookup(before, eid, node) && time_tick_sem_type(node) == 3 &&
          sem_post_group(before, node) != 0 && event_task_rdy_entry(sg, TskState(before), eid, node, tid, old) &&
          event_task_rdy_pre(sg, TskState(before), eid, node, tid, old, 1, 0,
            time_tick_sem_ready_group(before), time_tick_sem_ready_rows(before)) *
          sem_post_wake_frame(sg, before, eid, tid) */
        (void)OS_EventTaskRdy(pevent, (void *)0, OS_STAT_SEM, OS_STAT_PEND_OK);
        
        
        /*@ exists (tid : Z) (old : TaskAbstractState) (priority : Z),
          UCOS2_state_inv(sg, before) && sem_post_lookup(before, eid, node) &&
          time_tick_sem_type(node) == 3 && sem_post_group(before, node) != 0 &&
          pevent == pe && pevent != 0 && pevent == event_addr(sg, eid) &&
          event_task_rdy_entry(sg, TskState(before), eid, node, tid, old) &&
          event_task_rdy_post(sg, TskState(before), eid, node, tid, old, 0, 1, 0,
            time_tick_sem_ready_group(before), time_tick_sem_ready_rows(before), priority) *
          sem_post_wake_frame(sg, before, eid, tid)
          which implies exists (after : UCOS2_Verify_State),
          pevent == pe && time_tick_sem_result(sg, pe, before, 0, after) && os_sched_ints(after) == os_sched_ints(before) &&
          UCOS2_inv(sg, after) * unmap_table_rep(sg) */
        /*@ Given after */
        OS_EXIT_CRITICAL();
        
        /*@
          os_sched_ints(after) == os_sched_ints(before) && os_sched_ints(before) > 0 &&
          interrupt_platform_running(platform, invocation, origin, 192) *
          critical_region_inside(critical, sg, invocation, region_entry) * UCOS2_inv(sg, after) * unmap_table_rep(sg)
          which implies os_sched_ints(after) > 0 &&
          time_tick_sched_owned(platform, critical, sg, invocation, origin, region_entry, after) */
        OS_Sched();
        OS_TRACE_SEM_POST_EXIT(OS_ERR_NONE);
        return (OS_ERR_NONE);
    }
    
    /*@ 
      pevent == event_addr(sg, eid) && event_object_layout_prop(sg, eid) &&
      UCOS2_state_inv(sg, before) && sem_post_lookup(before, eid, node) &&
      time_tick_sem_type(node) == 3 && sem_post_group(before, node) == 0 &&
      data_at(&pevent->OSEventGrp, INT8U, sem_post_group(before, node)) * sem_post_group_frame(sg, before, eid, node)
      which implies 
      pevent == event_addr(sg, eid) && event_object_layout_prop(sg, eid) &&
      UCOS2_state_inv(sg, before) && sem_post_lookup(before, eid, node) &&
      time_tick_sem_type(node) == 3 && sem_post_group(before, node) == 0 &&
      0 <= encode_event_cnt_value(node) && encode_event_cnt_value(node) <= 65535 &&
      data_at(&pevent->OSEventCnt, INT16U, encode_event_cnt_value(node)) * sem_post_count_frame(sg, before, eid, node) */
    if (pevent->OSEventCnt < 65535u) {
        pevent->OSEventCnt++;
        
        /*@ 
          pevent == pe && pevent != 0 && pevent == event_addr(sg, eid) &&
          event_object_layout_prop(sg, eid) && UCOS2_state_inv(sg, before) &&
          sem_post_lookup(before, eid, node) && time_tick_sem_type(node) == 3 && sem_post_group(before, node) == 0 &&
          0 <= encode_event_cnt_value(node) && encode_event_cnt_value(node) < 65535 &&
          data_at(&pevent->OSEventCnt, INT16U, encode_event_cnt_value(node) + 1) * sem_post_count_frame(sg, before, eid, node)
          which implies 
          pevent == pe && time_tick_sem_result(sg, pe, before, 0, sem_post_count_checkpoint(before, eid, node)) &&
          UCOS2_inv(sg, sem_post_count_checkpoint(before, eid, node)) */
        OS_EXIT_CRITICAL();
        OS_TRACE_SEM_POST_EXIT(OS_ERR_NONE);
        return (OS_ERR_NONE);
    }
    
    /*@ 
      pevent == pe && pevent != 0 && pevent == event_addr(sg, eid) &&
      event_object_layout_prop(sg, eid) && UCOS2_state_inv(sg, before) &&
      sem_post_lookup(before, eid, node) && time_tick_sem_type(node) == 3 && sem_post_group(before, node) == 0 &&
      encode_event_cnt_value(node) >= 65535 && encode_event_cnt_value(node) <= 65535 &&
      data_at(&pevent->OSEventCnt, INT16U, encode_event_cnt_value(node)) * sem_post_count_frame(sg, before, eid, node)
      which implies pevent == pe && time_tick_sem_result(sg, pe, before, 51, before) && UCOS2_inv(sg, before) */
    OS_EXIT_CRITICAL();
    OS_TRACE_SEM_POST_EXIT(OS_ERR_SEM_OVF);
    return (OS_ERR_SEM_OVF);
}
