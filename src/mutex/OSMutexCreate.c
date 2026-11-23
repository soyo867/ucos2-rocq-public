/* Single-function annotation carrier; compose before canonical QCP.
 * The environment retains the pinned headers, configuration and callees.
 * Formatting and documented frontend form match the checked C input.
 */

OS_EVENT  *OSMutexCreate (INT8U   prio,
                          INT8U  *perr)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
         (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
         (mask: Z) (before: UCOS2_Verify_State) (prio_in perr_in: Z) X
    Require prio == prio_in && coq_prop(mutex_create_priority_input_prop(prio, prio_in)) && 0 <= prio_in && prio_in <= 255 && perr != 0 &&
      coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
      coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
      coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
      coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
      safeExec(LastSeen(before), atomic_cmd(publication_call_program(critical, sg, invocation, prio_in)), X) &&
      data_at(perr, unsigned char, perr_in) *
      interrupt_platform_running(platform, invocation, origin, mask) * UCOS2_inv(sg, before)
    Ensure exists (after: UCOS2_Verify_State) (retv errv: Z),
      __return == retv && prio == prio_in && perr != 0 &&
      coq_prop(publication_result_prop(critical, sg, invocation, prio_in, before, after, retv, errv)) &&
      safeExec(LastSeen(after), return(retv), X) &&
      data_at(perr, unsigned char, errv) *
      closed(platform, critical, sg, invocation, origin, mask, after)
*/
{
    OS_EVENT  *pevent;
#if OS_CRITICAL_METHOD == 3u                               /* Allocate storage for CPU status register */
    OS_CPU_SR  cpu_sr = 0u;
#endif



#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return ((OS_EVENT *)0);
    }
#endif

#ifdef OS_SAFETY_CRITICAL_IEC61508
    if (OSSafetyCriticalStartFlag == OS_TRUE) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        *perr = OS_ERR_ILLEGAL_CREATE_RUN_TIME;
        return ((OS_EVENT *)0);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (prio != OS_PRIO_MUTEX_CEIL_DIS) {
        if (prio >= OS_LOWEST_PRIO) {                      /* Validate PCP                             */
           *perr = OS_ERR_PRIO_INVALID;
            return ((OS_EVENT *)0);
        }
    }
#endif
    
/*@ coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) * UCOS2_inv(sg, before)
        which implies
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) * coq_prop(UCOS2_state_inv(sg, before)) *
        data_at(&OSIntNesting, unsigned char, intNesting(before.IntrState)) * UCOS2_inv_without_os_int_nesting(sg, before)
    */
if (OSIntNesting > 0u) {                               /* See if called from ISR ...               */
        
/*@ coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) * coq_prop(UCOS2_state_inv(sg, before)) *
        data_at(&OSIntNesting, unsigned char, intNesting(before.IntrState)) * UCOS2_inv_without_os_int_nesting(sg, before)
        which implies
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) * UCOS2_inv(sg, before)
    */
*perr = OS_ERR_CREATE_ISR;                         /* ... can't CREATE mutex from an ISR       */
        return ((OS_EVENT *)0);
    }
    
/*@ coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) * coq_prop(UCOS2_state_inv(sg, before)) *
        data_at(&OSIntNesting, unsigned char, intNesting(before.IntrState)) * UCOS2_inv_without_os_int_nesting(sg, before)
        which implies
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) * UCOS2_inv(sg, before)
    */

/*@ Branch name
        priority_enabled: prio_in != 255;
        priority_disabled: prio_in == 255
    */

/*@ 0 <= prio_in && prio_in < 63 && coq_prop(valid_stable_glob_vars(sg))
        $ priority_enabled
        which implies
        coq_prop(valid_stable_glob_vars(sg)) * coq_prop(valid_mutex_pcp(sg, prio_in))
        $ priority_enabled
    */

/*@ prio_in == 255 && coq_prop(valid_stable_glob_vars(sg))
        $ priority_disabled
        which implies
        coq_prop(valid_stable_glob_vars(sg)) * coq_prop(valid_mutex_pcp(sg, prio_in))
        $ priority_disabled
    */

/*@ interrupt_platform_running(platform, invocation, origin, mask) * UCOS2_inv(sg, before)
        which implies closed(platform, critical, sg, invocation, origin, mask, before) */
OS_ENTER_CRITICAL();
    
/*@ exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 && coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) && coq_prop(mutex_create_priority_input_prop(prio, prio_in)) && coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) && coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry)
        which implies
        exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          priority_table(sg, entry) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
    */
if (prio != OS_PRIO_MUTEX_CEIL_DIS) {
        
/*@ exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          priority_table(sg, entry) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        which implies
        exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), priority_value(sg, entry, prio_in)) *
          priority_table_missing(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
    */
if (OSTCBPrioTbl[prio] != (OS_TCB *)0) {           /* Mutex priority must not already exist    */
            
/*@ exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 && priority_value(sg, entry, prio_in) != 0 &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), priority_value(sg, entry, prio_in)) *
          priority_table_missing(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        which implies
        exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) && prio_in != 255 && 0 <= prio_in && prio_in < 64 && priority_value(sg, entry, prio_in) != 0 &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry)
    */
OS_EXIT_CRITICAL();                            /* Task already exist at priority ...       */
           *perr = OS_ERR_PRIO_EXIST;                      /* ... ceiling priority                     */
            return ((OS_EVENT *)0);
        }
        OSTCBPrioTbl[prio] = ((OS_TCB *)1);              /* Reserve the table entry                  */
    
/*@ exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 && priority_value(sg, entry, prio_in) == 0 &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), 1) *
          priority_table_missing(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        which implies
        exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
    */
}

    
/*@ exists (entry: UCOS2_Verify_State),
          prio_in == 255 && coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          priority_table(sg, entry) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        $ priority_disabled
        which implies
        exists (entry: UCOS2_Verify_State),
          prio_in == 255 && coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        $ priority_disabled
    */
pevent = OSEventFreeList;                              /* Get next free event control block        */
    if (pevent == (OS_EVENT *)0) {                         /* See if an ECB was available              */
        if (prio != OS_PRIO_MUTEX_CEIL_DIS) {
            
/*@ exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 && free_head(sg, entry) == 0 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        which implies
        exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 && free_head(sg, entry) == 0 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), 1) *
          reserved_priority_table_missing(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
    */
OSTCBPrioTbl[prio] = (OS_TCB *)0;              /* No, Release the table entry              */
        
/*@ exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 && free_head(sg, entry) == 0 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), 0) *
          reserved_priority_table_missing(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        which implies
        exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 && free_head(sg, entry) == 0 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          priority_table(sg, entry) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
    */
}
        
/*@ exists (entry: UCOS2_Verify_State),
          prio_in == 255 && coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          free_head(sg, entry) == 0 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        $ priority_disabled
        which implies
        exists (entry: UCOS2_Verify_State),
          prio_in == 255 && coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          free_head(sg, entry) == 0 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          priority_table(sg, entry) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        $ priority_disabled
    */

/*@ exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          free_head(sg, entry) == 0 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          priority_table(sg, entry) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        which implies
        exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) && free_head(sg, entry) == 0 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry)
    */
OS_EXIT_CRITICAL();
       *perr = OS_ERR_PEVENT_NULL;                         /* No more event control blocks             */
        return (pevent);
    }
    
/*@ exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          free_head(sg, entry) != 0 && pevent == free_head(sg, entry) && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        which implies
        exists (entry: UCOS2_Verify_State) (eid: EventID) (rest: list EventID) (image: EventStorage),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) && coq_prop(slot_available(sg, entry, prio_in)) &&
          coq_prop(free_head_facts(sg, entry, eid, rest, image)) && coq_prop(event_object_layout_prop(sg, eid)) && coq_prop(event_pointer_eq(sg, eid, pevent)) && pevent == free_head(sg, entry) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          node_residual(sg, entry, eid) *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry)) *
          data_at(&pevent->OSEventPtr, void *, event_encode_pool_link(sg, hd_error(rest))) *
          event_storage_without_field(false, pevent, image, EventPtrField)
    */
OSEventFreeList     = (OS_EVENT *)OSEventFreeList->OSEventPtr; /* Adjust the free list             */
    
/*@ exists (entry: UCOS2_Verify_State) (eid: EventID) (rest: list EventID) (image: EventStorage),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) && coq_prop(slot_available(sg, entry, prio_in)) &&
          coq_prop(free_head_facts(sg, entry, eid, rest, image)) && coq_prop(event_object_layout_prop(sg, eid)) && coq_prop(event_pointer_eq(sg, eid, pevent)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          node_residual(sg, entry, eid) *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, event_encode_pool_link(sg, hd_error(rest))) *
          data_at(&pevent->OSEventPtr, void *, event_encode_pool_link(sg, hd_error(rest))) *
          event_storage_without_field(false, pevent, image, EventPtrField)
        which implies
        exists (entry: UCOS2_Verify_State) (eid: EventID) (rest: list EventID) (image: EventStorage),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) && coq_prop(slot_available(sg, entry, prio_in)) &&
          coq_prop(free_head_facts(sg, entry, eid, rest, image)) && coq_prop(event_object_layout_prop(sg, eid)) && coq_prop(event_pointer_eq(sg, eid, pevent)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          node_residual(sg, entry, eid) *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, event_encode_pool_link(sg, hd_error(rest))) *
          undef_data_at(&pevent->OSEventType, unsigned char) *
          undef_data_at(&pevent->OSEventCnt, unsigned short) *
          undef_data_at(&pevent->OSEventPtr, void *) *
          event_wait_list_init_pre(&pevent->OSEventGrp, &pevent->OSEventTbl[0]) *
          initialization_padding(pevent, image)
    */
pevent->OSEventCnt  = (INT16U)((INT16U)prio << 8u) | ((INT16U)0x00FFu); /* Resource is avail.     */
    pevent->OSEventPtr  = (void *)0;                       /* No task owning the mutex                 */
#if OS_EVENT_NAME_EN > 0u
    pevent->OSEventName = (INT8U *)(void *)"?";
#endif
    OS_EventWaitListInit(pevent);
    /* Publish the initialized Mutex before restoring the saved interrupt mask. */
    pevent->OSEventType = OS_EVENT_TYPE_MUTEX;
    
/*@ exists (entry: UCOS2_Verify_State) (eid: EventID) (rest: list EventID) (image: EventStorage),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) && coq_prop(slot_available(sg, entry, prio_in)) &&
          coq_prop(free_head_facts(sg, entry, eid, rest, image)) && coq_prop(event_object_layout_prop(sg, eid)) && coq_prop(event_pointer_eq(sg, eid, pevent)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          node_residual(sg, entry, eid) *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, event_encode_pool_link(sg, hd_error(rest))) *
          data_at(&pevent->OSEventType, unsigned char, 4) *
          data_at(&pevent->OSEventCnt, unsigned short, prio_in * 256 + 255) *
          data_at(&pevent->OSEventPtr, void *, 0) *
          event_wait_list_init_post(&pevent->OSEventGrp, &pevent->OSEventTbl[0]) *
          initialization_padding(pevent, image)
        which implies
        exists (entry: UCOS2_Verify_State) (eid: EventID) (rest: list EventID) (image: EventStorage),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(event_table_layout_prop(sg)) &&
          coq_prop(slot_available(sg, entry, prio_in)) &&
          coq_prop(free_head_facts(sg, entry, eid, rest, image)) && coq_prop(event_pointer_eq(sg, eid, pevent)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          UCOS2_inv(sg, mutex_create_state(sg, prio_in, eid, rest, entry))
    */
OS_EXIT_CRITICAL();
    OS_TRACE_MUTEX_CREATE(pevent, pevent->OSEventName);
   *perr = OS_ERR_NONE;
    return (pevent);
}
