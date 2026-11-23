/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSMemNameSet (OS_MEM  *pmem,
                    INT8U   *pname,
                    INT8U   *perr)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
    (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
    (mask : Z) (before : UCOS2_Verify_State) (view : MemQueryView)
    (pe name error_addr : addr) (caller_frame : Assertion)
    (X : Z -> UCOS2_Verify_State -> Prop)
    Require pmem == pe && pname == name && perr == error_addr &&
      mem_name_set_safe(critical, sg, invocation, view, pe, name, before, X) &&
      caller_frame * undef_data_at(perr, unsigned char) *
      (pmem == 0 || (pmem != 0 && pname == 0) ||
       (pmem != 0 && pname != 0 &&
        mem_name_set_nesting_address(sg, &OSIntNesting) &&
        mem_name_set_admission(critical, sg, invocation, pe, name, view, before) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) *
        (task_name_set_nesting(before) > 0 ||
         (task_name_set_nesting(before) == 0 && mem_query_source_rep(sg, pe, view)))))
    Ensure mem_name_set_api_post(platform, critical, sg, invocation, origin, mask,
      view, pe, name, error_addr, before, X) * caller_frame
*/
{
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif



#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return;
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pmem == (OS_MEM *)0) {                   /* Is 'pmem' a NULL pointer?                          */
        *perr = OS_ERR_MEM_INVALID_PMEM;
        return;
    }
    if (pname == (INT8U *)0) {                   /* Is 'pname' a NULL pointer?                         */
        *perr = OS_ERR_PNAME_NULL;
        return;
    }
#endif
    /*@ mem_name_set_nesting_address(sg, &OSIntNesting) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
        which implies
        mem_name_set_nesting_address(sg, &OSIntNesting) &&
        UCOS2_state_inv(sg, before) &&
        0 <= task_name_set_nesting(before) && task_name_set_nesting(before) <= 255 &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&OSIntNesting, unsigned char, task_name_set_nesting(before)) *
        task_name_set_observation_frame(sg, before)
    */
    if (OSIntNesting > 0u) {                     /* See if trying to call from an ISR                  */
    /*@ mem_name_set_nesting_address(sg, &OSIntNesting) &&
        UCOS2_state_inv(sg, before) &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&OSIntNesting, unsigned char, task_name_set_nesting(before)) *
        task_name_set_observation_frame(sg, before)
        which implies
        mem_name_set_nesting_address(sg, &OSIntNesting) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
    */
        *perr = OS_ERR_NAME_SET_ISR;
        return;
    }
    /*@ mem_name_set_nesting_address(sg, &OSIntNesting) &&
        UCOS2_state_inv(sg, before) &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&OSIntNesting, unsigned char, task_name_set_nesting(before)) *
        task_name_set_observation_frame(sg, before)
        which implies
        mem_name_set_nesting_address(sg, &OSIntNesting) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (entry : UCOS2_Verify_State) (image : MemoryControlImage),
        pmem == pe && pname == name && perr == error_addr && pe != 0 && name != 0 &&
        task_name_set_nesting(before) == 0 &&
        mem_name_set_safe(critical, sg, invocation, view, pe, name, before, X) &&
        mem_query_admission(critical, sg, invocation, pe, view, before) &&
        mem_query_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
        mem_query_selected(view, entry, image) &&
        mem_name_set_name_available(view, entry, name) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        data_at(&((OS_MEM *)pe)->OSMemName, INT8U *, memImageName(image)) *
        mem_name_set_field_frame(sg, pe, view, entry, image) *
        undef_data_at(perr, unsigned char) * caller_frame
    */
    /*@ Given entry image */
    pmem->OSMemName = pname;
    /*@ Assert pmem == pe && pname == name && perr == error_addr && pe != 0 && name != 0 &&
        task_name_set_nesting(before) == 0 &&
        mem_name_set_safe(critical, sg, invocation, view, pe, name, before, X) &&
        mem_query_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
        mem_name_set_step(view, name, entry, 0, mem_name_set_update(view, entry, image, name)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        UCOS2_inv(sg, mem_name_set_update(view, entry, image, name)) *
        mem_query_source_rep(sg, pe, mem_name_set_updated_view(view, name)) *
        undef_data_at(perr, unsigned char) * caller_frame
    */
    OS_EXIT_CRITICAL();
    OS_TRACE_EVENT_NAME_SET(pmem, pname);
    *perr           = OS_ERR_NONE;
}
