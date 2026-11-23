/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSFlagNameSet (OS_FLAG_GRP  *pgrp,
                     INT8U        *pname,
                     INT8U        *perr)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
    (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
    (mask : Z) (before : UCOS2_Verify_State) (view : FlagQueryView)
    (p name error_addr : addr) (caller_frame : Assertion)
    (X : FlagNameSetResult -> UCOS2_Verify_State -> Prop)
    Require pgrp == p && pname == name && perr == error_addr &&
      flag_name_set_safe(critical, sg, invocation, view, p, name, before, X) &&
      caller_frame * undef_data_at(perr, unsigned char) *
      (pgrp == 0 || (pgrp != 0 && pname == 0) ||
       (pgrp != 0 && pname != 0 &&
        mem_name_set_nesting_address(sg, &OSIntNesting) &&
        flag_name_set_admission(critical, sg, invocation, p, name, view, before) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) *
        (task_name_set_nesting(before) > 0 ||
         (task_name_set_nesting(before) == 0 && flag_name_set_input_rep(p, view)))))
    Ensure flag_name_set_api_post(platform, critical, sg, invocation, origin, mask,
      view, p, name, error_addr, before, X) * caller_frame
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
    if (pgrp == (OS_FLAG_GRP *)0) {              /* Is 'pgrp' a NULL pointer?                          */
        *perr = OS_ERR_FLAG_INVALID_PGRP;
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
        mem_name_set_nesting_address(sg, &OSIntNesting) && UCOS2_state_inv(sg, before) &&
        0 <= task_name_set_nesting(before) && task_name_set_nesting(before) <= 255 &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&OSIntNesting, unsigned char, task_name_set_nesting(before)) *
        task_name_set_observation_frame(sg, before)
    */
    if (OSIntNesting > 0u) {                     /* See if trying to call from an ISR                  */
    /*@ mem_name_set_nesting_address(sg, &OSIntNesting) && UCOS2_state_inv(sg, before) &&
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
    /*@ mem_name_set_nesting_address(sg, &OSIntNesting) && UCOS2_state_inv(sg, before) &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        data_at(&OSIntNesting, unsigned char, task_name_set_nesting(before)) *
        task_name_set_observation_frame(sg, before)
        which implies
        mem_name_set_nesting_address(sg, &OSIntNesting) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (entry : UCOS2_Verify_State) (image : FlagGroupImage),
        pgrp == p && pname == name && perr == error_addr && p != 0 && name != 0 &&
        task_name_set_nesting(before) == 0 &&
        flag_name_set_safe(critical, sg, invocation, view, p, name, before, X) &&
        mem_query_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
        flag_name_set_access(sg, p, view, entry, image) &&
        flag_name_set_publication_ready(view, entry, image, name) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        data_at(&((OS_FLAG_GRP *)p)->OSFlagType, unsigned char, flagImageType(image)) *
        flag_name_set_type_frame(sg, p, view, entry, image) *
        undef_data_at(perr, unsigned char) * caller_frame
    */
    /*@ Given entry image */
    if (pgrp->OSFlagType != OS_EVENT_TYPE_FLAG) {
    /*@ Assert pgrp == p && pname == name && perr == error_addr && p != 0 && name != 0 &&
        task_name_set_nesting(before) == 0 &&
        flag_name_set_safe(critical, sg, invocation, view, p, name, before, X) &&
        mem_query_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
        flag_name_set_step(view, name, entry, 1, entry) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        UCOS2_inv(sg, entry) * flag_name_set_private_rep(p, view) *
        undef_data_at(perr, unsigned char) * caller_frame
    */
        OS_EXIT_CRITICAL();
        *perr = OS_ERR_EVENT_TYPE;
        return;
    }
    /*@ flag_name_set_access(sg, p, view, entry, image) && flagImageType(image) == 5 &&
        data_at(&((OS_FLAG_GRP *)p)->OSFlagType, unsigned char, flagImageType(image)) *
        flag_name_set_type_frame(sg, p, view, entry, image)
        which implies
        flag_name_set_access(sg, p, view, entry, image) && flagImageType(image) == 5 &&
        undef_data_at(&((OS_FLAG_GRP *)p)->OSFlagName, INT8U *) *
        flag_name_set_name_frame(sg, p, view, entry, image)
    */
    pgrp->OSFlagName = pname;
    /*@ Assert pgrp == p && pname == name && perr == error_addr && p != 0 && name != 0 &&
        task_name_set_nesting(before) == 0 &&
        flag_name_set_safe(critical, sg, invocation, view, p, name, before, X) &&
        mem_query_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry) &&
        flag_name_set_step(view, name, entry, 0, flag_name_set_update(view, entry, image, name)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        UCOS2_inv(sg, flag_name_set_update(view, entry, image, name)) *
        flag_name_set_private_rep(p, flag_name_set_updated_view(view, name)) *
        undef_data_at(perr, unsigned char) * caller_frame
    */
    OS_EXIT_CRITICAL();
    OS_TRACE_EVENT_NAME_SET(pgrp, pname);
    *perr            = OS_ERR_NONE;
    return;
}
