/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSFlagNameGet (OS_FLAG_GRP   *pgrp,
                      INT8U        **pname,
                      INT8U         *perr)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
    (sg : StableGlobVars) (before : UCOS2_Verify_State) (invocation : nat)
    (origin : TaskInvocationOrigin) (mask : Z) (slot : option Z)
    (raw : FlagGroupImage) (old : option Z)
    (X : FlagNameGetObservation -> UCOS2_Verify_State -> Prop)
    Require flag_name_get_addresses(sg, pgrp, &OSIntNesting,
        &(pgrp->OSFlagType), &(pgrp->OSFlagName)) &&
      flag_name_get_pre(platform, critical, sg, invocation, origin, mask, before,
        pgrp, pname, perr, slot, raw, old) &&
      flag_name_get_safe(critical, sg, invocation, pgrp, pname, slot, raw, before, X)
    Ensure flag_name_get_post(platform, critical, sg, invocation, origin, mask, before,
      pgrp, pname, perr, slot, raw, old, __return, X)
*/
{
    INT8U      len;
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif



    /*@ flag_name_get_pre(platform, critical, sg, invocation, origin, mask, before,
        pgrp, pname, perr, slot, raw, old)
      which implies UCOS2_state_inv(sg, before) &&
      flag_name_get_access(critical, sg, invocation, before, pgrp, pname, slot, raw, old) &&
      task_name_get_closed(platform, critical, sg, invocation, origin, mask, before) *
      undef_data_at(perr, unsigned char) * task_name_get_output_cell(pname, old) *
      flag_name_get_guarded_private(before, pgrp, pname, slot, raw)
    */
#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return (0u);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pgrp == (OS_FLAG_GRP *)0) {              /* Is 'pgrp' a NULL pointer?                          */
        *perr = OS_ERR_FLAG_INVALID_PGRP;
        return (0u);
    }
    if (pname == (INT8U **)0) {                   /* Is 'pname' a NULL pointer?                         */
        *perr = OS_ERR_PNAME_NULL;
        return (0u);
    }
#endif
    /*@ flag_name_get_addresses(sg, pgrp, &OSIntNesting,
        &(pgrp->OSFlagType), &(pgrp->OSFlagName)) &&
      task_name_get_closed(platform, critical, sg, invocation, origin, mask, before)
      which implies flag_name_get_addresses(sg, pgrp, &OSIntNesting,
        &(pgrp->OSFlagType), &(pgrp->OSFlagName)) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      data_at(&OSIntNesting, unsigned char, task_name_get_nesting(before)) *
      task_name_get_nesting_frame(sg, before)
    */
    if (OSIntNesting > 0u) {                     /* See if trying to call from an ISR                  */
        /*@ flag_name_get_addresses(sg, pgrp, &OSIntNesting,
            &(pgrp->OSFlagType), &(pgrp->OSFlagName)) &&
          interrupt_platform_running(platform, invocation, origin, mask) *
          data_at(&OSIntNesting, unsigned char, task_name_get_nesting(before)) *
          task_name_get_nesting_frame(sg, before)
          which implies flag_name_get_addresses(sg, pgrp, &OSIntNesting,
            &(pgrp->OSFlagType), &(pgrp->OSFlagName)) &&
          task_name_get_closed(platform, critical, sg, invocation, origin, mask, before)
        */
        *perr = OS_ERR_NAME_GET_ISR;
        return (0u);
    }
    /*@ flag_name_get_addresses(sg, pgrp, &OSIntNesting,
        &(pgrp->OSFlagType), &(pgrp->OSFlagName)) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      data_at(&OSIntNesting, unsigned char, task_name_get_nesting(before)) *
      task_name_get_nesting_frame(sg, before)
      which implies flag_name_get_addresses(sg, pgrp, &OSIntNesting,
        &(pgrp->OSFlagType), &(pgrp->OSFlagName)) &&
      0 <= task_name_get_nesting(before) && task_name_get_nesting(before) < 256 &&
      task_name_get_closed(platform, critical, sg, invocation, origin, mask, before)
    */
    /*@ task_name_get_closed(platform, critical, sg, invocation, origin, mask, before)
      which implies interrupt_platform_running(platform, invocation, origin, mask) *
        critical_region_outside(critical, sg, invocation, before)
    */
    OS_ENTER_CRITICAL();
    /*@ Assert exists acquired,
      pgrp == pgrp@pre && pname == pname@pre && perr == perr@pre &&
      UCOS2_state_inv(sg, before) && UCOS2_state_inv(sg, acquired) &&
      flag_name_get_addresses(sg, pgrp, &OSIntNesting,
        &(pgrp->OSFlagType), &(pgrp->OSFlagName)) &&
      flag_name_get_early_error(pgrp, pname, task_name_get_nesting(before)) == None &&
      flag_name_get_access(critical, sg, invocation, before, pgrp, pname, slot, raw, old) &&
      critical_region_interval(critical, sg, invocation, before, acquired) &&
      interrupt_saved_value(mask, cpu_sr) &&
      flag_name_get_safe(critical, sg, invocation, pgrp, pname, slot, raw, before, X) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
      UCOS2_inv(sg, acquired) * flag_name_get_private(pgrp, slot, raw) *
      task_name_get_output_cell(pname, old) * undef_data_at(perr, unsigned char) *
      undef_data_at(&len, unsigned char)
    */
    /*@ Given acquired */
    /*@ flag_name_get_addresses(sg, pgrp, &OSIntNesting,
        &(pgrp->OSFlagType), &(pgrp->OSFlagName)) &&
      UCOS2_state_inv(sg, acquired) &&
      flag_name_get_early_error(pgrp, pname, task_name_get_nesting(before)) == None &&
      flag_name_get_access(critical, sg, invocation, before, pgrp, pname, slot, raw, old) &&
      critical_region_interval(critical, sg, invocation, before, acquired) &&
      UCOS2_inv(sg, acquired) * flag_name_get_private(pgrp, slot, raw)
      which implies exists image,
      flag_name_get_addresses(sg, pgrp, &OSIntNesting,
        &(pgrp->OSFlagType), &(pgrp->OSFlagName)) &&
      UCOS2_state_inv(sg, acquired) &&
      flag_name_get_early_error(pgrp, pname, task_name_get_nesting(before)) == None &&
      flag_name_get_access(critical, sg, invocation, before, pgrp, pname, slot, raw, old) &&
      critical_region_interval(critical, sg, invocation, before, acquired) &&
      flag_name_get_selected(sg, acquired, pgrp, slot, raw, image) &&
      data_at(&(pgrp->OSFlagType), unsigned char, flag_name_get_type(image)) *
      flag_name_get_name_cell(pgrp, image) * flag_name_get_read_frame(sg, acquired, pgrp, slot, image)
    */
    /*@ Given image */
    if (pgrp->OSFlagType != OS_EVENT_TYPE_FLAG) {
        /*@ flag_name_get_addresses(sg, pgrp, &OSIntNesting,
            &(pgrp->OSFlagType), &(pgrp->OSFlagName)) &&
          UCOS2_state_inv(sg, acquired) &&
          flag_name_get_selected(sg, acquired, pgrp, slot, raw, image) &&
          data_at(&(pgrp->OSFlagType), unsigned char, flag_name_get_type(image)) *
          flag_name_get_name_cell(pgrp, image) * flag_name_get_read_frame(sg, acquired, pgrp, slot, image)
          which implies flag_name_get_addresses(sg, pgrp, &OSIntNesting,
            &(pgrp->OSFlagType), &(pgrp->OSFlagName)) &&
          UCOS2_state_inv(sg, acquired) && 0 <= flag_name_get_type(image) && flag_name_get_type(image) < 256 &&
          flag_name_get_selected(sg, acquired, pgrp, slot, raw, image) &&
          UCOS2_inv(sg, acquired) * flag_name_get_private(pgrp, slot, raw)
        */
        OS_EXIT_CRITICAL();
        *perr = OS_ERR_EVENT_TYPE;
        return (0u);
    }
    /*@ flag_name_get_addresses(sg, pgrp, &OSIntNesting,
        &(pgrp->OSFlagType), &(pgrp->OSFlagName)) &&
      UCOS2_state_inv(sg, acquired) &&
      flag_name_get_selected(sg, acquired, pgrp, slot, raw, image) &&
      flag_name_get_type(image) == OS_EVENT_TYPE_FLAG &&
      flag_name_get_early_error(pgrp, pname, task_name_get_nesting(before)) == None &&
      flag_name_get_access(critical, sg, invocation, before, pgrp, pname, slot, raw, old) &&
      critical_region_interval(critical, sg, invocation, before, acquired) &&
      flag_name_get_name_cell(pgrp, image) * task_name_get_output_cell(pname, old)
      which implies exists previous chars,
      flag_name_get_addresses(sg, pgrp, &OSIntNesting,
        &(pgrp->OSFlagType), &(pgrp->OSFlagName)) &&
      UCOS2_state_inv(sg, acquired) &&
      flag_name_get_selected(sg, acquired, pgrp, slot, raw, image) &&
      flag_name_get_type(image) == OS_EVENT_TYPE_FLAG && old == Some(previous) &&
      task_name_get_readable(task_name_get_names(acquired), flag_name_get_name(image), chars) &&
      data_at(&(pgrp->OSFlagName), INT8U *, flag_name_get_name(image)) * data_at(pname, INT8U *, previous)
    */
    /*@ Given previous chars */
    *pname = pgrp->OSFlagName;
    /*@ flag_name_get_addresses(sg, pgrp, &OSIntNesting,
        &(pgrp->OSFlagType), &(pgrp->OSFlagName)) &&
      UCOS2_state_inv(sg, acquired) &&
      flag_name_get_selected(sg, acquired, pgrp, slot, raw, image) &&
      flag_name_get_type(image) == OS_EVENT_TYPE_FLAG &&
      data_at(&(pgrp->OSFlagType), unsigned char, flag_name_get_type(image)) *
      data_at(&(pgrp->OSFlagName), INT8U *, flag_name_get_name(image)) *
      flag_name_get_read_frame(sg, acquired, pgrp, slot, image)
      which implies flag_name_get_addresses(sg, pgrp, &OSIntNesting,
        &(pgrp->OSFlagType), &(pgrp->OSFlagName)) &&
      UCOS2_state_inv(sg, acquired) &&
      flag_name_get_selected(sg, acquired, pgrp, slot, raw, image) &&
      flag_name_get_type(image) == OS_EVENT_TYPE_FLAG &&
      UCOS2_inv(sg, acquired) * flag_name_get_private(pgrp, slot, raw)
    */
    /*@ UCOS2_state_inv(sg, acquired) &&
      task_name_get_readable(task_name_get_names(acquired), flag_name_get_name(image), chars) &&
      UCOS2_inv(sg, acquired)
      which implies UCOS2_state_inv(sg, acquired) &&
      task_name_get_readable(task_name_get_names(acquired), flag_name_get_name(image), chars) &&
      task_name_get_name_bytes(flag_name_get_name(image), chars) *
      task_name_get_name_frame(sg, acquired, flag_name_get_name(image), chars)
    */
    /*@ task_name_get_name_frame(sg, acquired, flag_name_get_name(image), chars) *
      flag_name_get_private(pgrp, slot, raw) *
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
      undef_data_at(perr, unsigned char)
      which implies flag_name_get_call_frame(platform, critical, sg, invocation, origin,
        cpu_sr, acquired, pgrp, perr, slot, raw, image, chars)
    */
    len    = OS_StrLen(*pname) /*@ where (flag_name_get_spec) entry=flag_name_get_name(image),
      names=task_name_get_names(acquired), chars=chars,
      frame=flag_name_get_call_frame(platform, critical, sg, invocation, origin,
        cpu_sr, acquired, pgrp, perr, slot, raw, image, chars) */;
    /*@ flag_name_get_call_frame(platform, critical, sg, invocation, origin,
        cpu_sr, acquired, pgrp, perr, slot, raw, image, chars)
      which implies task_name_get_name_frame(sg, acquired, flag_name_get_name(image), chars) *
      flag_name_get_private(pgrp, slot, raw) *
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
      undef_data_at(perr, unsigned char)
    */
    /*@ UCOS2_state_inv(sg, acquired) &&
      task_name_get_readable(task_name_get_names(acquired), flag_name_get_name(image), chars) &&
      task_name_get_name_bytes(flag_name_get_name(image), chars) *
      task_name_get_name_frame(sg, acquired, flag_name_get_name(image), chars)
      which implies UCOS2_state_inv(sg, acquired) &&
      task_name_get_readable(task_name_get_names(acquired), flag_name_get_name(image), chars) &&
      UCOS2_inv(sg, acquired)
    */
    OS_EXIT_CRITICAL();
    *perr  = OS_ERR_NONE;
    return (len);
}
