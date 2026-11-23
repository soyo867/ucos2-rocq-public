/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSMemNameGet (OS_MEM   *pmem,
                     INT8U   **pname,
                     INT8U    *perr)
/*@ With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
    (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
    (mask : Z) (before : UCOS2_Verify_State) (pe pn err : Z)
    (view : MemQueryView) (raw : NameResourceState) (raw_chars : list Z) (old : option Z)
    (X : MemNameGetObservation -> UCOS2_Verify_State -> Prop)
    Require pmem == pe && pname == pn && perr == err &&
      mem_name_get_addresses(sg, &OSIntNesting) &&
      mem_name_get_pre(platform, critical, sg, invocation, origin, mask, before,
        pe, pn, err, view, raw, raw_chars, old) &&
      mem_name_get_safe(critical, sg, invocation, pe, pn, view, raw, raw_chars, before, X)
    Ensure mem_name_get_post(platform, critical, sg, invocation, origin, mask, before,
      pe, pn, err, view, raw, raw_chars, old, __return, X)
*/
{
    INT8U      len;
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif



    /*@ perr == err && mem_name_get_pre(platform, critical, sg, invocation, origin, mask, before,
        pe, pn, err, view, raw, raw_chars, old)
      which implies
      perr == err && mem_name_get_access(critical, sg, invocation, pe, pn, view, raw, raw_chars, before, old) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) *
      undef_data_at(perr, unsigned char) * task_name_get_output_cell(pn, old) *
      mem_name_get_guarded_source(sg, pe, pn, view, raw_chars, before)
    */
#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return (0u);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pmem == (OS_MEM *)0) {                   /* Is 'pmem' a NULL pointer?                          */
        *perr = OS_ERR_MEM_INVALID_PMEM;
        return (0u);
    }
    if (pname == (INT8U **)0) {                  /* Is 'pname' a NULL pointer?                         */
        *perr = OS_ERR_PNAME_NULL;
        return (0u);
    }
#endif
    /*@ mem_name_get_addresses(sg, &OSIntNesting) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
      which implies mem_name_get_addresses(sg, &OSIntNesting) && UCOS2_state_inv(sg, before) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      data_at(&OSIntNesting, unsigned char, task_name_get_nesting(before)) *
      task_name_get_nesting_frame(sg, before)
    */
    if (OSIntNesting > 0u) {                     /* See if trying to call from an ISR                  */
        /*@ mem_name_get_addresses(sg, &OSIntNesting) && UCOS2_state_inv(sg, before) &&
          interrupt_platform_running(platform, invocation, origin, mask) *
          data_at(&OSIntNesting, unsigned char, task_name_get_nesting(before)) *
          task_name_get_nesting_frame(sg, before)
          which implies mem_name_get_addresses(sg, &OSIntNesting) &&
          0 <= task_name_get_nesting(before) && task_name_get_nesting(before) < 256 &&
          mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
        */
        *perr = OS_ERR_NAME_GET_ISR;
        return (0u);
    }
    /*@ mem_name_get_addresses(sg, &OSIntNesting) && UCOS2_state_inv(sg, before) &&
      interrupt_platform_running(platform, invocation, origin, mask) *
      data_at(&OSIntNesting, unsigned char, task_name_get_nesting(before)) *
      task_name_get_nesting_frame(sg, before)
      which implies mem_name_get_addresses(sg, &OSIntNesting) &&
      0 <= task_name_get_nesting(before) && task_name_get_nesting(before) < 256 &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
    */
    /*@ Assert pmem == pe && pname == pn && perr == err && pe != 0 && pn != 0 &&
      mem_name_get_early_error(pe, pn, task_name_get_nesting(before)) == None &&
      mem_name_get_access(critical, sg, invocation, pe, pn, view, raw, raw_chars, before, old) &&
      mem_name_get_safe(critical, sg, invocation, pe, pn, view, raw, raw_chars, before, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) *
      undef_data_at(perr, unsigned char) * task_name_get_output_cell(pname, old) *
      mem_name_get_guarded_source(sg, pe, pn, view, raw_chars, before) *
      undef_data_at(&len, unsigned char) * data_at(&cpu_sr, unsigned int, 0)
    */
    /*@ mem_name_get_access(critical, sg, invocation, pe, pn, view, raw, raw_chars, before, old) &&
      mem_name_get_early_error(pe, pn, task_name_get_nesting(before)) == None &&
      task_name_get_output_cell(pn, old) * mem_name_get_guarded_source(sg, pe, pn, view, raw_chars, before)
      which implies exists previous,
      mem_name_get_admission(critical, sg, invocation, pe, view, raw, raw_chars, before) &&
      old == Some(previous) &&
      mem_name_get_early_error(pe, pn, task_name_get_nesting(before)) == None &&
      data_at(pn, INT8U *, previous) * mem_name_get_source(sg, pe, view, raw_chars)
    */
    /*@ Given previous */
    OS_ENTER_CRITICAL();
    /*@ Assert exists acquired,
      pmem == pe && pname == pn && perr == err && pe != 0 && pn != 0 && old == Some(previous) &&
      mem_name_get_early_error(pe, pn, task_name_get_nesting(before)) == None &&
      mem_query_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, acquired) &&
      mem_name_get_admission(critical, sg, invocation, pe, view, raw, raw_chars, before) &&
      mem_name_get_safe(critical, sg, invocation, pe, pn, view, raw, raw_chars, before, X) &&
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
      UCOS2_inv(sg, acquired) * mem_name_get_source(sg, pe, view, raw_chars) *
      data_at(pname, INT8U *, previous) * undef_data_at(perr, unsigned char) * undef_data_at(&len, unsigned char)
    */
    /*@ Given acquired */
    /*@ mem_query_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, acquired) &&
      mem_name_get_admission(critical, sg, invocation, pe, view, raw, raw_chars, before) &&
      UCOS2_inv(sg, acquired) * mem_name_get_source(sg, pe, view, raw_chars)
      which implies exists image chars,
      mem_query_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, acquired) &&
      mem_name_get_admission(critical, sg, invocation, pe, view, raw, raw_chars, before) &&
      mem_name_get_selected(view, raw, raw_chars, acquired, image, chars) &&
      data_at(&((OS_MEM *)pe)->OSMemName, INT8U *, memImageName(image)) *
      mem_name_get_control_residual(sg, pe, view, acquired, image) * mem_name_get_raw_bytes(view, raw_chars)
    */
    /*@ Given image chars */
    *pname = pmem->OSMemName;
    /*@ mem_name_get_admission(critical, sg, invocation, pe, view, raw, raw_chars, before) &&
      mem_name_get_selected(view, raw, raw_chars, acquired, image, chars) &&
      data_at(&((OS_MEM *)pe)->OSMemName, INT8U *, memImageName(image)) *
      mem_name_get_control_residual(sg, pe, view, acquired, image) * mem_name_get_raw_bytes(view, raw_chars)
      which implies mem_name_get_admission(critical, sg, invocation, pe, view, raw, raw_chars, before) &&
      mem_name_get_selected(view, raw, raw_chars, acquired, image, chars) &&
      UCOS2_inv(sg, acquired) * mem_name_get_source(sg, pe, view, raw_chars)
    */
    /*@ mem_query_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, acquired) &&
      mem_name_get_selected(view, raw, raw_chars, acquired, image, chars) &&
      UCOS2_inv(sg, acquired) * mem_name_get_source(sg, pe, view, raw_chars)
      which implies mem_query_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, acquired) &&
      mem_name_get_selected(view, raw, raw_chars, acquired, image, chars) &&
      task_name_get_readable(mem_name_get_names(view, raw, acquired), memImageName(image), chars) &&
      task_name_get_name_bytes(memImageName(image), chars) *
      mem_name_get_string_residual(sg, pe, view, acquired, memImageName(image), chars)
    */
    /*@ mem_name_get_string_residual(sg, pe, view, acquired, memImageName(image), chars) *
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
      undef_data_at(err, unsigned char)
      which implies mem_name_get_call_frame(platform, critical, sg, invocation, origin, cpu_sr,
        pe, err, view, acquired, memImageName(image), chars)
    */
    len    = OS_StrLen(*pname) /*@ where (mem_name_get_spec) entry=memImageName(image),
      names=mem_name_get_names(view, raw, acquired), chars=chars,
      frame=mem_name_get_call_frame(platform, critical, sg, invocation, origin, cpu_sr,
        pe, err, view, acquired, memImageName(image), chars) */;
    /*@ mem_name_get_call_frame(platform, critical, sg, invocation, origin, cpu_sr,
        pe, err, view, acquired, memImageName(image), chars)
      which implies mem_name_get_string_residual(sg, pe, view, acquired, memImageName(image), chars) *
      critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, acquired) *
      undef_data_at(err, unsigned char)
    */
    /*@ mem_query_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, acquired) &&
      mem_name_get_selected(view, raw, raw_chars, acquired, image, chars) &&
      task_name_get_name_bytes(memImageName(image), chars) *
      mem_name_get_string_residual(sg, pe, view, acquired, memImageName(image), chars)
      which implies mem_query_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, acquired) &&
      mem_name_get_selected(view, raw, raw_chars, acquired, image, chars) &&
      UCOS2_inv(sg, acquired) * mem_name_get_source(sg, pe, view, raw_chars)
    */
    OS_EXIT_CRITICAL();
    *perr  = OS_ERR_NONE;
    return (len);
}
