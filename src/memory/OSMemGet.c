/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  *OSMemGet (OS_MEM  *pmem,
                 INT8U   *perr)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
    (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
    (mask: Z) (before: UCOS2_Verify_State) (view: MemGetView) (pe error_addr: Z)
    (X: MemGetOutcome -> UCOS2_Verify_State -> Prop)
    Require pmem == pe && perr == error_addr && mem_get_profile(sg) &&
      mem_get_call_domain(critical, sg, invocation, view, pe, before) &&
      mem_get_safe(critical, sg, invocation, view, pe, before, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) *
      mem_get_input_resources(sg, view, pe) * undef_data_at(perr, unsigned char)
    Ensure mem_get_api_post(platform, critical, sg, invocation, origin, mask,
      view, pe, error_addr, before, __return, X)
*/
{
    void      *pblk;
#if OS_CRITICAL_METHOD == 3u                          /* Allocate storage for CPU status register      */
    OS_CPU_SR  cpu_sr = 0u;
#endif


#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return ((void *)0);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (pmem == (OS_MEM *)0) {                        /* Must point to a valid memory partition        */
        *perr = OS_ERR_MEM_INVALID_PMEM;
        return ((void *)0);
    }
#endif

    OS_TRACE_MEM_GET_ENTER(pmem);

    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State),
        pmem == pe && pmem != 0 && mem_get_profile(sg) &&
        mem_get_call_domain(critical, sg, invocation, view, pe, before) &&
        critical_region_interval(critical, sg, invocation, before, entry) &&
        UCOS2_state_inv(sg, entry) && interrupt_saved_value(mask, cpu_sr) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        UCOS2_inv(sg, entry) * mem_get_input_resources(sg, view, pe)
        which implies exists (entry: UCOS2_Verify_State) (access: MemGetAccess),
        pmem == pe && pmem != 0 && mem_get_profile(sg) &&
        critical_region_interval(critical, sg, invocation, before, entry) &&
        UCOS2_state_inv(sg, entry) && interrupt_saved_value(mask, cpu_sr) &&
        mem_get_access_matches(sg, view, pe, entry, access) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        data_at(&pmem->OSMemFreeList, void *, memImageFree(mem_get_access_image(access))) *
        data_at(&pmem->OSMemNFree, unsigned int, memImageNFree(mem_get_access_image(access))) *
        mem_get_control_frame(sg, pe, entry, access)
    */
    /*@ Given entry access */
    /*@ 0 <= memImageNFree(mem_get_access_image(access)) &&
        memImageNFree(mem_get_access_image(access)) <= 4294967295 by local */
    if (pmem->OSMemNFree > 0u) {                      /* See if there are any free memory blocks       */
        pblk                = pmem->OSMemFreeList;    /* Yes, point to next free memory block          */
        /*@ pblk == memImageFree(mem_get_access_image(access)) &&
            0 < memImageNFree(mem_get_access_image(access)) &&
            mem_get_control_frame(sg, pe, entry, access)
            which implies pblk == memImageFree(mem_get_access_image(access)) &&
            0 < memImageNFree(mem_get_access_image(access)) &&
            data_at(pblk, void *, mem_get_access_next(access)) *
            mem_get_success_frame(sg, pe, entry, access)
        */
        pmem->OSMemFreeList = *(void **)pblk;         /*      Adjust pointer to new free list          */
        pmem->OSMemNFree--;                           /*      One less memory block in this partition  */
        /*@ pmem == pe && pmem != 0 && mem_get_profile(sg) &&
            critical_region_interval(critical, sg, invocation, before, entry) &&
            UCOS2_state_inv(sg, entry) && interrupt_saved_value(mask, cpu_sr) &&
            mem_get_access_matches(sg, view, pe, entry, access) &&
            pblk == memImageFree(mem_get_access_image(access)) &&
            0 < memImageNFree(mem_get_access_image(access)) &&
            memImageNFree(mem_get_access_image(access)) <= 4294967295 &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
            data_at(&pmem->OSMemFreeList, void *, mem_get_access_next(access)) *
            data_at(&pmem->OSMemNFree, unsigned int, memImageNFree(mem_get_access_image(access)) - 1) *
            data_at(pblk, void *, mem_get_access_next(access)) *
            mem_get_success_frame(sg, pe, entry, access)
            which implies pmem == pe && pmem != 0 &&
            critical_region_interval(critical, sg, invocation, before, entry) &&
            pblk == mem_get_pointer(mem_get_access_outcome(access)) &&
            mem_get_error(mem_get_access_outcome(access)) == 0 &&
            mem_get_protected(sg, view, pe, entry, mem_get_access_outcome(access), mem_get_access_checkpoint(entry, access)) &&
            mbox_accept_cpu_restore_pre(platform, critical, sg, invocation, origin, mask, cpu_sr, entry, mem_get_access_checkpoint(entry, access)) *
            mem_get_outcome_resources(sg, view, pe, mem_get_access_outcome(access))
        */
        OS_EXIT_CRITICAL();
        *perr = OS_ERR_NONE;                          /*      No error                                 */
        OS_TRACE_MEM_GET_EXIT(*perr);
        return (pblk);                                /*      Return memory block to caller            */
    }
    /*@ pmem == pe && pmem != 0 && mem_get_profile(sg) &&
        critical_region_interval(critical, sg, invocation, before, entry) &&
        UCOS2_state_inv(sg, entry) && interrupt_saved_value(mask, cpu_sr) &&
        mem_get_access_matches(sg, view, pe, entry, access) &&
        0 <= memImageNFree(mem_get_access_image(access)) &&
        memImageNFree(mem_get_access_image(access)) <= 0 &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        data_at(&pmem->OSMemFreeList, void *, memImageFree(mem_get_access_image(access))) *
        data_at(&pmem->OSMemNFree, unsigned int, memImageNFree(mem_get_access_image(access))) *
        mem_get_control_frame(sg, pe, entry, access)
        which implies pmem == pe && pmem != 0 &&
        critical_region_interval(critical, sg, invocation, before, entry) &&
        mem_get_protected(sg, view, pe, entry, mem_get_empty_outcome, entry) &&
        mbox_accept_cpu_restore_pre(platform, critical, sg, invocation, origin, mask, cpu_sr, entry, entry) *
        mem_get_outcome_resources(sg, view, pe, mem_get_empty_outcome)
    */
    OS_EXIT_CRITICAL();
    *perr = OS_ERR_MEM_NO_FREE_BLKS;                  /* No,  Notify caller of empty memory partition  */
    OS_TRACE_MEM_GET_EXIT(*perr);
    return ((void *)0);                               /*      Return NULL pointer to caller            */
}
