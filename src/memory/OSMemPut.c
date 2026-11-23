/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSMemPut (OS_MEM  *pmem,
                 void    *pblk)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
    (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
    (mask: Z) (before: UCOS2_Verify_State) (input: MemPutInput)
    (X: MemPutRawResult -> UCOS2_Verify_State -> Prop)
    Require mem_put_profile(sg) &&
      mem_put_input_protocol(critical, sg, before, pmem, pblk, input) &&
      mem_put_safe(critical, sg, invocation, pmem, pblk, input, before, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) *
      mem_put_input_resources(sg, pmem, pblk, input)
    Ensure mem_put_api_post(platform, critical, sg, invocation, origin, mask, before, pmem, pblk, input, __return, X)
*/
{
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif


#if OS_ARG_CHK_EN > 0u
    if (pmem == (OS_MEM *)0) {                   /* Must point to a valid memory partition             */
        return (OS_ERR_MEM_INVALID_PMEM);
    }
    if (pblk == (void *)0) {                     /* Must release a valid block                         */
        return (OS_ERR_MEM_INVALID_PBLK);
    }
#endif

    OS_TRACE_MEM_PUT_ENTER(pmem, pblk);

    /*@ mutex_query_closed(platform, critical, sg, invocation, origin, mask, before)
        which implies
        UCOS2_state_inv(sg, before) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) */
    OS_ENTER_CRITICAL();
    /*@ Given entry */
    /*@ mem_put_profile(sg) && pmem != 0 && pblk != 0 &&
        mem_put_input_protocol(critical, sg, before, pmem, pblk, input) &&
        UCOS2_state_inv(sg, before) && UCOS2_state_inv(sg, entry) &&
        critical_region_interval(critical, sg, invocation, before, entry) &&
        UCOS2_inv(sg, entry) * mem_put_input_resources(sg, pmem, pblk, input)
        which implies
        exists (acquired: MemPutAcquired),
        mem_put_profile(sg) &&
        mem_put_acquired_facts(critical, sg, invocation, before, entry, pmem, pblk, input, acquired) &&
        data_at(&(pmem->OSMemFreeList), void*, memImageFree(mem_put_acquired_image(acquired))) *
        data_at(&(pmem->OSMemNFree), INT32U, memImageNFree(mem_put_acquired_image(acquired))) *
        data_at(&(pmem->OSMemNBlks), INT32U, memImageCount(mem_put_acquired_image(acquired))) *
        mem_put_focus_frame(sg, entry, pmem, pblk, input, acquired) */
    /*@ Given acquired */
    /*@ data_at(&(pmem->OSMemNFree), INT32U, memImageNFree(mem_put_acquired_image(acquired))) *
        data_at(&(pmem->OSMemNBlks), INT32U, memImageCount(mem_put_acquired_image(acquired)))
        which implies
        0 <= memImageNFree(mem_put_acquired_image(acquired)) &&
        memImageNFree(mem_put_acquired_image(acquired)) < 4294967296 &&
        0 <= memImageCount(mem_put_acquired_image(acquired)) &&
        memImageCount(mem_put_acquired_image(acquired)) < 4294967296 &&
        data_at(&(pmem->OSMemNFree), INT32U, memImageNFree(mem_put_acquired_image(acquired))) *
        data_at(&(pmem->OSMemNBlks), INT32U, memImageCount(mem_put_acquired_image(acquired))) */
    if (pmem->OSMemNFree >= pmem->OSMemNBlks) {  /* Make sure all blocks not already returned          */
        /*@ mem_put_profile(sg) &&
            mem_put_acquired_facts(critical, sg, invocation, before, entry, pmem, pblk, input, acquired) &&
            memImageNFree(mem_put_acquired_image(acquired)) >= memImageCount(mem_put_acquired_image(acquired)) &&
            data_at(&(pmem->OSMemFreeList), void*, memImageFree(mem_put_acquired_image(acquired))) *
            data_at(&(pmem->OSMemNFree), INT32U, memImageNFree(mem_put_acquired_image(acquired))) *
            data_at(&(pmem->OSMemNBlks), INT32U, memImageCount(mem_put_acquired_image(acquired))) *
            mem_put_focus_frame(sg, entry, pmem, pblk, input, acquired)
            which implies
            mem_put_completed(critical, sg, invocation, before, entry, pmem, pblk, input, acquired, 94, entry) &&
            UCOS2_state_inv(sg, entry) &&
            UCOS2_inv(sg, entry) * mem_put_result_resources(sg, pmem, pblk, input,
              mem_put_raw_result(pmem, pblk, mem_put_acquired_image(acquired))) */
        /*@ interrupt_saved_value(mask, cpu_sr) && UCOS2_state_inv(sg, entry) &&
            critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_inv(sg, entry)
            which implies
            mbox_accept_cpu_restore_pre(platform, critical, sg, invocation, origin, mask, cpu_sr, entry, entry) */
        OS_EXIT_CRITICAL();
        OS_TRACE_MEM_PUT_EXIT(OS_ERR_MEM_FULL);
        return (OS_ERR_MEM_FULL);
    }
    /*@ mem_put_acquired_facts(critical, sg, invocation, before, entry, pmem, pblk, input, acquired) &&
        memImageNFree(mem_put_acquired_image(acquired)) < memImageCount(mem_put_acquired_image(acquired)) &&
        mem_put_focus_frame(sg, entry, pmem, pblk, input, acquired)
        which implies
        mem_put_acquired_facts(critical, sg, invocation, before, entry, pmem, pblk, input, acquired) &&
        memImageNFree(mem_put_acquired_image(acquired)) < memImageCount(mem_put_acquired_image(acquired)) &&
        mem_put_current_allocation(input, acquired) &&
        exists (old_word: Z), data_at(pblk, void*, old_word) *
        mem_put_success_frame(sg, entry, pmem, input, acquired) */
    *(void **)pblk      = pmem->OSMemFreeList;   /* Insert released block into free block list         */
    pmem->OSMemFreeList = pblk;
    pmem->OSMemNFree++;                          /* One more memory block in this partition            */
    /*@ mem_put_profile(sg) &&
        mem_put_acquired_facts(critical, sg, invocation, before, entry, pmem, pblk, input, acquired) &&
        mem_put_current_allocation(input, acquired) &&
        0 <= memImageNFree(mem_put_acquired_image(acquired)) &&
        memImageNFree(mem_put_acquired_image(acquired)) < memImageCount(mem_put_acquired_image(acquired)) &&
        memImageCount(mem_put_acquired_image(acquired)) < 4294967296 &&
        data_at(pblk, void*, memImageFree(mem_put_acquired_image(acquired))) *
        data_at(&(pmem->OSMemFreeList), void*, pblk) *
        data_at(&(pmem->OSMemNFree), INT32U, memImageNFree(mem_put_acquired_image(acquired)) + 1) *
        data_at(&(pmem->OSMemNBlks), INT32U, memImageCount(mem_put_acquired_image(acquired))) *
        mem_put_success_frame(sg, entry, pmem, input, acquired)
        which implies
        mem_put_completed(critical, sg, invocation, before, entry, pmem, pblk, input, acquired, 0,
          mem_put_checkpoint(entry, input, acquired)) &&
        UCOS2_state_inv(sg, mem_put_checkpoint(entry, input, acquired)) &&
        UCOS2_inv(sg, mem_put_checkpoint(entry, input, acquired)) *
        mem_put_result_resources(sg, pmem, pblk, input,
          mem_put_raw_result(pmem, pblk, mem_put_acquired_image(acquired))) */
    /*@ interrupt_saved_value(mask, cpu_sr) &&
        UCOS2_state_inv(sg, mem_put_checkpoint(entry, input, acquired)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        UCOS2_inv(sg, mem_put_checkpoint(entry, input, acquired))
        which implies
        mbox_accept_cpu_restore_pre(platform, critical, sg, invocation, origin, mask, cpu_sr, entry,
          mem_put_checkpoint(entry, input, acquired)) */
    OS_EXIT_CRITICAL();
    OS_TRACE_MEM_PUT_EXIT(OS_ERR_NONE);
    return (OS_ERR_NONE);                        /* Notify caller that memory block was released       */
}
