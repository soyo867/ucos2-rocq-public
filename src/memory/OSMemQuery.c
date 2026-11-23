/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

INT8U  OSMemQuery (OS_MEM       *pmem,
                   OS_MEM_DATA  *p_mem_data)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
    (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
    (mask: Z) (before: UCOS2_Verify_State) (view: MemQueryView)
    (pe pd: addr) (caller_frame: Assertion)
    (X: Z -> option (list Z) -> UCOS2_Verify_State -> Prop)
    Require pmem == pe && p_mem_data == pd &&
      mem_query_safe(critical, sg, invocation, view, pe, pd, before, X) && caller_frame *
      (pmem == 0 || (pmem != 0 && p_mem_data == 0) ||
       (pmem != 0 && p_mem_data != 0 &&
        coq_prop(mem_query_admission(critical, sg, invocation, pe, view, before)) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) *
        mem_query_source_rep(sg, pe, view) *
        undef_data_at(&((OS_MEM_DATA *)pd)->OSAddr, void *) *
        undef_data_at(&((OS_MEM_DATA *)pd)->OSFreeList, void *) *
        undef_data_at(&((OS_MEM_DATA *)pd)->OSBlkSize, unsigned int) *
        undef_data_at(&((OS_MEM_DATA *)pd)->OSNBlks, unsigned int) *
        undef_data_at(&((OS_MEM_DATA *)pd)->OSNFree, unsigned int) *
        undef_data_at(&((OS_MEM_DATA *)pd)->OSNUsed, unsigned int)))
    Ensure mem_query_api_post(platform, critical, sg, invocation, origin, mask,
      view, pe, pd, before, __return, X) * caller_frame
*/
{
#if OS_CRITICAL_METHOD == 3u                     /* Allocate storage for CPU status register           */
    OS_CPU_SR  cpu_sr = 0u;
#endif



#if OS_ARG_CHK_EN > 0u
    if (pmem == (OS_MEM *)0) {                   /* Must point to a valid memory partition             */
        return (OS_ERR_MEM_INVALID_PMEM);
    }
    if (p_mem_data == (OS_MEM_DATA *)0) {        /* Must release a valid storage area for the data     */
        return (OS_ERR_MEM_INVALID_PDATA);
    }
#endif
    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State),
        coq_prop(mem_query_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
        coq_prop(mem_query_admission(critical, sg, invocation, pe, view, before)) &&
        pmem == pe && p_mem_data == pd && pmem != 0 && p_mem_data != 0 &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        UCOS2_inv(sg, entry) * mem_query_source_rep(sg, pe, view)
        which implies exists (entry: UCOS2_Verify_State) (image: MemoryControlImage),
        pmem == pe && p_mem_data == pd && pmem != 0 && p_mem_data != 0 &&
        mem_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, view, pe, image) *
        data_at(&((OS_MEM *)pe)->OSMemAddr, void *, memImageBase(image)) *
        data_at(&((OS_MEM *)pe)->OSMemFreeList, void *, memImageFree(image)) *
        data_at(&((OS_MEM *)pe)->OSMemBlkSize, unsigned int, memImageSize(image)) *
        data_at(&((OS_MEM *)pe)->OSMemNBlks, unsigned int, memImageCount(image)) *
        data_at(&((OS_MEM *)pe)->OSMemNFree, unsigned int, memImageNFree(image))
    */
    /*@ Given entry image */
    p_mem_data->OSAddr     = pmem->OSMemAddr;
    p_mem_data->OSFreeList = pmem->OSMemFreeList;
    p_mem_data->OSBlkSize  = pmem->OSMemBlkSize;
    p_mem_data->OSNBlks    = pmem->OSMemNBlks;
    p_mem_data->OSNFree    = pmem->OSMemNFree;
    /*@ pmem == pe && p_mem_data == pd && pmem != 0 && p_mem_data != 0 &&
        mem_query_copy_frame(platform, critical, sg, invocation, origin, mask, cpu_sr,
          before, entry, view, pe, image) *
        data_at(&((OS_MEM *)pe)->OSMemAddr, void *, memImageBase(image)) *
        data_at(&((OS_MEM *)pe)->OSMemFreeList, void *, memImageFree(image)) *
        data_at(&((OS_MEM *)pe)->OSMemBlkSize, unsigned int, memImageSize(image)) *
        data_at(&((OS_MEM *)pe)->OSMemNBlks, unsigned int, memImageCount(image)) *
        data_at(&((OS_MEM *)pe)->OSMemNFree, unsigned int, memImageNFree(image))
        which implies pmem == pe && p_mem_data == pd && pmem != 0 && p_mem_data != 0 &&
        coq_prop(mem_query_acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
        coq_prop(mem_query_selected(view, entry, image)) &&
        critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
        UCOS2_inv(sg, entry) * mem_query_source_rep(sg, pe, view)
    */
    OS_EXIT_CRITICAL();
    p_mem_data->OSNUsed    = p_mem_data->OSNBlks - p_mem_data->OSNFree;
    return (OS_ERR_NONE);
}
