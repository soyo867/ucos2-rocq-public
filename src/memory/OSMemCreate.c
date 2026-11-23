/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

OS_MEM  *OSMemCreate (void   *addr,
                      INT32U  nblks,
                      INT32U  blksize,
                      INT8U  *perr)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
    (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
    (mask: Z) (before: UCOS2_Verify_State) (mode: MemCreateInput)
    (base count size output: Z) (caller_frame: Assertion)
    (X: MemCreateOutcome -> MemCreateWorld -> Prop)
    Require addr == base && nblks == count && blksize == size && perr == output &&
      &OSMemFreeList == g_OSMemFreeList(sg) && mem_create_profile(sg) &&
      mem_create_call_domain(critical, sg, invocation, mode, base, count, size, before) &&
      mem_create_output_rely(critical, sg, invocation, mode, base, count, size, output, caller_frame) &&
      mem_create_byte_access(mem_create_entry_resources(sg, before, mode, base, count, size, caller_frame), output) &&
      mem_create_safe(critical, sg, invocation, base, count, size, output, before, X) &&
      mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) *
      mem_create_input_resources(mode, base, count, size) * caller_frame
    Ensure mem_create_api_post(platform, critical, sg, invocation, origin, mask, mode,
      base, count, size, output, before, __return, caller_frame, X)
*/
{
    OS_MEM    *pmem;
    INT8U     *pblk;
    void     **plink;
    INT32U     loops;
    INT32U     i;
#if OS_CRITICAL_METHOD == 3u                          /* Allocate storage for CPU status register      */
    OS_CPU_SR  cpu_sr = 0u;
#endif

    /*@ mem_create_arguments_in_range(base, count, size) by local */

#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return ((OS_MEM *)0);
    }
#endif

#ifdef OS_SAFETY_CRITICAL_IEC61508
    if (OSSafetyCriticalStartFlag == OS_TRUE) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        *perr = OS_ERR_ILLEGAL_CREATE_RUN_TIME;
        return ((OS_MEM *)0);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (addr == (void *)0) {                          /* Must pass a valid address for the memory part.*/
        /*@ perr == output &&
            mem_create_byte_access(mem_create_entry_resources(sg, before, mode, base, count, size, caller_frame), output) &&
            mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) *
            mem_create_input_resources(mode, base, count, size) * caller_frame
            which implies perr == output &&
            interrupt_platform_running(platform, invocation, origin, mask) *
            undef_data_at(perr, unsigned char) *
            mem_create_output_residual(mem_create_return_resources(sg, mode, base, count, size, 0, before, caller_frame), output)
        */
        *perr = OS_ERR_MEM_INVALID_ADDR;
        return ((OS_MEM *)0);
    }
    if (((INT32U)addr & (sizeof(void *) - 1u)) != 0u){  /* Must be pointer size aligned                */
        /*@ perr == output &&
            mem_create_byte_access(mem_create_entry_resources(sg, before, mode, base, count, size, caller_frame), output) &&
            mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) *
            mem_create_input_resources(mode, base, count, size) * caller_frame
            which implies perr == output &&
            interrupt_platform_running(platform, invocation, origin, mask) *
            undef_data_at(perr, unsigned char) *
            mem_create_output_residual(mem_create_return_resources(sg, mode, base, count, size, 0, before, caller_frame), output)
        */
        *perr = OS_ERR_MEM_INVALID_ADDR;
        return ((OS_MEM *)0);
    }
    if (nblks < 2u) {                                 /* Must have at least 2 blocks per partition     */
        /*@ perr == output &&
            mem_create_byte_access(mem_create_entry_resources(sg, before, mode, base, count, size, caller_frame), output) &&
            mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) *
            mem_create_input_resources(mode, base, count, size) * caller_frame
            which implies perr == output &&
            interrupt_platform_running(platform, invocation, origin, mask) *
            undef_data_at(perr, unsigned char) *
            mem_create_output_residual(mem_create_return_resources(sg, mode, base, count, size, 0, before, caller_frame), output)
        */
        *perr = OS_ERR_MEM_INVALID_BLKS;
        return ((OS_MEM *)0);
    }
    if (blksize < sizeof(void *)) {                   /* Must contain space for at least a pointer     */
        /*@ perr == output &&
            mem_create_byte_access(mem_create_entry_resources(sg, before, mode, base, count, size, caller_frame), output) &&
            mutex_query_closed(platform, critical, sg, invocation, origin, mask, before) *
            mem_create_input_resources(mode, base, count, size) * caller_frame
            which implies perr == output &&
            interrupt_platform_running(platform, invocation, origin, mask) *
            undef_data_at(perr, unsigned char) *
            mem_create_output_residual(mem_create_return_resources(sg, mode, base, count, size, 0, before, caller_frame), output)
        */
        *perr = OS_ERR_MEM_INVALID_SIZE;
        return ((OS_MEM *)0);
    }
#endif
    /*@ mem_create_arguments_valid(base, count, size) by local */
    OS_ENTER_CRITICAL();
    /*@ Given entry */
    /*@ &OSMemFreeList == g_OSMemFreeList(sg) && mem_create_profile(sg) &&
        mem_create_arguments_valid(base, count, size) &&
        critical_region_interval(critical, sg, invocation, before, entry) &&
        mem_create_output_rely(critical, sg, invocation, mode, base, count, size, output, caller_frame) &&
        mem_create_byte_access(mem_create_entry_resources(sg, before, mode, base, count, size, caller_frame), output) &&
        UCOS2_inv(sg, entry) * mem_create_input_resources(mode, base, count, size) * caller_frame
        which implies &OSMemFreeList == g_OSMemFreeList(sg) && mem_create_profile(sg) &&
        mem_create_arguments_valid(base, count, size) &&
        critical_region_interval(critical, sg, invocation, before, entry) &&
        mem_create_output_rely(critical, sg, invocation, mode, base, count, size, output, caller_frame) &&
        mem_create_byte_access(mem_create_entry_resources(sg, entry, mode, base, count, size, caller_frame), output) &&
        UCOS2_state_inv(sg, entry) &&
        data_at(&OSMemFreeList, OS_MEM *, mem_create_free_head(sg, entry)) *
        mem_create_root_frame(sg, entry) * mem_create_input_resources(mode, base, count, size) * caller_frame
    */
    pmem = OSMemFreeList;                             /* Get next free memory partition                */
    /*@ 0 <= pmem && pmem < 4294967296 by local */
    if (OSMemFreeList != (OS_MEM *)0) {               /* See if pool of free partitions was empty      */
        /*@ pmem == mem_create_free_head(sg, entry) && pmem != 0 &&
            0 <= pmem && pmem < 4294967296 &&
            mem_create_profile(sg) && UCOS2_state_inv(sg, entry) &&
            mem_create_call_domain(critical, sg, invocation, mode, base, count, size, before) &&
            critical_region_interval(critical, sg, invocation, before, entry) &&
            mem_create_arguments_valid(base, count, size) &&
            mem_create_arguments_in_range(base, count, size) &&
            addr == base && nblks == count && blksize == size &&
            mem_create_root_frame(sg, entry)
            which implies exists (private: MemoryPrivatePartition) (post: GlobMemoryState),
            pmem == memory_control_addr(sg, memPrivateSlot(private)) && pmem != 0 &&
            mem_create_profile(sg) && UCOS2_state_inv(sg, entry) && mode == MemCreateArena &&
            mem_create_arguments_valid(base, count, size) &&
            critical_region_interval(critical, sg, invocation, before, entry) &&
            addr == base && nblks == count && blksize == size &&
            mem_create_reservation(sg, base, count, size, entry, private, post) &&
            data_at(&pmem->OSMemFreeList, void *, memImageFree(memPrivateImage(private))) *
            mem_create_head_field_frame(sg, entry, private)
        */
        /*@ Given private post */
        OSMemFreeList = (OS_MEM *)OSMemFreeList->OSMemFreeList;
        /*@ &OSMemFreeList == g_OSMemFreeList(sg) &&
            pmem == memory_control_addr(sg, memPrivateSlot(private)) &&
            mem_create_profile(sg) && UCOS2_state_inv(sg, entry) &&
            mem_create_reservation(sg, base, count, size, entry, private, post) &&
            mem_create_byte_access(mem_create_entry_resources(sg, entry, mode, base, count, size, caller_frame), output) &&
            data_at(&OSMemFreeList, OS_MEM *, memImageFree(memPrivateImage(private))) *
            data_at(&pmem->OSMemFreeList, void *, memImageFree(memPrivateImage(private))) *
            mem_create_head_field_frame(sg, entry, private) *
            mem_create_input_resources(mode, base, count, size) * caller_frame
            which implies pmem == memory_control_addr(sg, memPrivateSlot(private)) &&
            mem_create_reservation(sg, base, count, size, entry, private, post) &&
            UCOS2_state_inv(sg, replace_MemoryS(post, entry)) &&
            mem_create_byte_access(mem_create_detached_resources(sg, replace_MemoryS(post, entry),
              mem_create_selection(private), mode, base, count, size, caller_frame), output) &&
            UCOS2_inv(sg, replace_MemoryS(post, entry)) * memory_private_control_rep(sg, private) *
            mem_create_input_resources(mode, base, count, size) * caller_frame
        */
    }
    /*@ Assert exists (selected: MemCreateSelection) (checkpoint: UCOS2_Verify_State),
        addr == base && nblks == count && blksize == size && perr == output &&
        pmem == mem_create_selected_pointer(sg, selected) && mem_create_profile(sg) &&
        mem_create_acquire_facts(critical, sg, invocation, mode, base, count, size, before, entry, selected, checkpoint) &&
        mem_create_call_domain(critical, sg, invocation, mode, base, count, size, before) &&
        mem_create_output_rely(critical, sg, invocation, mode, base, count, size, output, caller_frame) &&
        mem_create_safe(critical, sg, invocation, base, count, size, output, before, X) &&
        mem_create_byte_access(mem_create_detached_resources(sg, checkpoint, selected, mode, base, count, size, caller_frame), output) &&
        mbox_accept_cpu_restore_pre(platform, critical, sg, invocation, origin, mask, cpu_sr, entry, checkpoint) *
        mem_create_selected_resources(sg, selected) * mem_create_input_resources(mode, base, count, size) * caller_frame *
        undef_data_at(&pblk, INT8U *) * undef_data_at(&plink, void **) *
        undef_data_at(&loops, INT32U) * undef_data_at(&i, INT32U)
    */
    /*@ Given selected checkpoint */
    OS_EXIT_CRITICAL();
    /*@ Given current */
    if (pmem == (OS_MEM *)0) {                        /* See if we have a memory partition             */
        /*@ pmem == 0 && pmem == mem_create_selected_pointer(sg, selected) && perr == output &&
            mem_create_acquire_facts(critical, sg, invocation, mode, base, count, size, before, entry, selected, checkpoint) &&
            critical_region_interval(critical, sg, invocation, checkpoint, current) &&
            mem_create_output_rely(critical, sg, invocation, mode, base, count, size, output, caller_frame) &&
            mem_create_byte_access(mem_create_detached_resources(sg, checkpoint, selected, mode, base, count, size, caller_frame), output) &&
            mutex_query_closed(platform, critical, sg, invocation, origin, mask, current) *
            mem_create_selected_resources(sg, selected) * mem_create_input_resources(mode, base, count, size) * caller_frame
            which implies pmem == 0 && perr == output &&
            mem_create_kernel_program(critical, sg, invocation, base, count, size, before, mem_create_outcome(0, 90), current) &&
            interrupt_platform_running(platform, invocation, origin, mask) *
            undef_data_at(perr, unsigned char) *
            mem_create_output_residual(mem_create_return_resources(sg, mode, base, count, size, 0, current, caller_frame), output)
        */
        *perr = OS_ERR_MEM_INVALID_PART;
        return ((OS_MEM *)0);
    }
    /*@ pmem != 0 && pmem == mem_create_selected_pointer(sg, selected) &&
        mem_create_profile(sg) &&
        mem_create_acquire_facts(critical, sg, invocation, mode, base, count, size, before, entry, selected, checkpoint) &&
        critical_region_interval(critical, sg, invocation, checkpoint, current) &&
        mem_create_call_domain(critical, sg, invocation, mode, base, count, size, before) &&
        mem_create_output_rely(critical, sg, invocation, mode, base, count, size, output, caller_frame) &&
        mem_create_byte_access(mem_create_detached_resources(sg, checkpoint, selected, mode, base, count, size, caller_frame), output) &&
        mem_create_safe(critical, sg, invocation, base, count, size, output, before, X) &&
        mutex_query_closed(platform, critical, sg, invocation, origin, mask, current) *
        mem_create_selected_resources(sg, selected) * mem_create_input_resources(mode, base, count, size) * caller_frame
        which implies exists (private: MemoryPrivatePartition),
        pmem == memory_control_addr(sg, memPrivateSlot(private)) && mode == MemCreateArena &&
        memPrivateBase(private) == base && memPrivateBlockCount(private) == count &&
        memPrivateBlockSize(private) == size && memory_private_initialization_valid(private) &&
        mem_create_loop_state(platform, critical, sg, invocation, origin, mask, base, count, size, output,
          before, current, private, 0, caller_frame, X)
    */
    /*@ Given private */
    plink = (void **)addr;                            /* Create linked list of free memory blocks      */
    pblk  = (INT8U *)addr;
    loops  = nblks - 1u;
    /*@ Inv addr == base && nblks == count && blksize == size && perr == output &&
        pmem == memory_control_addr(sg, memPrivateSlot(private)) && mode == MemCreateArena &&
        memPrivateBase(private) == base && memPrivateBlockCount(private) == count &&
        memPrivateBlockSize(private) == size && memory_private_initialization_valid(private) &&
        loops == count - 1 && 0 <= i && i <= count - 1 &&
        pblk == base + i * size && plink == base + i * size &&
        mem_create_loop_state(platform, critical, sg, invocation, origin, mask, base, count, size, output,
          before, current, private, i, caller_frame, X) * undef_data_at(&cpu_sr, OS_CPU_SR)
    */
    for (i = 0u; i < loops; i++) {
        pblk +=  blksize;                             /* Point to the FOLLOWING block                  */
        /*@ 0 <= i && i < count - 1 && plink == base + i * size &&
            pblk == base + (i + 1) * size &&
            memPrivateBase(private) == base && memPrivateBlockCount(private) == count &&
            memPrivateBlockSize(private) == size && memory_private_initialization_valid(private) &&
            mem_create_loop_state(platform, critical, sg, invocation, origin, mask, base, count, size, output,
              before, current, private, i, caller_frame, X)
            which implies 0 <= i && i < count - 1 && plink == base + i * size &&
            pblk == base + (i + 1) * size &&
            mem_create_profile(sg) &&
            mem_create_private_history(critical, sg, invocation, base, count, size, before, current, private) &&
            mem_create_safe(critical, sg, invocation, base, count, size, output, before, X) &&
            mem_create_byte_access(mem_create_cursor_resources(sg, current, private, i + 1, caller_frame), output) &&
            interrupt_platform_running(platform, invocation, origin, mask) *
            undef_data_at(plink, void *) * mem_create_loop_resources(sg, current, private, i, caller_frame)
        */
       *plink = (void  *)pblk;                        /* Save pointer to NEXT block in CURRENT block   */
        /*@ plink == base + i * size && pblk == base + (i + 1) * size &&
            memPrivateBase(private) == base && memPrivateBlockCount(private) == count &&
            memPrivateBlockSize(private) == size && memory_private_initialization_valid(private) &&
            0 <= i && i < count - 1 &&
            data_at(plink, void *, pblk) * mem_create_loop_resources(sg, current, private, i, caller_frame)
            which implies plink == base + i * size && pblk == base + (i + 1) * size &&
            mem_create_cursor_resources(sg, current, private, i + 1, caller_frame)
        */
        plink = (void **)pblk;                        /* Position to  NEXT      block                  */
    }
    /*@ loops == count - 1 && i >= loops && i <= count - 1 && plink == base + i * size &&
        memPrivateBase(private) == base && memPrivateBlockCount(private) == count &&
        memPrivateBlockSize(private) == size && memory_private_initialization_valid(private) &&
        mem_create_loop_state(platform, critical, sg, invocation, origin, mask, base, count, size, output,
          before, current, private, i, caller_frame, X)
        which implies i == count - 1 && loops == count - 1 && plink == base + (count - 1) * size &&
        mem_create_profile(sg) &&
        mem_create_private_history(critical, sg, invocation, base, count, size, before, current, private) &&
        mem_create_safe(critical, sg, invocation, base, count, size, output, before, X) &&
        mem_create_byte_access(mem_create_cursor_resources(sg, current, private, count, caller_frame), output) &&
        interrupt_platform_running(platform, invocation, origin, mask) *
        undef_data_at(plink, void *) * mem_create_loop_resources(sg, current, private, count - 1, caller_frame)
    */
    *plink              = (void *)0;                  /* Last memory block points to NULL              */
    /*@ pmem == memory_control_addr(sg, memPrivateSlot(private)) &&
        plink == base + (count - 1) * size &&
        memPrivateBase(private) == base && memPrivateBlockCount(private) == count &&
        memPrivateBlockSize(private) == size && memory_private_initialization_valid(private) &&
        mem_create_profile(sg) &&
        mem_create_byte_access(mem_create_cursor_resources(sg, current, private, count, caller_frame), output) &&
        data_at(plink, void *, 0) * mem_create_loop_resources(sg, current, private, count - 1, caller_frame)
        which implies pmem == memory_control_addr(sg, memPrivateSlot(private)) &&
        plink == base + (count - 1) * size &&
        mem_create_byte_access(mem_create_initialized_resources(sg, current, private, caller_frame), output) &&
        data_at(&pmem->OSMemAddr, void *, memImageBase(memPrivateImage(private))) *
        data_at(&pmem->OSMemFreeList, void *, memImageFree(memPrivateImage(private))) *
        data_at(&pmem->OSMemNFree, unsigned int, memImageNFree(memPrivateImage(private))) *
        data_at(&pmem->OSMemNBlks, unsigned int, memImageCount(memPrivateImage(private))) *
        data_at(&pmem->OSMemBlkSize, unsigned int, memImageSize(memPrivateImage(private))) *
        data_at(&pmem->OSMemName, INT8U *, memImageName(memPrivateImage(private))) *
        mem_create_control_write_frame(sg, current, private, caller_frame)
    */
    pmem->OSMemAddr     = addr;                       /* Store start address of memory partition       */
    pmem->OSMemFreeList = addr;                       /* Initialize pointer to pool of free blocks     */
    pmem->OSMemNFree    = nblks;                      /* Store number of free blocks in MCB            */
    pmem->OSMemNBlks    = nblks;
    pmem->OSMemBlkSize  = blksize;                    /* Store block size of each memory blocks        */

    OS_TRACE_MEM_CREATE(pmem);

    /*@ pmem == memory_control_addr(sg, memPrivateSlot(private)) && perr == output &&
        addr == base && nblks == count && blksize == size && mode == MemCreateArena &&
        memPrivateBase(private) == base && memPrivateBlockCount(private) == count &&
        memPrivateBlockSize(private) == size && memory_private_initialization_valid(private) &&
        mem_create_profile(sg) &&
        mem_create_private_history(critical, sg, invocation, base, count, size, before, current, private) &&
        mem_create_byte_access(mem_create_initialized_resources(sg, current, private, caller_frame), output) &&
        data_at(&pmem->OSMemAddr, void *, base) * data_at(&pmem->OSMemFreeList, void *, base) *
        data_at(&pmem->OSMemNFree, unsigned int, count) * data_at(&pmem->OSMemNBlks, unsigned int, count) *
        data_at(&pmem->OSMemBlkSize, unsigned int, size) *
        data_at(&pmem->OSMemName, INT8U *, memImageName(memPrivateImage(private))) *
        mem_create_control_write_frame(sg, current, private, caller_frame)
        which implies pmem == memory_control_addr(sg, memPrivateSlot(private)) && perr == output &&
        addr == base && nblks == count && blksize == size &&
        mem_create_kernel_program(critical, sg, invocation, base, count, size, before,
          mem_create_outcome(pmem, 0), mem_create_publish_state(current, private)) &&
        undef_data_at(perr, unsigned char) *
        mem_create_output_residual(mem_create_return_resources(sg, mode, base, count, size,
          pmem, mem_create_publish_state(current, private), caller_frame), output)
    */
    *perr               = OS_ERR_NONE;
    return (pmem);
}
