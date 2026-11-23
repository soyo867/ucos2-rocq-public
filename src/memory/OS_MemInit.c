/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OS_MemInit (void)
/*@ With (sg : StableGlobVars) (LitMap : String -> Z) (frame : Assertion)
    Require
      mem_init_profile(sg) &&
      mem_init_global_addresses(sg, OSMemTbl, &OSMemFreeList) &&
      mem_init_layout(sg) && sizeof(struct os_mem[5]) == 120 &&
      mem_init_pre(sg) * GlobalStrings(LitMap) * frame
    Ensure
      mem_init_profile(sg) &&
      mem_init_global_addresses(sg, OSMemTbl, &OSMemFreeList) &&
      mem_init_layout(sg) && sizeof(struct os_mem[5]) == 120 &&
      mem_init_post(sg, LitMap("?")) * GlobalStrings(LitMap) * frame
*/
{
#if OS_MAX_MEM_PART == 1u
    OS_MemClr((INT8U *)&OSMemTbl[0], sizeof(OSMemTbl));   /* Clear the memory partition table          */
    OSMemFreeList               = (OS_MEM *)&OSMemTbl[0]; /* Point to beginning of free list           */
#if OS_MEM_NAME_EN > 0u
    OSMemFreeList->OSMemName    = (INT8U *)"?";           /* Unknown name                              */
#endif
#endif

#if OS_MAX_MEM_PART >= 2u
    OS_MEM  *pmem;
    INT16U   i;


    /*@
          mem_init_profile(sg) &&
          mem_init_global_addresses(sg, OSMemTbl, &OSMemFreeList) &&
          mem_init_layout(sg) && sizeof(struct os_mem[5]) == 120 &&
          mem_init_pre(sg)
        which implies
          mem_init_profile(sg) &&
          mem_init_global_addresses(sg, OSMemTbl, &OSMemFreeList) &&
          mem_init_layout(sg) && sizeof(struct os_mem[5]) == 120 &&
          0 <= pointer_offset(OSMemTbl, 0, OS_MEM) &&
          pointer_offset(pointer_offset(OSMemTbl, 0, OS_MEM), sizeof(struct os_mem[5]), INT8U) <= 4294967295 &&
          mem_clr_pre(pointer_offset(OSMemTbl, 0, OS_MEM), sizeof(struct os_mem[5])) *
          undef_data_at(&OSMemFreeList, OS_MEM *)
    */
    OS_MemClr((INT8U *)&OSMemTbl[0], sizeof(OSMemTbl));   /* Clear the memory partition table          */
    /*@
          mem_init_profile(sg) &&
          mem_init_global_addresses(sg, OSMemTbl, &OSMemFreeList) &&
          mem_init_layout(sg) && sizeof(struct os_mem[5]) == 120 &&
          mem_clr_post(pointer_offset(OSMemTbl, 0, OS_MEM), sizeof(struct os_mem[5])) *
          undef_data_at(&OSMemFreeList, OS_MEM *)
        which implies
          mem_init_profile(sg) &&
          mem_init_global_addresses(sg, OSMemTbl, &OSMemFreeList) &&
          mem_init_layout(sg) && sizeof(struct os_mem[5]) == 120 &&
          mem_init_loop_state(sg, LitMap("?"), 0)
    */
    /*@ Inv Assert
          mem_init_profile(sg) &&
          mem_init_global_addresses(sg, OSMemTbl, &OSMemFreeList) &&
          mem_init_layout(sg) && sizeof(struct os_mem[5]) == 120 &&
          0 <= i && i <= 4 &&
          mem_init_loop_state(sg, LitMap("?"), i) * GlobalStrings(LitMap) * frame *
          undef_data_at(&pmem, OS_MEM *)
    */
    for (i = 0u; i < (OS_MAX_MEM_PART - 1u); i++) {       /* Init. list of free memory partitions      */
        pmem                = &OSMemTbl[i];               /* Point to memory control block (MCB)       */
        /*@
              mem_init_profile(sg) &&
              mem_init_global_addresses(sg, OSMemTbl, &OSMemFreeList) &&
              mem_init_layout(sg) && sizeof(struct os_mem[5]) == 120 &&
              0 <= i && i < 4 && pmem == pointer_offset(OSMemTbl, i, OS_MEM) &&
              mem_init_loop_state(sg, LitMap("?"), i)
            which implies
              mem_init_profile(sg) &&
              mem_init_global_addresses(sg, OSMemTbl, &OSMemFreeList) &&
              mem_init_layout(sg) && sizeof(struct os_mem[5]) == 120 &&
              0 <= i && i < 4 && pmem == pointer_offset(OSMemTbl, i, OS_MEM) &&
              data_at(&pmem->OSMemFreeList, void *, 0) *
              data_at(&pmem->OSMemName, INT8U *, 0) *
              mem_init_loop_residual(sg, LitMap("?"), i)
        */
        pmem->OSMemFreeList = (void *)&OSMemTbl[i + 1u];  /* Chain list of free partitions             */
#if OS_MEM_NAME_EN > 0u
        pmem->OSMemName  = (INT8U *)(void *)"?";
#endif
        /*@ Assert
              mem_init_profile(sg) &&
              mem_init_global_addresses(sg, OSMemTbl, &OSMemFreeList) &&
              mem_init_layout(sg) && sizeof(struct os_mem[5]) == 120 &&
              0 <= i && i < 4 &&
              mem_init_loop_state(sg, LitMap("?"), i + 1) * GlobalStrings(LitMap) * frame *
              undef_data_at(&pmem, OS_MEM *)
        */
    }
    pmem                = &OSMemTbl[i];
    /*@
          mem_init_profile(sg) &&
          mem_init_global_addresses(sg, OSMemTbl, &OSMemFreeList) &&
          mem_init_layout(sg) && sizeof(struct os_mem[5]) == 120 &&
          4 <= i && i <= 4 && pmem == pointer_offset(OSMemTbl, i, OS_MEM) &&
          mem_init_loop_state(sg, LitMap("?"), i)
        which implies
          mem_init_profile(sg) &&
          mem_init_global_addresses(sg, OSMemTbl, &OSMemFreeList) &&
          mem_init_layout(sg) && sizeof(struct os_mem[5]) == 120 &&
          i == 4 && pmem == pointer_offset(OSMemTbl, i, OS_MEM) &&
          data_at(&pmem->OSMemFreeList, void *, 0) *
          data_at(&pmem->OSMemName, INT8U *, 0) *
          mem_init_loop_residual(sg, LitMap("?"), i)
    */
    pmem->OSMemFreeList = (void *)0;                      /* Initialize last node                      */
#if OS_MEM_NAME_EN > 0u
    pmem->OSMemName = (INT8U *)(void *)"?";
#endif

    /*@ Assert
          mem_init_profile(sg) &&
          mem_init_global_addresses(sg, OSMemTbl, &OSMemFreeList) &&
          mem_init_layout(sg) && sizeof(struct os_mem[5]) == 120 &&
          mem_init_loop_state(sg, LitMap("?"), 5) * GlobalStrings(LitMap) * frame *
          undef_data_at(&i, INT16U) * undef_data_at(&pmem, OS_MEM *)
    */
    /*@
          mem_init_profile(sg) &&
          mem_init_global_addresses(sg, OSMemTbl, &OSMemFreeList) &&
          mem_init_layout(sg) && sizeof(struct os_mem[5]) == 120 &&
          mem_init_loop_state(sg, LitMap("?"), 5)
        which implies
          mem_init_profile(sg) &&
          mem_init_global_addresses(sg, OSMemTbl, &OSMemFreeList) &&
          mem_init_layout(sg) && sizeof(struct os_mem[5]) == 120 &&
          mem_init_prefix(sg, LitMap("?"), 5) * undef_data_at(&OSMemFreeList, OS_MEM *)
    */
    OSMemFreeList   = &OSMemTbl[0];                       /* Point to beginning of free list           */
#endif
}
