/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OS_FlagInit (void)
/*@ With (sg : StableGlobVars) (LitMap : String -> Z) (frame : Assertion)
    Require
      flag_init_profile(sg) &&
      flag_init_global_addresses(sg, OSFlagTbl, &OSFlagFreeList) &&
      flag_init_layout(sg) && sizeof(struct os_flag_grp[5]) == 80 &&
      flag_init_pre(sg) * GlobalStrings(LitMap) * frame
    Ensure
      flag_init_profile(sg) &&
      flag_init_global_addresses(sg, OSFlagTbl, &OSFlagFreeList) &&
      flag_init_layout(sg) && sizeof(struct os_flag_grp[5]) == 80 &&
      flag_init_post(sg, LitMap("?")) * GlobalStrings(LitMap) * frame
*/
{
#if OS_MAX_FLAGS == 1u
    OSFlagFreeList                 = (OS_FLAG_GRP *)&OSFlagTbl[0];  /* Only ONE event flag group!      */
    OSFlagFreeList->OSFlagType     = OS_EVENT_TYPE_UNUSED;
    OSFlagFreeList->OSFlagWaitList = (void *)0;
    OSFlagFreeList->OSFlagFlags    = (OS_FLAGS)0;
#if OS_FLAG_NAME_EN > 0u
    OSFlagFreeList->OSFlagName     = (INT8U *)"?";
#endif
#endif

#if OS_MAX_FLAGS >= 2u
    INT16U        ix;
    INT16U        ix_next;
    OS_FLAG_GRP  *pgrp1;
    OS_FLAG_GRP  *pgrp2;



/*@
          flag_init_profile(sg) &&
          flag_init_global_addresses(sg, OSFlagTbl, &OSFlagFreeList) &&
          flag_init_layout(sg) && sizeof(struct os_flag_grp[5]) == 80 &&
          flag_init_pre(sg)
        which implies
          flag_init_profile(sg) &&
          flag_init_global_addresses(sg, OSFlagTbl, &OSFlagFreeList) &&
          flag_init_layout(sg) && sizeof(struct os_flag_grp[5]) == 80 &&
          0 <= pointer_offset(OSFlagTbl, 0, OS_FLAG_GRP) &&
          pointer_offset(pointer_offset(OSFlagTbl, 0, OS_FLAG_GRP), sizeof(struct os_flag_grp[5]), INT8U) <= 4294967295 &&
          mem_clr_pre(pointer_offset(OSFlagTbl, 0, OS_FLAG_GRP), sizeof(struct os_flag_grp[5])) *
          undef_data_at(&OSFlagFreeList, OS_FLAG_GRP *)
    */
OS_MemClr((INT8U *)&OSFlagTbl[0], sizeof(OSFlagTbl));           /* Clear the flag group table      */

/*@
          flag_init_profile(sg) &&
          flag_init_global_addresses(sg, OSFlagTbl, &OSFlagFreeList) &&
          flag_init_layout(sg) && sizeof(struct os_flag_grp[5]) == 80 &&
          mem_clr_post(pointer_offset(OSFlagTbl, 0, OS_FLAG_GRP), sizeof(struct os_flag_grp[5])) *
          undef_data_at(&OSFlagFreeList, OS_FLAG_GRP *)
        which implies
          flag_init_profile(sg) &&
          flag_init_global_addresses(sg, OSFlagTbl, &OSFlagFreeList) &&
          flag_init_layout(sg) && sizeof(struct os_flag_grp[5]) == 80 &&
          flag_init_loop_state(sg, LitMap("?"), 0)
    */

/*@ Inv Assert
          flag_init_profile(sg) &&
          flag_init_global_addresses(sg, OSFlagTbl, &OSFlagFreeList) &&
          flag_init_layout(sg) && sizeof(struct os_flag_grp[5]) == 80 &&
          0 <= ix && ix <= 4 &&
          flag_init_loop_state(sg, LitMap("?"), ix) * GlobalStrings(LitMap) * frame *
          undef_data_at(&ix_next, INT16U) *
          undef_data_at(&pgrp1, OS_FLAG_GRP *) * undef_data_at(&pgrp2, OS_FLAG_GRP *)
    */
for (ix = 0u; ix < (OS_MAX_FLAGS - 1u); ix++) {                 /* Init. list of free EVENT FLAGS  */
        ix_next = ix + 1u;
        pgrp1 = &OSFlagTbl[ix];
        pgrp2 = &OSFlagTbl[ix_next];

/*@
              flag_init_profile(sg) &&
              flag_init_global_addresses(sg, OSFlagTbl, &OSFlagFreeList) &&
              flag_init_layout(sg) && sizeof(struct os_flag_grp[5]) == 80 &&
              0 <= ix && ix < 4 && ix_next == ix + 1 &&
              pgrp1 == pointer_offset(OSFlagTbl, ix, OS_FLAG_GRP) &&
              pgrp2 == pointer_offset(OSFlagTbl, ix_next, OS_FLAG_GRP) &&
              flag_init_loop_state(sg, LitMap("?"), ix)
            which implies
              flag_init_profile(sg) &&
              flag_init_global_addresses(sg, OSFlagTbl, &OSFlagFreeList) &&
              flag_init_layout(sg) && sizeof(struct os_flag_grp[5]) == 80 &&
              0 <= ix && ix < 4 && ix_next == ix + 1 &&
              pgrp1 == pointer_offset(OSFlagTbl, ix, OS_FLAG_GRP) &&
              pgrp2 == pointer_offset(OSFlagTbl, ix_next, OS_FLAG_GRP) &&
              data_at(&pgrp1->OSFlagType, INT8U, 0) *
              data_at(&pgrp1->OSFlagWaitList, void *, 0) *
              data_at(&pgrp1->OSFlagName, INT8U *, 0) *
              flag_init_loop_residual(sg, LitMap("?"), ix)
        */
pgrp1->OSFlagType     = OS_EVENT_TYPE_UNUSED;
        pgrp1->OSFlagWaitList = (void *)pgrp2;
#if OS_FLAG_NAME_EN > 0u
        pgrp1->OSFlagName     = (INT8U *)(void *)"?";               /* Unknown name                    */
#endif

/*@ Assert
              flag_init_profile(sg) &&
              flag_init_global_addresses(sg, OSFlagTbl, &OSFlagFreeList) &&
              flag_init_layout(sg) && sizeof(struct os_flag_grp[5]) == 80 &&
              0 <= ix && ix < 4 &&
              flag_init_loop_state(sg, LitMap("?"), ix + 1) * GlobalStrings(LitMap) * frame *
              undef_data_at(&ix_next, INT16U) *
              undef_data_at(&pgrp1, OS_FLAG_GRP *) * undef_data_at(&pgrp2, OS_FLAG_GRP *)
        */
}
    pgrp1                 = &OSFlagTbl[ix];

/*@
          flag_init_profile(sg) &&
          flag_init_global_addresses(sg, OSFlagTbl, &OSFlagFreeList) &&
          flag_init_layout(sg) && sizeof(struct os_flag_grp[5]) == 80 &&
          4 <= ix && ix <= 4 && pgrp1 == pointer_offset(OSFlagTbl, ix, OS_FLAG_GRP) &&
          flag_init_loop_state(sg, LitMap("?"), ix)
        which implies
          flag_init_profile(sg) &&
          flag_init_global_addresses(sg, OSFlagTbl, &OSFlagFreeList) &&
          flag_init_layout(sg) && sizeof(struct os_flag_grp[5]) == 80 &&
          ix == 4 && pgrp1 == pointer_offset(OSFlagTbl, ix, OS_FLAG_GRP) &&
          data_at(&pgrp1->OSFlagType, INT8U, 0) *
          data_at(&pgrp1->OSFlagWaitList, void *, 0) *
          data_at(&pgrp1->OSFlagName, INT8U *, 0) *
          flag_init_loop_residual(sg, LitMap("?"), ix)
    */
pgrp1->OSFlagType     = OS_EVENT_TYPE_UNUSED;
    pgrp1->OSFlagWaitList = (void *)0;
#if OS_FLAG_NAME_EN > 0u
    pgrp1->OSFlagName     = (INT8U *)(void *)"?";                   /* Unknown name                    */
#endif

/*@ Assert
          flag_init_profile(sg) &&
          flag_init_global_addresses(sg, OSFlagTbl, &OSFlagFreeList) &&
          flag_init_layout(sg) && sizeof(struct os_flag_grp[5]) == 80 &&
          flag_init_loop_state(sg, LitMap("?"), 5) * GlobalStrings(LitMap) * frame *
          undef_data_at(&ix, INT16U) * undef_data_at(&ix_next, INT16U) *
          undef_data_at(&pgrp1, OS_FLAG_GRP *) * undef_data_at(&pgrp2, OS_FLAG_GRP *)
    */

/*@
          flag_init_profile(sg) &&
          flag_init_global_addresses(sg, OSFlagTbl, &OSFlagFreeList) &&
          flag_init_layout(sg) && sizeof(struct os_flag_grp[5]) == 80 &&
          flag_init_loop_state(sg, LitMap("?"), 5)
        which implies
          flag_init_profile(sg) &&
          flag_init_global_addresses(sg, OSFlagTbl, &OSFlagFreeList) &&
          flag_init_layout(sg) && sizeof(struct os_flag_grp[5]) == 80 &&
          flag_init_prefix(sg, LitMap("?"), 5) * undef_data_at(&OSFlagFreeList, OS_FLAG_GRP *)
    */
OSFlagFreeList        = &OSFlagTbl[0];
#endif
}
