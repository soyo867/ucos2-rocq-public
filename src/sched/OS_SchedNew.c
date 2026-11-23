/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

static  void  OS_SchedNew (void)
/*@ With (sg : StableGlobVars) (group high : Z) (rows : list Z)
         (frame : Assertion)
    Require
      sched_new_global_addresses(sg, OSUnMapTbl, &OSRdyGrp,
                                OSRdyTbl, &OSPrioHighRdy) &&
      sched_new_rep(sg, group, rows, high) * frame
    Ensure
      sched_new_global_addresses(sg, OSUnMapTbl, &OSRdyGrp,
                                OSRdyTbl, &OSPrioHighRdy) &&
      sched_new_rep(sg, group, rows, sched_new_priority(group, rows)) * frame
*/
{
#if OS_LOWEST_PRIO <= 63u                        /* See if we support up to 64 tasks                   */
    INT8U   y;


    
/*@
      sched_new_global_addresses(sg, OSUnMapTbl, &OSRdyGrp,
                                OSRdyTbl, &OSPrioHighRdy) &&
      sched_new_rep(sg, group, rows, high)
      which implies
      sched_new_global_addresses(sg, OSUnMapTbl, &OSRdyGrp,
                                OSRdyTbl, &OSPrioHighRdy) &&
      0 <= group && group < 256 &&
      0 <= unmap_value(group) && unmap_value(group) < 8 &&
      data_at(&OSRdyGrp, unsigned char, group) *
      UCharArray::full(OSRdyTbl, 8, rows) *
      UCharArray::full(OSUnMapTbl, 256, unmap_table) *
      data_at(&OSPrioHighRdy, unsigned char, high)
    */
y             = OSUnMapTbl[OSRdyGrp];
    
/*@ Assert
      sched_new_global_addresses(sg, OSUnMapTbl, &OSRdyGrp,
                                OSRdyTbl, &OSPrioHighRdy) &&
      y == unmap_value(group) && 0 <= y && y < 8 &&
      0 <= Znth(y, rows, 0) && Znth(y, rows, 0) < 256 &&
      0 <= unmap_value(Znth(y, rows, 0)) &&
      unmap_value(Znth(y, rows, 0)) < 8 &&
      data_at(&OSRdyGrp, unsigned char, group) *
      UCharArray::full(OSRdyTbl, 8, rows) *
      UCharArray::full(OSUnMapTbl, 256, unmap_table) *
      data_at(&OSPrioHighRdy, unsigned char, high) * frame
    */
OSPrioHighRdy = (INT8U)((y << 3u) + OSUnMapTbl[OSRdyTbl[y]]);
#else                                            /* We support up to 256 tasks                         */
    INT8U     y;
    OS_PRIO  *ptbl;


    if ((OSRdyGrp & 0xFFu) != 0u) {
        y = OSUnMapTbl[OSRdyGrp & 0xFFu];
    } else {
        y = OSUnMapTbl[(OS_PRIO)(OSRdyGrp >> 8u) & 0xFFu] + 8u;
    }
    ptbl = &OSRdyTbl[y];
    if ((*ptbl & 0xFFu) != 0u) {
        OSPrioHighRdy = (INT8U)((y << 4u) + OSUnMapTbl[(*ptbl & 0xFFu)]);
    } else {
        OSPrioHighRdy = (INT8U)((y << 4u) + OSUnMapTbl[(OS_PRIO)(*ptbl >> 8u) & 0xFFu] + 8u);
    }
#endif
}
