/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OS_QInit (void)
/*@ With (sg : StableGlobVars)
    Require
      valid_stable_glob_vars(sg) &&
      queue_first_round_profile(sg) &&
      os_q_table_addr(sg, OSQTbl) &&
      os_q_free_list_addr(sg, &OSQFreeList) &&
      queue_table_layout_prop(sg, OSQTbl) &&
      q_init_zynq7_reference_layout(sg) &&
      queue_init_pre(sg)
    Ensure
      valid_stable_glob_vars(sg) &&
      queue_first_round_profile(sg) &&
      os_q_table_addr(sg, OSQTbl) &&
      os_q_free_list_addr(sg, &OSQFreeList) &&
      queue_table_layout_prop(sg, OSQTbl) &&
      OS_QInit_spec(sg)
*/
{
#if OS_MAX_QS == 1u
    OSQFreeList         = &OSQTbl[0];                /* Only ONE queue!                                */
    OSQFreeList->OSQPtr = (OS_Q *)0;
#endif

#if OS_MAX_QS >= 2u
    INT16U   ix;
    INT16U   ix_next;
    OS_Q    *pq1;
    OS_Q    *pq2;



    
/*@ queue_first_round_profile(sg) && os_q_table_addr(sg, OSQTbl) && queue_init_pre(sg)
        which implies
        g_OSQTbl(sg) % 4 == 0 &&
        0 <= g_OSQTbl(sg) && g_OSQTbl(sg) + 96 <= 4294967296 &&
        mem_clr_pre(pointer_offset(OSQTbl, 0, struct os_q), sizeof(struct os_q[4])) *
        undef_data_at(g_OSQFreeList(sg), OS_Q *)
    */
OS_MemClr((INT8U *)&OSQTbl[0], sizeof(OSQTbl));  /* Clear the queue table                          */
    
/*@ queue_first_round_profile(sg) && os_q_table_addr(sg, OSQTbl) &&
        g_OSQTbl(sg) % 4 == 0 &&
        0 <= g_OSQTbl(sg) && g_OSQTbl(sg) + 96 <= 4294967296 &&
        mem_clr_post(pointer_offset(OSQTbl, 0, struct os_q), sizeof(struct os_q[4])) *
        undef_data_at(g_OSQFreeList(sg), OS_Q *)
        which implies q_init_after_clear(sg)
    */

/*@ Inv Assert
          valid_stable_glob_vars(sg) &&
          queue_first_round_profile(sg) &&
          os_q_table_addr(sg, OSQTbl) &&
          os_q_free_list_addr(sg, &OSQFreeList) &&
          queue_table_layout_prop(sg, OSQTbl) &&
          q_init_loop_state(sg, ix) *
          undef_data_at(&ix_next, unsigned short) *
          undef_data_at(&pq1, OS_Q *) *
          undef_data_at(&pq2, OS_Q *)
    */
for (ix = 0u; ix < (OS_MAX_QS - 1u); ix++) {     /* Init. list of free QUEUE control blocks        */
        ix_next = ix + 1u;
        pq1 = &OSQTbl[ix];
        pq2 = &OSQTbl[ix_next];
        
/*@
              valid_stable_glob_vars(sg) &&
              queue_first_round_profile(sg) &&
              os_q_table_addr(sg, OSQTbl) &&
              os_q_free_list_addr(sg, &OSQFreeList) &&
              queue_table_layout_prop(sg, OSQTbl) &&
              ix_next == ix + 1 &&
              pq1 == pointer_offset(OSQTbl, ix, OS_Q) &&
              pq2 == pointer_offset(OSQTbl, ix_next, OS_Q) &&
              q_init_loop_state(sg, ix)
            which implies
              valid_stable_glob_vars(sg) &&
              queue_first_round_profile(sg) &&
              os_q_table_addr(sg, OSQTbl) &&
              os_q_free_list_addr(sg, &OSQFreeList) &&
              queue_table_layout_prop(sg, OSQTbl) &&
              ix_next == ix + 1 &&
              pq1 == pointer_offset(OSQTbl, ix, OS_Q) &&
              pq2 == pointer_offset(OSQTbl, ix_next, OS_Q) &&
              queue_control_block_layout_prop(
                sg, ix,
                &(pq1->OSQPtr), &(pq1->OSQStart), &(pq1->OSQEnd),
                &(pq1->OSQIn), &(pq1->OSQOut),
                &(pq1->OSQSize), &(pq1->OSQEntries)) &&
              data_at(&(pq1->OSQPtr), OS_Q *, 0) *
              q_init_loop_residual(sg, ix)
        */
pq1->OSQPtr = pq2;
    
/*@ Assert
              valid_stable_glob_vars(sg) &&
              queue_first_round_profile(sg) &&
              os_q_table_addr(sg, OSQTbl) &&
              os_q_free_list_addr(sg, &OSQFreeList) &&
              queue_table_layout_prop(sg, OSQTbl) &&
              q_init_link_committed(sg, ix) *
              undef_data_at(&ix_next, unsigned short) *
              undef_data_at(&pq1, OS_Q *) *
              undef_data_at(&pq2, OS_Q *)
        */
}
    pq1         = &OSQTbl[ix];
    
/*@
          valid_stable_glob_vars(sg) &&
          queue_first_round_profile(sg) &&
          os_q_table_addr(sg, OSQTbl) &&
          os_q_free_list_addr(sg, &OSQFreeList) &&
          queue_table_layout_prop(sg, OSQTbl) &&
          ix >= 3 &&
          data_at(&pq1, OS_Q *, pointer_offset(OSQTbl, ix, OS_Q)) *
          q_init_loop_state(sg, ix) *
          undef_data_at(&ix_next, unsigned short) *
          undef_data_at(&pq2, OS_Q *)
        which implies
          valid_stable_glob_vars(sg) &&
          queue_first_round_profile(sg) &&
          os_q_table_addr(sg, OSQTbl) &&
          os_q_free_list_addr(sg, &OSQFreeList) &&
          queue_table_layout_prop(sg, OSQTbl) &&
          ix == 3 &&
          pq1 == pointer_offset(OSQTbl, ix, OS_Q) &&
          queue_control_block_layout_prop(
            sg, ix,
            &(pq1->OSQPtr), &(pq1->OSQStart), &(pq1->OSQEnd),
            &(pq1->OSQIn), &(pq1->OSQOut),
            &(pq1->OSQSize), &(pq1->OSQEntries)) &&
          data_at(&(pq1->OSQPtr), OS_Q *, 0) *
          q_init_last_link_residual(sg) *
          undef_data_at(&ix_next, unsigned short) *
          undef_data_at(&pq2, OS_Q *)
    */
pq1->OSQPtr = (OS_Q *)0;
    
/*@ Assert
          valid_stable_glob_vars(sg) &&
          queue_first_round_profile(sg) &&
          os_q_table_addr(sg, OSQTbl) &&
          os_q_free_list_addr(sg, &OSQFreeList) &&
          queue_table_layout_prop(sg, OSQTbl) &&
          ix == 3 &&
          pq1 == pointer_offset(OSQTbl, 3, OS_Q) &&
          q_init_before_publish(sg) *
          undef_data_at(&ix_next, unsigned short) *
          undef_data_at(&pq2, OS_Q *)
    */

/*@
          valid_stable_glob_vars(sg) &&
          queue_first_round_profile(sg) &&
          os_q_table_addr(sg, OSQTbl) &&
          os_q_free_list_addr(sg, &OSQFreeList) &&
          queue_table_layout_prop(sg, OSQTbl) &&
          ix == 3 &&
          pq1 == pointer_offset(OSQTbl, 3, OS_Q) &&
          q_init_before_publish(sg) *
          undef_data_at(&ix_next, unsigned short) *
          undef_data_at(&pq2, OS_Q *)
        which implies
          valid_stable_glob_vars(sg) &&
          queue_first_round_profile(sg) &&
          os_q_table_addr(sg, OSQTbl) &&
          os_q_free_list_addr(sg, &OSQFreeList) &&
          queue_table_layout_prop(sg, OSQTbl) &&
          ix == 3 &&
          pq1 == pointer_offset(OSQTbl, 3, OS_Q) &&
          undef_data_at(&OSQFreeList, OS_Q *) *
          q_init_publish_residual(sg) *
          undef_data_at(&ix_next, unsigned short) *
          undef_data_at(&pq2, OS_Q *)
    */
OSQFreeList = &OSQTbl[0];
#endif
}
