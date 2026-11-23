/*
 * Executable-source skeleton for the OS_QInit verification case.
 *
 * Upstream: https://github.com/weston-embedded/uC-OS2.git
 * Commit: bfc6120f20cb27a927a9fc5dd667f9e455495777
 * Version: V2.93.01
 * Source: Source/os_q.c
 * Source SHA-256: 246eb61cd70e44a793dcc6f2393bbaca49235a86b03a6e976d325b9f095e42aa
 * Function slice: Source/os_q.c lines 936-962
 * Function-slice SHA-256: 6243a8974806f6420d309ba7b49d7b334570c5f61d5951d18720f5086b275b91
 * Type/declaration source: Source/ucos_ii.h
 * Header SHA-256: be144099fce9f05f578fcd359f40a922ad17290b8bb553bfd83ff9bb99b7113e
 * Profile: uC-OS2_verify/config/queue-v2.93.01-first-round/profile.json
 *
 * The support declarations below form a standalone verification slice.  The
 * OS_QInit function text is retained in upstream source order.  Verification
 * annotations do not alter the executable token sequence.
 */

/*@ Extern Coq (StableGlobVars :: *) */
/*@ Extern Coq (valid_stable_glob_vars : StableGlobVars -> Prop) */
/*@ Extern Coq (os_q_table_addr : StableGlobVars -> Z -> Prop) */
/*@ Extern Coq (os_q_free_list_addr : StableGlobVars -> Z -> Prop) */
/*@ Extern Coq (queue_first_round_profile : StableGlobVars -> Prop) */
/*@ Extern Coq (queue_init_pre : StableGlobVars -> Assertion) */
/*@ Extern Coq (queue_init_post : StableGlobVars -> Assertion) */
/*@ Extern Coq (q_init_after_clear : StableGlobVars -> Assertion) */
/*@ Extern Coq (queue_table_layout_prop : StableGlobVars -> Z -> Prop) */
/*@ Extern Coq (q_init_loop_state : StableGlobVars -> Z -> Assertion) */
/*@ Extern Coq (q_init_loop_focus : StableGlobVars -> Z -> Assertion) */
/*@ Extern Coq (q_init_loop_residual : StableGlobVars -> Z -> Assertion) */
/*@ Extern Coq (q_init_link_committed : StableGlobVars -> Z -> Assertion) */
/*@ Extern Coq (q_init_before_last_link : StableGlobVars -> Assertion) */
/*@ Extern Coq (q_init_last_link_residual : StableGlobVars -> Assertion) */
/*@ Extern Coq (q_init_before_publish : StableGlobVars -> Assertion) */
/*@ Extern Coq (q_init_publish_residual : StableGlobVars -> Assertion) */
/*@ Extern Coq (OS_QInit_spec : StableGlobVars -> Assertion) */
/*@ Extern Coq
      (queue_control_block_layout_prop :
        StableGlobVars -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Local Open Scope Z_scope */
/*@ Import Coq Local Open Scope sac */
/*@ Import Coq Require Import Ucos2Verify.lib.stable_glob_vars */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_verify_state_def */
/*@ Import Coq Require Import Ucos2Verify.lib.event */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_rules_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.queue_core */
/*@ Import Coq Require Import Ucos2Verify.VC.code.queue.spec.q_init_spec */

typedef unsigned char  INT8U;
typedef unsigned short INT16U;

#define OS_MAX_QS 4u

typedef struct os_q {                       /* QUEUE CONTROL BLOCK                                     */
    struct os_q   *OSQPtr;                  /* Link to next queue control block in list of free blocks */
    void         **OSQStart;                /* Ptr to start of queue data                              */
    void         **OSQEnd;                  /* Ptr to end   of queue data                              */
    void         **OSQIn;                   /* Ptr to where next message will be inserted  in   the Q  */
    void         **OSQOut;                  /* Ptr to where next message will be extracted from the Q  */
    INT16U         OSQSize;                 /* Size of queue (maximum number of entries)               */
    INT16U         OSQEntries;              /* Current number of entries in the queue                  */
} OS_Q;

extern OS_Q  *OSQFreeList;
extern OS_Q   OSQTbl[OS_MAX_QS];

void OS_MemClr(INT8U *pdest, INT16U size)
/*@ With (sg : StableGlobVars)
    Require
      valid_stable_glob_vars(sg) &&
      queue_first_round_profile(sg) &&
      os_q_table_addr(sg, pdest) &&
      queue_table_layout_prop(sg, pdest) &&
      size == 96 &&
      queue_init_pre(sg)
    Ensure
      valid_stable_glob_vars(sg) &&
      queue_first_round_profile(sg) &&
      queue_table_layout_prop(sg, pdest) &&
      q_init_after_clear(sg)
*/ ;

void  OS_QInit (void)
/*@ With (sg : StableGlobVars)
    Require
      valid_stable_glob_vars(sg) &&
      queue_first_round_profile(sg) &&
      os_q_table_addr(sg, OSQTbl) &&
      os_q_free_list_addr(sg, &OSQFreeList) &&
      queue_table_layout_prop(sg, OSQTbl) &&
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



    OS_MemClr((INT8U *)&OSQTbl[0], sizeof(OSQTbl))   /* Clear the queue table                          */
      /*@ where sg = sg */;
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
