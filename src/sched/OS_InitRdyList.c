/*
 * uC/OS-II V2.93.01, Source/os_core.c: OS_InitRdyList.
 * Bound upstream checkout: /tmp/ucos2-official-audit-20260802/Source/
 * Selected ILP32 profile: OS_LOWEST_PRIO = 63, eight UChar ready rows.
 * Function body and write order are retained from upstream. The standalone
 * declarations expose only its actual globals; OS_TCB stays opaque because
 * this function writes null pointers and never dereferences a TCB.
 * See config/core-initializers-v2.93.01.md for scope and composition.
 */

#include "verification_stdlib.h"

/*@ Import Coq Require Import Ucos2Verify.VC.code.sched.spec.init_rdy_list_spec */
/*@ Import Coq Import Ucos2Verify.lib.ucos2_rules_lib.UCOS2_C_Rules */
/*@ Extern Coq
      (init_rdy_list_pre : Z -> Z -> Z -> Z -> Z -> Z -> Assertion)
      (init_rdy_list_post : Z -> Z -> Z -> Z -> Z -> Z -> Assertion)
      (init_rdy_list_table_prefix : Z -> Z -> Assertion)
      (init_rdy_list_row_frame : Z -> Z -> Assertion)
*/

typedef unsigned char INT8U;
typedef unsigned char OS_PRIO;

#define OS_LOWEST_PRIO 63u
#define OS_RDY_TBL_SIZE ((OS_LOWEST_PRIO) / 8u + 1u)

struct os_tcb;
typedef struct os_tcb OS_TCB;

extern OS_PRIO OSRdyGrp;
extern OS_PRIO OSRdyTbl[OS_RDY_TBL_SIZE];
extern INT8U OSPrioCur;
extern INT8U OSPrioHighRdy;
extern OS_TCB *OSTCBHighRdy;
extern OS_TCB *OSTCBCur;

static void OS_InitRdyList (void)
/*@ Require init_rdy_list_pre(&OSRdyGrp, &OSRdyTbl,
      &OSPrioCur, &OSPrioHighRdy, &OSTCBHighRdy, &OSTCBCur)
    Ensure init_rdy_list_post(&OSRdyGrp, &OSRdyTbl,
      &OSPrioCur, &OSPrioHighRdy, &OSTCBHighRdy, &OSTCBCur)
*/
{
    INT8U i;

    /*@ init_rdy_list_pre(&OSRdyGrp, &OSRdyTbl,
          &OSPrioCur, &OSPrioHighRdy, &OSTCBHighRdy, &OSTCBCur)
        which implies
          undef_data_at(&OSRdyGrp, unsigned char) *
          init_rdy_list_table_prefix(&OSRdyTbl, 0) *
          undef_data_at(&OSPrioCur, unsigned char) *
          undef_data_at(&OSPrioHighRdy, unsigned char) *
          undef_data_at(&OSTCBHighRdy, OS_TCB *) *
          undef_data_at(&OSTCBCur, OS_TCB *)
    */
    OSRdyGrp = 0u;
    /*@ Inv Assert
          0 <= i && i <= 8 &&
          data_at(&OSRdyGrp, unsigned char, 0) *
          init_rdy_list_table_prefix(&OSRdyTbl, i) *
          undef_data_at(&OSPrioCur, unsigned char) *
          undef_data_at(&OSPrioHighRdy, unsigned char) *
          undef_data_at(&OSTCBHighRdy, OS_TCB *) *
          undef_data_at(&OSTCBCur, OS_TCB *)
    */
    for (i = 0u; i < OS_RDY_TBL_SIZE; i++) {
        /*@ 0 <= i && i < 8 &&
              init_rdy_list_table_prefix(&OSRdyTbl, i)
            which implies
              undef_data_at(pointer_offset(&OSRdyTbl, i, unsigned char), unsigned char) *
              init_rdy_list_row_frame(&OSRdyTbl, i)
        */
        OSRdyTbl[i] = 0u;
        /*@ 0 <= i && i < 8 &&
              data_at(pointer_offset(&OSRdyTbl, i, unsigned char), unsigned char, 0) *
              init_rdy_list_row_frame(&OSRdyTbl, i)
            which implies
              init_rdy_list_table_prefix(&OSRdyTbl, i + 1)
        */
    }

    OSPrioCur = 0u;
    OSPrioHighRdy = 0u;

    OSTCBHighRdy = (OS_TCB *)0;
    OSTCBCur = (OS_TCB *)0;
}
