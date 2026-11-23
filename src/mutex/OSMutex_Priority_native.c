/* Native annotation carrier for the checked raw priority helpers.
 * Actual input uses original headers and priority_native_source overlays.
 * No legacy InsideCritical token belongs to these raw footprints.
 */
#include "ucos_ii.h"

#include "verification_stdlib.h"
#include "verification_list.h"

/*@ Import Coq Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec */
/*@ Import Coq Import UCOS2_C_Rules */
/*@ Import Coq Import ucos2_rules_lib */
/*@ Import Coq Local Open Scope sac_scope */
/*@ Extern Coq (TCBCommonImage :: *) (TCBField :: *) */
/*@ Extern Coq (TCBPrio : TCBField)
               (tcb64_storage_rep : Z -> TCBCommonImage -> Assertion)
               (tcb64_storage_without : Z -> TCBField -> TCBCommonImage -> Assertion)
               (mutex_priority_fallback : TCBCommonImage -> Z -> Prop)
               (mutex_priority_tcb_rest : Z -> TCBCommonImage -> Assertion)
               (mutex_priority_image_fields : TCBCommonImage -> Z -> Z -> Z -> Z -> Z -> Prop)
               (mutex_priority_image : TCBCommonImage -> Z -> TCBCommonImage)
               (mutex_priority_no_match : list Z -> Z -> Z -> Prop)
               (mutex_base_priority_prefix : list Z -> Z -> Z -> Z -> Z -> Prop)
               (mutex_base_priority_result : list Z -> Z -> Z -> Z -> Prop)
               (mutex_effective_priority_result : list Z -> Z -> Z -> Z -> Prop)
               (mutex_priority_was_ready : list Z -> Z -> Z -> bool)
               (mutex_priority_removed_rows : list Z -> Z -> Z -> list Z)
               (mutex_priority_removed_group : list Z -> Z -> Z -> Z -> Z -> Z)
               (mutex_priority_rows : list Z -> Z -> Z -> Z -> list Z)
               (mutex_priority_group : list Z -> Z -> Z -> Z -> Z -> Z -> Z)
               (mutex_priority_current : Z -> Z -> Z -> Z -> Z)
               (encode_bool : bool -> Z)
               (tcb_x_of_prio : Z -> Z) (tcb_y_of_prio : Z -> Z)
               (tcb_bit_x_of_prio : Z -> Z) (tcb_bit_y_of_prio : Z -> Z)
               (PtrArray::full : Z -> Z -> list Z -> Assertion)
               (PtrArray::missing_i : Z -> Z -> Z -> Z -> list Z -> Assertion)
               (UCharArray::full : Z -> Z -> list Z -> Assertion)
               (UCharArray::missing_i : Z -> Z -> Z -> Z -> list Z -> Assertion)
               (replace_Znth : {A} -> Z -> A -> list A -> list A)
*/

static INT8U OSMutex_BasePrio(OS_TCB *ptcb)
/*@ With (image : TCBCommonImage) (table : list Z) (fallback : Z)
    Require 0 <= fallback && fallback < 256 && Zlength(table) == 64 &&
      mutex_priority_fallback(image, fallback) &&
      tcb64_storage_rep(ptcb, image) *
      PtrArray::full(&OSTCBPrioTbl, 64, table)
    Ensure mutex_base_priority_result(table, ptcb, fallback, __return) &&
      tcb64_storage_rep(ptcb, image) *
      PtrArray::full(&OSTCBPrioTbl, 64, table)
*/
{
    INT16U i;
    /*@ mutex_priority_fallback(image, fallback) && tcb64_storage_rep(ptcb, image)
        which implies
        data_at(&(ptcb->OSTCBPrio), INT8U, fallback) *
        tcb64_storage_without(ptcb, TCBPrio, image) */
    INT8U prio = ptcb->OSTCBPrio;

    /*@ Inv Assert
      0 <= i && i <= 64 && 0 <= prio && prio < 256 &&
      0 <= fallback && fallback < 256 && ptcb == ptcb@pre &&
      Zlength(table) == 64 && mutex_priority_fallback(image, fallback) &&
      mutex_base_priority_prefix(table, ptcb, fallback, i, prio) &&
      data_at(&(ptcb->OSTCBPrio), INT8U, fallback) *
      tcb64_storage_without(ptcb, TCBPrio, image) *
      PtrArray::full(&OSTCBPrioTbl, 64, table)
    */
    for (i = 0u; i <= OS_LOWEST_PRIO; i++) {

        if (OSTCBPrioTbl[i] == ptcb) {
            prio = (INT8U)i;
        }

    }
    /*@ mutex_priority_fallback(image, fallback) &&
        data_at(&(ptcb->OSTCBPrio), INT8U, fallback) *
        tcb64_storage_without(ptcb, TCBPrio, image)
        which implies tcb64_storage_rep(ptcb, image) */
    return prio;
}

static INT8U OSMutex_EffectivePrio(OS_TCB *ptcb)
/*@ With (image : TCBCommonImage) (table : list Z) (fallback : Z)
    Require 0 <= fallback && fallback < 256 && Zlength(table) == 64 &&
      mutex_priority_fallback(image, fallback) &&
      tcb64_storage_rep(ptcb, image) *
      PtrArray::full(&OSTCBPrioTbl, 64, table)
    Ensure mutex_effective_priority_result(table, ptcb, fallback, __return) &&
      tcb64_storage_rep(ptcb, image) *
      PtrArray::full(&OSTCBPrioTbl, 64, table)
*/
{
    INT16U i;

    /*@ Inv Assert
      0 <= i && i <= 64 && 0 <= fallback && fallback < 256 &&
      ptcb == ptcb@pre && Zlength(table) == 64 &&
      mutex_priority_fallback(image, fallback) &&
      mutex_priority_no_match(table, ptcb, i) &&
      tcb64_storage_rep(ptcb, image) *
      PtrArray::full(&OSTCBPrioTbl, 64, table)
    */
    for (i = 0u; i <= OS_LOWEST_PRIO; i++) {

        if (OSTCBPrioTbl[i] == ptcb) {

            return (INT8U)i;
        }

    }
    /*@ mutex_priority_fallback(image, fallback) && tcb64_storage_rep(ptcb, image)
        which implies
        data_at(&(ptcb->OSTCBPrio), INT8U, fallback) *
        tcb64_storage_without(ptcb, TCBPrio, image) */
    /* The read at return retains the same full object via its postcondition;
       its restoration is a generated return obligation. */
    return ptcb->OSTCBPrio;
}

static void OSMutex_RdyAtPrio(OS_TCB *ptcb, INT8U prio)
/*@ With (image : TCBCommonImage) (table rows : list Z)
         (old_prio old_x old_y old_bitx old_bity group current current_prio : Z)
    Require 0 <= prio && prio < 64 && 0 <= old_y && old_y < 8 &&
      Zlength(table) == 64 && Zlength(rows) == 8 &&
      mutex_priority_image_fields(image, old_prio, old_x, old_y, old_bitx, old_bity) &&
      tcb64_storage_rep(ptcb, image) *
      PtrArray::full(&OSTCBPrioTbl, 64, table) * UCharArray::full(&OSRdyTbl, 8, rows) *
      data_at(&OSRdyGrp, OS_PRIO, group) * data_at(&OSTCBCur, OS_TCB *, current) *
      data_at(&OSPrioCur, INT8U, current_prio)
    Ensure tcb64_storage_rep(ptcb, mutex_priority_image(image, prio)) *
      PtrArray::full(&OSTCBPrioTbl, 64, replace_Znth(prio, ptcb, table)) *
      UCharArray::full(&OSRdyTbl, 8, mutex_priority_rows(rows, old_y, old_bitx, prio)) *
      data_at(&OSRdyGrp, OS_PRIO, mutex_priority_group(rows, group, old_y, old_bitx, old_bity, prio)) *
      data_at(&OSTCBCur, OS_TCB *, current) *
      data_at(&OSPrioCur, INT8U, mutex_priority_current(ptcb, current, current_prio, prio))
*/
{
    INT8U y;
    BOOLEAN rdy;

    /*@ mutex_priority_image_fields(image, old_prio, old_x, old_y, old_bitx, old_bity) &&
        tcb64_storage_rep(ptcb, image)
        which implies
        mutex_priority_tcb_rest(ptcb, image) *
        data_at(&(ptcb->OSTCBPrio), INT8U, old_prio) *
        data_at(&(ptcb->OSTCBX), INT8U, old_x) *
        data_at(&(ptcb->OSTCBY), INT8U, old_y) *
        data_at(&(ptcb->OSTCBBitX), OS_PRIO, old_bitx) *
        data_at(&(ptcb->OSTCBBitY), OS_PRIO, old_bity) */
    /* Preserve entry byte observations before ready-table or group writes. */
    /*@ Zlength(rows) == 8 &&
        data_at(&OSRdyGrp, OS_PRIO, group) * UCharArray::full(&OSRdyTbl, 8, rows) *
        data_at(&(ptcb->OSTCBBitX), OS_PRIO, old_bitx) *
        data_at(&(ptcb->OSTCBBitY), OS_PRIO, old_bity)
        which implies
        0 <= group && group < 256 && 0 <= old_bitx && old_bitx < 256 &&
        0 <= old_bity && old_bity < 256 && Zlength(rows) == 8 &&
        (forall (index : Z), (0 <= index && index < 8) =>
          (0 <= Znth(index, rows, 0) && Znth(index, rows, 0) < 256)) &&
        data_at(&OSRdyGrp, OS_PRIO, group) * UCharArray::full(&OSRdyTbl, 8, rows) *
        data_at(&(ptcb->OSTCBBitX), OS_PRIO, old_bitx) *
        data_at(&(ptcb->OSTCBBitY), OS_PRIO, old_bity) */
    y = ptcb->OSTCBY;

    rdy = (OSRdyTbl[y] & ptcb->OSTCBBitX) != 0u;
    if (rdy == OS_TRUE) {
        OSRdyTbl[y] &= (OS_PRIO)~ptcb->OSTCBBitX;
        OS_TRACE_TASK_SUSPENDED(ptcb);
        if (OSRdyTbl[y] == 0u) {
            OSRdyGrp &= (OS_PRIO)~ptcb->OSTCBBitY;
        }
    }
    /*@ Assert
      ptcb == ptcb@pre && prio == prio@pre && 0 <= prio && prio < 64 &&
      y == old_y && 0 <= old_y && old_y < 8 && Zlength(table) == 64 && Zlength(rows) == 8 &&
      0 <= group && group < 256 && 0 <= old_bitx && old_bitx < 256 &&
      0 <= old_bity && old_bity < 256 &&
      (forall (index : Z), (0 <= index && index < 8) =>
        (0 <= Znth(index, rows, 0) && Znth(index, rows, 0) < 256)) &&
      rdy == encode_bool(mutex_priority_was_ready(rows, old_y, old_bitx)) &&
      mutex_priority_tcb_rest(ptcb, image) *
      data_at(&(ptcb->OSTCBPrio), INT8U, old_prio) * data_at(&(ptcb->OSTCBX), INT8U, old_x) *
      data_at(&(ptcb->OSTCBY), INT8U, old_y) * data_at(&(ptcb->OSTCBBitX), OS_PRIO, old_bitx) *
      data_at(&(ptcb->OSTCBBitY), OS_PRIO, old_bity) *
      PtrArray::full(&OSTCBPrioTbl, 64, table) *
      UCharArray::full(&OSRdyTbl, 8, mutex_priority_removed_rows(rows, old_y, old_bitx)) *
      data_at(&OSRdyGrp, OS_PRIO, mutex_priority_removed_group(rows, group, old_y, old_bitx, old_bity)) *
      data_at(&OSTCBCur, OS_TCB *, current) * data_at(&OSPrioCur, INT8U, current_prio)
    */

    ptcb->OSTCBPrio = prio;
    if (ptcb == OSTCBCur) {
        OSPrioCur = prio;
    }
#if OS_LOWEST_PRIO <= 63u
    ptcb->OSTCBY = (INT8U)((INT8U)(prio >> 3u) & 0x07u);
    ptcb->OSTCBX = (INT8U)(prio & 0x07u);
#else
    ptcb->OSTCBY = (INT8U)((INT8U)(prio >> 4u) & 0x0Fu);
    ptcb->OSTCBX = (INT8U) (prio & 0x0Fu);
#endif
    ptcb->OSTCBBitY = (OS_PRIO)(1uL << ptcb->OSTCBY);
    ptcb->OSTCBBitX = (OS_PRIO)(1uL << ptcb->OSTCBX);
    /*@ Assert
      ptcb == ptcb@pre && prio == prio@pre && 0 <= prio && prio < 64 &&
      y == old_y && 0 <= old_y && old_y < 8 && Zlength(table) == 64 && Zlength(rows) == 8 &&
      0 <= group && group < 256 && 0 <= old_bitx && old_bitx < 256 &&
      0 <= old_bity && old_bity < 256 &&
      (forall (index : Z), (0 <= index && index < 8) =>
        (0 <= Znth(index, rows, 0) && Znth(index, rows, 0) < 256)) &&
      0 <= tcb_y_of_prio(prio) && tcb_y_of_prio(prio) < 8 &&
      0 <= tcb_x_of_prio(prio) && tcb_x_of_prio(prio) < 8 &&
      rdy == encode_bool(mutex_priority_was_ready(rows, old_y, old_bitx)) &&
      mutex_priority_tcb_rest(ptcb, image) *
      data_at(&(ptcb->OSTCBPrio), INT8U, prio) *
      data_at(&(ptcb->OSTCBX), INT8U, tcb_x_of_prio(prio)) *
      data_at(&(ptcb->OSTCBY), INT8U, tcb_y_of_prio(prio)) *
      data_at(&(ptcb->OSTCBBitX), OS_PRIO, tcb_bit_x_of_prio(prio)) *
      data_at(&(ptcb->OSTCBBitY), OS_PRIO, tcb_bit_y_of_prio(prio)) *
      PtrArray::full(&OSTCBPrioTbl, 64, table) *
      UCharArray::full(&OSRdyTbl, 8, mutex_priority_removed_rows(rows, old_y, old_bitx)) *
      data_at(&OSRdyGrp, OS_PRIO, mutex_priority_removed_group(rows, group, old_y, old_bitx, old_bity)) *
      data_at(&OSTCBCur, OS_TCB *, current) *
      data_at(&OSPrioCur, INT8U, mutex_priority_current(ptcb, current, current_prio, prio))
    */
    if (rdy == OS_TRUE) {
        OSRdyGrp |= ptcb->OSTCBBitY;

        OSRdyTbl[ptcb->OSTCBY] |= ptcb->OSTCBBitX;

    }

    OSTCBPrioTbl[prio] = ptcb;

    if (rdy == OS_TRUE) {
        OS_TRACE_TASK_READY(ptcb);
    }
    /*@ mutex_priority_tcb_rest(ptcb, image) *
        data_at(&(ptcb->OSTCBPrio), INT8U, prio) *
        data_at(&(ptcb->OSTCBX), INT8U, tcb_x_of_prio(prio)) *
        data_at(&(ptcb->OSTCBY), INT8U, tcb_y_of_prio(prio)) *
        data_at(&(ptcb->OSTCBBitX), OS_PRIO, tcb_bit_x_of_prio(prio)) *
        data_at(&(ptcb->OSTCBBitY), OS_PRIO, tcb_bit_y_of_prio(prio))
        which implies tcb64_storage_rep(ptcb, mutex_priority_image(image, prio)) */
}
