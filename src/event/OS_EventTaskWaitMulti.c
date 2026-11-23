#include <ucos_ii.h>
#include "verification_stdlib.h"
#include "event_task_wait_multi_annotations.h"

void  OS_EventTaskWaitMulti (OS_EVENT **pevents_wait)
/*@ With (sg: StableGlobVars) (tasks: Glob_TaskAbstractState)
    (entry: Glob_EventAbstractState) (tid: Z) (t: TaskAbstractState)
    (pointers: list Z) (instances: EventTaskWaitMultiInstances)
    (tcb base ready_row ready_grp: Z) (frame: Assertion)
    Require pevents_wait == base && (event_task_wait_multi_input(sg, tasks, entry, tid, t, pointers, instances)) &&
      event_multi_array_rep(base, pointers) * event_raw_rep(sg, tasks, entry) * data_at(&OSTCBCur, OS_TCB *, tcb) *
undef_data_at(field_addr(tcb, struct os_tcb, OSTCBEventMultiPtr), OS_EVENT **) *
undef_data_at(field_addr(tcb, struct os_tcb, OSTCBEventMultiRdy), OS_EVENT *) *
data_at(field_addr(tcb, struct os_tcb, OSTCBY), unsigned char, tcb_y_of_prio(t.curPrio)) *
data_at(field_addr(tcb, struct os_tcb, OSTCBBitX), unsigned char, tcb_bit_x_of_prio(t.curPrio)) *
data_at(field_addr(tcb, struct os_tcb, OSTCBBitY), unsigned char, tcb_bit_y_of_prio(t.curPrio)) *
data_at(pointer_offset(&OSRdyTbl, tcb_y_of_prio(t.curPrio), unsigned char), unsigned char, ready_row) *
data_at(&OSRdyGrp, unsigned char, ready_grp) * frame
    Ensure event_task_wait_multi_post(sg, tasks, entry, tid, t, instances, pointers,
      &OSTCBCur, tcb, base, &OSRdyGrp, &OSRdyTbl, ready_row, ready_grp) * frame
*/
{
    OS_EVENT **pevents;
    OS_EVENT  *pevent;
    INT8U      y;


    /*@ (event_task_wait_multi_input(sg, tasks, entry, tid, t, pointers, instances)) && event_raw_rep(sg, tasks, entry)
which implies (event_task_wait_multi_input(sg, tasks, entry, tid, t, pointers, instances)) && 0 <= tcb_y_of_prio(t.curPrio) && tcb_y_of_prio(t.curPrio) < 8 && event_task_wait_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, 0, entry) && event_raw_rep(sg, tasks, entry) */
    /*@ 0 <= tcb_bit_x_of_prio(t.curPrio) && tcb_bit_x_of_prio(t.curPrio) < 256 by local */
    /*@ 0 <= tcb_bit_y_of_prio(t.curPrio) && tcb_bit_y_of_prio(t.curPrio) < 256 by local */
    OSTCBCur->OSTCBEventMultiPtr = (OS_EVENT **)pevents_wait;       /* Store ptr to ECBs in TCB        */
    OSTCBCur->OSTCBEventMultiRdy = (OS_EVENT  *)0;

    pevents =  pevents_wait;
    /*@ pevents == base && event_multi_array_rep(base, pointers)
which implies pevents == base && (event_multi_array_valid(base, pointers)) && data_at(pevents, OS_EVENT *, event_task_wait_multi_pointer(pointers, 0)) * event_task_wait_multi_array_missing(base, pointers, 0) */
    pevent  = *pevents;
    /*@ pevents == base && pevent == event_task_wait_multi_pointer(pointers, 0) &&
(event_multi_array_valid(base, pointers)) && data_at(pevents, OS_EVENT *, event_task_wait_multi_pointer(pointers, 0)) * event_task_wait_multi_array_missing(base, pointers, 0)
which implies pevents == base && pevent == event_task_wait_multi_pointer(pointers, 0) &&
(event_task_wait_multi_cursor(pevents, base, 0)) &&
(event_task_wait_multi_value(pevent, pointers, 0)) && event_multi_array_rep(base, pointers) */
    /*@ Inv exists (index: Z) (events: Glob_EventAbstractState),
pevents_wait == base && (event_task_wait_multi_cursor(pevents, base, index)) && (event_task_wait_multi_value(pevent, pointers, index)) &&
(event_task_wait_multi_input(sg, tasks, entry, tid, t, pointers, instances)) && event_task_wait_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, index, events) && 0 <= tcb_y_of_prio(t.curPrio) && tcb_y_of_prio(t.curPrio) < 8 &&
0 <= tcb_bit_x_of_prio(t.curPrio) && tcb_bit_x_of_prio(t.curPrio) < 256 && 0 <= tcb_bit_y_of_prio(t.curPrio) && tcb_bit_y_of_prio(t.curPrio) < 256 &&
event_multi_array_rep(base, pointers) * event_raw_rep(sg, tasks, events) * data_at(&OSTCBCur, OS_TCB *, tcb) *
data_at(field_addr(tcb, struct os_tcb, OSTCBEventMultiPtr), OS_EVENT **, base) *
data_at(field_addr(tcb, struct os_tcb, OSTCBEventMultiRdy), OS_EVENT *, 0) *
data_at(field_addr(tcb, struct os_tcb, OSTCBY), unsigned char, tcb_y_of_prio(t.curPrio)) *
data_at(field_addr(tcb, struct os_tcb, OSTCBBitX), unsigned char, tcb_bit_x_of_prio(t.curPrio)) *
data_at(field_addr(tcb, struct os_tcb, OSTCBBitY), unsigned char, tcb_bit_y_of_prio(t.curPrio)) *
data_at(pointer_offset(&OSRdyTbl, tcb_y_of_prio(t.curPrio), unsigned char), unsigned char, ready_row) *
data_at(&OSRdyGrp, unsigned char, ready_grp) * frame */
    while (pevent != (OS_EVENT *)0) {                               /* Put task in waiting lists       */
        /*@ exists (index: Z) (events: Glob_EventAbstractState),
(event_task_wait_multi_cursor(pevents, base, index)) && (event_task_wait_multi_value(pevent, pointers, index)) && pevent != 0 &&
(event_task_wait_multi_input(sg, tasks, entry, tid, t, pointers, instances)) && event_task_wait_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, index, events) && event_multi_array_rep(base, pointers) * event_raw_rep(sg, tasks, events)
which implies exists (index: Z) (events: Glob_EventAbstractState) (eid: Z) (e: OSEventAbstractState),
(event_task_wait_multi_cursor(pevents, base, index)) && (event_task_wait_multi_value(pevent, pointers, index)) &&
(event_task_wait_multi_input(sg, tasks, entry, tid, t, pointers, instances)) && event_task_wait_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, index, events) && (event_task_wait_multi_selected(sg, events, pointers, instances, index, eid, e)) &&
0 <= encode_event_wait_tbl_at_or(e.waitList, tasks, tcb_y_of_prio(t.curPrio)) && encode_event_wait_tbl_at_or(e.waitList, tasks, tcb_y_of_prio(t.curPrio)) < 256 && 0 <= encode_event_wait_grp(e.waitList, tasks) && encode_event_wait_grp(e.waitList, tasks) < 256 &&
event_multi_array_rep(base, pointers) * data_at(pointer_offset(&(pevent->OSEventTbl), tcb_y_of_prio(t.curPrio), unsigned char), unsigned char, encode_event_wait_tbl_at_or(e.waitList, tasks, tcb_y_of_prio(t.curPrio))) *
data_at(&(pevent->OSEventGrp), unsigned char, encode_event_wait_grp(e.waitList, tasks)) * event_task_wait_multi_event_frame(sg, tasks, events, eid, e, tcb_y_of_prio(t.curPrio)) */
    pevent->OSEventTbl[OSTCBCur->OSTCBY] |= OSTCBCur->OSTCBBitX;
        pevent->OSEventGrp                   |= OSTCBCur->OSTCBBitY;
        /*@ exists (index: Z) (events: Glob_EventAbstractState) (eid: Z) (e: OSEventAbstractState),
(event_task_wait_multi_cursor(pevents, base, index)) && (event_task_wait_multi_value(pevent, pointers, index)) && (event_task_wait_multi_input(sg, tasks, entry, tid, t, pointers, instances)) && event_task_wait_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, index, events) && (event_task_wait_multi_selected(sg, events, pointers, instances, index, eid, e)) &&
event_multi_array_rep(base, pointers) * data_at(pointer_offset(&(pevent->OSEventTbl), tcb_y_of_prio(t.curPrio), unsigned char), unsigned char, encode_event_wait_tbl_at_or(e.waitList, tasks, tcb_y_of_prio(t.curPrio)) | tcb_bit_x_of_prio(t.curPrio)) *
data_at(&(pevent->OSEventGrp), unsigned char, encode_event_wait_grp(e.waitList, tasks) | tcb_bit_y_of_prio(t.curPrio)) * event_task_wait_multi_event_frame(sg, tasks, events, eid, e, tcb_y_of_prio(t.curPrio))
which implies exists (next: Z) (after: Glob_EventAbstractState),
(event_task_wait_multi_cursor(pevents + 1, base, next)) && (event_task_wait_multi_input(sg, tasks, entry, tid, t, pointers, instances)) && event_task_wait_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, next, after) &&
undef_data_at(&pevent, OS_EVENT *) * event_multi_array_rep(base, pointers) * event_raw_rep(sg, tasks, after) */
    pevents++;
        /*@ exists (next: Z) (after: Glob_EventAbstractState),
(event_task_wait_multi_cursor(pevents, base, next)) && event_task_wait_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, next, after) && event_multi_array_rep(base, pointers) * event_raw_rep(sg, tasks, after)
which implies exists (next: Z) (after: Glob_EventAbstractState),
(event_task_wait_multi_cursor(pevents, base, next)) && event_task_wait_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, next, after) && (event_multi_array_valid(base, pointers)) &&
data_at(pevents, OS_EVENT *, event_task_wait_multi_pointer(pointers, next)) * event_task_wait_multi_array_missing(base, pointers, next) * event_raw_rep(sg, tasks, after) */
    pevent = *pevents;
/*@ exists (next: Z) (after: Glob_EventAbstractState),
(event_task_wait_multi_cursor(pevents, base, next)) && pevent == event_task_wait_multi_pointer(pointers, next) && event_task_wait_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, next, after) &&
(event_multi_array_valid(base, pointers)) && data_at(pevents, OS_EVENT *, event_task_wait_multi_pointer(pointers, next)) * event_task_wait_multi_array_missing(base, pointers, next) * event_raw_rep(sg, tasks, after)
which implies exists (next: Z) (after: Glob_EventAbstractState),
(event_task_wait_multi_cursor(pevents, base, next)) && (event_task_wait_multi_value(pevent, pointers, next)) && event_task_wait_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, next, after) &&
event_multi_array_rep(base, pointers) * event_raw_rep(sg, tasks, after) */
        }

    /*@ exists (index: Z) (events: Glob_EventAbstractState),
(event_task_wait_multi_value(pevent, pointers, index)) && pevent <= 0 && 0 <= pevent && event_task_wait_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, index, events) && event_multi_array_rep(base, pointers) * event_raw_rep(sg, tasks, events)
which implies undef_data_at(&pevent, OS_EVENT *) * event_multi_array_rep(base, pointers) * event_raw_rep(sg, tasks, event_task_wait_multi_events(sg, tasks, entry, tid, instances)) */
    y             =  OSTCBCur->OSTCBY;            /* Task no longer ready                              */
    OSRdyTbl[y]  &= (OS_PRIO)~OSTCBCur->OSTCBBitX;
    OS_TRACE_TASK_SUSPENDED(OSTCBCur);
    if (OSRdyTbl[y] == 0u) {                      /* Clear event grp bit if this was only task pending */
        OSRdyGrp &= (OS_PRIO)~OSTCBCur->OSTCBBitY;
    }
}
