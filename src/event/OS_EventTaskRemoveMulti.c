#include <ucos_ii.h>
#include "verification_stdlib.h"
#include "event_task_remove_multi_annotations.h"

void  OS_EventTaskRemoveMulti (OS_TCB    *ptcb,
                               OS_EVENT **pevents_multi)
/*@ With (sg: StableGlobVars) (tasks: Glob_TaskAbstractState)
    (entry: Glob_EventAbstractState) (tid: Z) (t: TaskAbstractState)
    (pointers: list Z) (instances: EventTaskRemoveMultiInstances)
    (frame: Assertion)
    Require event_task_remove_multi_input(sg, tasks, entry, tid, t, pointers, instances) &&
      event_multi_array_rep(pevents_multi, pointers) * event_raw_rep(sg, tasks, entry) * data_at(field_addr(ptcb, struct os_tcb, OSTCBY), unsigned char, tcb_y_of_prio(t.curPrio)) *
data_at(field_addr(ptcb, struct os_tcb, OSTCBBitX), unsigned char, tcb_bit_x_of_prio(t.curPrio)) *
data_at(field_addr(ptcb, struct os_tcb, OSTCBBitY), unsigned char, tcb_bit_y_of_prio(t.curPrio)) * frame
    Ensure event_task_remove_multi_post(sg, tasks, entry, tid, t, pointers, instances, ptcb, pevents_multi) * frame
*/
{
    OS_EVENT **pevents;
    OS_EVENT  *pevent;
    INT8U      y;
    OS_PRIO    bity;
    OS_PRIO    bitx;


    /*@ event_task_remove_multi_input(sg, tasks, entry, tid, t, pointers, instances) && event_raw_rep(sg, tasks, entry)
which implies event_task_remove_multi_input(sg, tasks, entry, tid, t, pointers, instances) && 0 <= tcb_y_of_prio(t.curPrio) && tcb_y_of_prio(t.curPrio) < 8 && event_task_remove_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, 0, entry) * event_raw_rep(sg, tasks, entry) */
    /*@ 0 <= tcb_bit_x_of_prio(t.curPrio) && tcb_bit_x_of_prio(t.curPrio) < 256 by local */
    /*@ 0 <= tcb_bit_y_of_prio(t.curPrio) && tcb_bit_y_of_prio(t.curPrio) < 256 by local */
    y       =  ptcb->OSTCBY;
    bity    =  ptcb->OSTCBBitY;
    bitx    =  ptcb->OSTCBBitX;
    pevents =  pevents_multi;
    /*@ pevents == pevents_multi@pre && event_multi_array_rep(pevents_multi@pre, pointers)
which implies pevents == pevents_multi@pre && event_multi_array_valid(pevents_multi@pre, pointers) && data_at(pevents, OS_EVENT *, event_task_remove_multi_pointer(pointers, 0)) * event_task_remove_multi_array_missing(pevents_multi@pre, pointers, 0) */
    pevent  = *pevents;
    /*@ pevents == pevents_multi@pre && pevent == event_task_remove_multi_pointer(pointers, 0) &&
event_multi_array_valid(pevents_multi@pre, pointers) && data_at(pevents, OS_EVENT *, event_task_remove_multi_pointer(pointers, 0)) * event_task_remove_multi_array_missing(pevents_multi@pre, pointers, 0)
which implies pevents == pevents_multi@pre && pevent == event_task_remove_multi_pointer(pointers, 0) && event_task_remove_multi_cursor(pevents, pevents_multi@pre, 0) && event_task_remove_multi_value(pevent, pointers, 0) && event_multi_array_rep(pevents_multi@pre, pointers) */
    /*@ Inv exists (index: Z) (events: Glob_EventAbstractState),
event_task_remove_multi_cursor(pevents, pevents_multi@pre, index) && event_task_remove_multi_value(pevent, pointers, index) &&
y == tcb_y_of_prio(t.curPrio) && bitx == tcb_bit_x_of_prio(t.curPrio) && bity == tcb_bit_y_of_prio(t.curPrio) && event_task_remove_multi_input(sg, tasks, entry, tid, t, pointers, instances) &&
0 <= tcb_y_of_prio(t.curPrio) && tcb_y_of_prio(t.curPrio) < 8 && 0 <= tcb_bit_x_of_prio(t.curPrio) && tcb_bit_x_of_prio(t.curPrio) < 256 && 0 <= tcb_bit_y_of_prio(t.curPrio) && tcb_bit_y_of_prio(t.curPrio) < 256 &&
event_task_remove_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, index, events) * event_multi_array_rep(pevents_multi@pre, pointers) * event_raw_rep(sg, tasks, events) * data_at(field_addr(ptcb@pre, struct os_tcb, OSTCBY), unsigned char, tcb_y_of_prio(t.curPrio)) *
data_at(field_addr(ptcb@pre, struct os_tcb, OSTCBBitX), unsigned char, tcb_bit_x_of_prio(t.curPrio)) *
data_at(field_addr(ptcb@pre, struct os_tcb, OSTCBBitY), unsigned char, tcb_bit_y_of_prio(t.curPrio)) * frame * data_at(&ptcb, OS_TCB *, ptcb@pre) * data_at(&pevents_multi, OS_EVENT **, pevents_multi@pre) */
    while (pevent != (OS_EVENT *)0) {                   /* Remove task from all events' wait lists     */
        /*@ exists (index: Z) (events: Glob_EventAbstractState),
event_task_remove_multi_cursor(pevents, pevents_multi@pre, index) && event_task_remove_multi_value(pevent, pointers, index) && pevent != 0 && event_task_remove_multi_input(sg, tasks, entry, tid, t, pointers, instances) &&
event_task_remove_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, index, events) * event_multi_array_rep(pevents_multi@pre, pointers) * event_raw_rep(sg, tasks, events)
which implies exists (index: Z) (events: Glob_EventAbstractState) (eid: Z) (e: OSEventAbstractState),
event_task_remove_multi_cursor(pevents, pevents_multi@pre, index) && event_task_remove_multi_value(pevent, pointers, index) && event_task_remove_multi_input(sg, tasks, entry, tid, t, pointers, instances) && event_task_remove_multi_selected(sg, events, pointers, instances, index, eid, e) &&
0 <= encode_event_wait_tbl_at_or(e.waitList, tasks, tcb_y_of_prio(t.curPrio)) && encode_event_wait_tbl_at_or(e.waitList, tasks, tcb_y_of_prio(t.curPrio)) < 256 && 0 <= encode_event_wait_grp(e.waitList, tasks) && encode_event_wait_grp(e.waitList, tasks) < 256 &&
event_task_remove_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, index, events) * event_multi_array_rep(pevents_multi@pre, pointers) * data_at(pointer_offset(&(pevent->OSEventTbl), tcb_y_of_prio(t.curPrio), unsigned char), unsigned char, encode_event_wait_tbl_at_or(e.waitList, tasks, tcb_y_of_prio(t.curPrio))) *
data_at(&(pevent->OSEventGrp), unsigned char, encode_event_wait_grp(e.waitList, tasks)) * event_task_remove_multi_event_frame(sg, tasks, events, eid, e, tcb_y_of_prio(t.curPrio)) */
    pevent->OSEventTbl[y]  &= (OS_PRIO)~bitx;
        if (pevent->OSEventTbl[y] == 0u) {
            pevent->OSEventGrp &= (OS_PRIO)~bity;
        }
        /*@ Assert exists (index: Z) (events: Glob_EventAbstractState) (eid: Z) (e: OSEventAbstractState),
event_task_remove_multi_cursor(pevents, pevents_multi@pre, index) && event_task_remove_multi_value(pevent, pointers, index) &&
y == tcb_y_of_prio(t.curPrio) && bitx == tcb_bit_x_of_prio(t.curPrio) && bity == tcb_bit_y_of_prio(t.curPrio) && event_task_remove_multi_input(sg, tasks, entry, tid, t, pointers, instances) && event_task_remove_multi_selected(sg, events, pointers, instances, index, eid, e) &&
0 <= tcb_y_of_prio(t.curPrio) && tcb_y_of_prio(t.curPrio) < 8 && 0 <= tcb_bit_x_of_prio(t.curPrio) && tcb_bit_x_of_prio(t.curPrio) < 256 && 0 <= tcb_bit_y_of_prio(t.curPrio) && tcb_bit_y_of_prio(t.curPrio) < 256 &&
event_task_remove_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, index, events) * event_multi_array_rep(pevents_multi@pre, pointers) * data_at(pointer_offset(&(pevent->OSEventTbl), tcb_y_of_prio(t.curPrio), unsigned char), unsigned char, event_task_remove_cleared(encode_event_wait_tbl_at_or(e.waitList, tasks, tcb_y_of_prio(t.curPrio)), tcb_bit_x_of_prio(t.curPrio))) *
data_at(&(pevent->OSEventGrp), unsigned char, event_task_remove_group(encode_event_wait_tbl_at_or(e.waitList, tasks, tcb_y_of_prio(t.curPrio)), encode_event_wait_grp(e.waitList, tasks), tcb_bit_x_of_prio(t.curPrio), tcb_bit_y_of_prio(t.curPrio))) * event_task_remove_multi_event_frame(sg, tasks, events, eid, e, tcb_y_of_prio(t.curPrio)) * data_at(field_addr(ptcb@pre, struct os_tcb, OSTCBY), unsigned char, tcb_y_of_prio(t.curPrio)) *
data_at(field_addr(ptcb@pre, struct os_tcb, OSTCBBitX), unsigned char, tcb_bit_x_of_prio(t.curPrio)) *
data_at(field_addr(ptcb@pre, struct os_tcb, OSTCBBitY), unsigned char, tcb_bit_y_of_prio(t.curPrio)) * frame * data_at(&ptcb, OS_TCB *, ptcb@pre) * data_at(&pevents_multi, OS_EVENT **, pevents_multi@pre) */
    /*@ exists (index: Z) (events: Glob_EventAbstractState) (eid: Z) (e: OSEventAbstractState),
event_task_remove_multi_cursor(pevents, pevents_multi@pre, index) && event_task_remove_multi_value(pevent, pointers, index) && event_task_remove_multi_input(sg, tasks, entry, tid, t, pointers, instances) && event_task_remove_multi_selected(sg, events, pointers, instances, index, eid, e) &&
event_task_remove_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, index, events) * event_multi_array_rep(pevents_multi@pre, pointers) * data_at(pointer_offset(&(pevent->OSEventTbl), tcb_y_of_prio(t.curPrio), unsigned char), unsigned char, event_task_remove_cleared(encode_event_wait_tbl_at_or(e.waitList, tasks, tcb_y_of_prio(t.curPrio)), tcb_bit_x_of_prio(t.curPrio))) *
data_at(&(pevent->OSEventGrp), unsigned char, event_task_remove_group(encode_event_wait_tbl_at_or(e.waitList, tasks, tcb_y_of_prio(t.curPrio)), encode_event_wait_grp(e.waitList, tasks), tcb_bit_x_of_prio(t.curPrio), tcb_bit_y_of_prio(t.curPrio))) * event_task_remove_multi_event_frame(sg, tasks, events, eid, e, tcb_y_of_prio(t.curPrio))
which implies exists (next: Z) (after: Glob_EventAbstractState),
event_task_remove_multi_cursor(pevents + 1, pevents_multi@pre, next) && event_task_remove_multi_input(sg, tasks, entry, tid, t, pointers, instances) &&
event_task_remove_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, next, after) * undef_data_at(&pevent, OS_EVENT *) * event_multi_array_rep(pevents_multi@pre, pointers) * event_raw_rep(sg, tasks, after) */
    pevents++;
        /*@ exists (next: Z) (after: Glob_EventAbstractState),
event_task_remove_multi_cursor(pevents, pevents_multi@pre, next) && event_task_remove_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, next, after) * event_multi_array_rep(pevents_multi@pre, pointers) * event_raw_rep(sg, tasks, after)
which implies exists (next: Z) (after: Glob_EventAbstractState),
event_task_remove_multi_cursor(pevents, pevents_multi@pre, next) && event_multi_array_valid(pevents_multi@pre, pointers) &&
event_task_remove_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, next, after) *
data_at(pevents, OS_EVENT *, event_task_remove_multi_pointer(pointers, next)) * event_task_remove_multi_array_missing(pevents_multi@pre, pointers, next) * event_raw_rep(sg, tasks, after) */
    pevent = *pevents;
/*@ exists (next: Z) (after: Glob_EventAbstractState),
event_task_remove_multi_cursor(pevents, pevents_multi@pre, next) && pevent == event_task_remove_multi_pointer(pointers, next) && event_multi_array_valid(pevents_multi@pre, pointers) && event_task_remove_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, next, after) *
data_at(pevents, OS_EVENT *, event_task_remove_multi_pointer(pointers, next)) * event_task_remove_multi_array_missing(pevents_multi@pre, pointers, next) * event_raw_rep(sg, tasks, after)
which implies exists (next: Z) (after: Glob_EventAbstractState),
event_task_remove_multi_cursor(pevents, pevents_multi@pre, next) && event_task_remove_multi_value(pevent, pointers, next) && event_task_remove_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, next, after) * event_multi_array_rep(pevents_multi@pre, pointers) * event_raw_rep(sg, tasks, after) */
        }/*@ exists (index: Z) (events: Glob_EventAbstractState),
event_task_remove_multi_value(pevent, pointers, index) && pevent <= 0 && 0 <= pevent && event_task_remove_multi_loop_assert(sg, tasks, entry, tid, pointers, instances, index, events) * event_multi_array_rep(pevents_multi@pre, pointers) * event_raw_rep(sg, tasks, events)
which implies undef_data_at(&pevent, OS_EVENT *) * event_multi_array_rep(pevents_multi@pre, pointers) *
event_raw_rep(sg, tasks, event_task_remove_multi_events(entry, tid, instances)) */
    
}
