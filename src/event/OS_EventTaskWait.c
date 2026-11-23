/* Single-function annotation carrier. Rebuild with the matching
 * environment and annotation_carrier.py compose. */

void OS_EventTaskWait (OS_EVENT *pevent)
/*@ With tcb row bit_x bit_y old_event event_row event_group ready_row ready_group (frame : Assertion)
    Require 0 <= row && row < 8 &&
      data_at(&OSTCBCur, OS_TCB *, tcb) *
      data_at(field_addr(tcb, struct os_tcb, OSTCBEventPtr), OS_EVENT *, old_event) *
      data_at(field_addr(tcb, struct os_tcb, OSTCBY), unsigned char, row) *
      data_at(field_addr(tcb, struct os_tcb, OSTCBBitX), unsigned char, bit_x) *
      data_at(field_addr(tcb, struct os_tcb, OSTCBBitY), unsigned char, bit_y) *
      data_at(pointer_offset(&(pevent->OSEventTbl), row, unsigned char), unsigned char, event_row) *
      data_at(&(pevent->OSEventGrp), unsigned char, event_group) *
      data_at(pointer_offset(&OSRdyTbl, row, unsigned char), unsigned char, ready_row) *
      data_at(&OSRdyGrp, unsigned char, ready_group) * frame
    Ensure event_task_wait_post(&OSTCBCur, tcb, pevent, &OSRdyGrp, &OSRdyTbl,
      row, bit_x, bit_y, event_row, event_group, ready_row, ready_group) * frame
*/
{
    INT8U y;

    /* Preserve the overwritten ECB input-byte ranges for the OR observer. */
    /*@ data_at(pointer_offset(&(pevent->OSEventTbl), row, unsigned char), unsigned char, event_row) *
          data_at(&(pevent->OSEventGrp), unsigned char, event_group)
        which implies
          0 <= event_row && event_row < 256 && 0 <= event_group && event_group < 256 &&
          data_at(pointer_offset(&(pevent->OSEventTbl), row, unsigned char), unsigned char, event_row) *
          data_at(&(pevent->OSEventGrp), unsigned char, event_group)
    */
    OSTCBCur->OSTCBEventPtr = pevent;
    pevent->OSEventTbl[OSTCBCur->OSTCBY] |= OSTCBCur->OSTCBBitX;
    pevent->OSEventGrp |= OSTCBCur->OSTCBBitY;

    y = OSTCBCur->OSTCBY;
    OSRdyTbl[y] &= (OS_PRIO)~OSTCBCur->OSTCBBitX;
    OS_TRACE_TASK_SUSPENDED(OSTCBCur);
    if (OSRdyTbl[y] == 0u) {
        OSRdyGrp &= (OS_PRIO)~OSTCBCur->OSTCBBitY;
    }
}
