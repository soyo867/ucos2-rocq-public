/* Single-function annotation carrier. Rebuild with the matching
 * environment and annotation_carrier.py compose. */

void OS_EventTaskRemove (OS_TCB *ptcb, OS_EVENT *pevent)
/*@ With row bit_x bit_y row_value group_value
    Require event_task_remove_pre(ptcb,
      &(pevent->OSEventGrp), &(pevent->OSEventTbl[0]),
      row, bit_x, bit_y, row_value, group_value)
    Ensure event_task_remove_post(ptcb,
      &(pevent->OSEventGrp), &(pevent->OSEventTbl[0]),
      row, bit_x, bit_y, row_value, group_value)
*/
{
    INT8U y;

    /*@ event_task_remove_pre(ptcb,
          &(pevent->OSEventGrp), &(pevent->OSEventTbl[0]),
          row, bit_x, bit_y, row_value, group_value)
        which implies
        0 <= row && row < 8 &&
        data_at(&(ptcb->OSTCBY), unsigned char, row) *
        data_at(&(ptcb->OSTCBBitX), unsigned char, bit_x) *
        data_at(&(ptcb->OSTCBBitY), unsigned char, bit_y) *
        undef_data_at(&(ptcb->OSTCBEventPtr), OS_EVENT *) *
        data_at(&(pevent->OSEventGrp), unsigned char, group_value) *
        data_at(&(pevent->OSEventTbl[row]), unsigned char, row_value)
    */
    y = ptcb->OSTCBY;
    pevent->OSEventTbl[y] &= (OS_PRIO)~ptcb->OSTCBBitX;
    if (pevent->OSEventTbl[y] == 0u) {
        pevent->OSEventGrp &= (OS_PRIO)~ptcb->OSTCBBitY;
    }
    ptcb->OSTCBEventPtr = (OS_EVENT *)0;
}
