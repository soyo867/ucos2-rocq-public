/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OS_EventWaitListInit (OS_EVENT *pevent)
/*@ Require event_wait_list_init_pre(
      &(pevent->OSEventGrp), &(pevent->OSEventTbl[0]))
    Ensure event_wait_list_init_post(
      &(pevent->OSEventGrp), &(pevent->OSEventTbl[0]))
*/
{
    INT8U  i;


    
/*@ event_wait_list_init_pre(
          &(pevent->OSEventGrp), &(pevent->OSEventTbl[0]))
        which implies
        undef_data_at(&(pevent->OSEventGrp), unsigned char) *
        event_wait_list_init_table_prefix(&(pevent->OSEventTbl[0]), 0)
    */
pevent->OSEventGrp = 0u;                     /* No task waiting on event                           */
    
/*@ Inv Assert
          pevent == pevent@pre && 0 <= i && i <= 8 &&
          data_at(&(pevent->OSEventGrp), unsigned char, 0) *
          event_wait_list_init_table_prefix(&(pevent->OSEventTbl[0]), i)
    */
for (i = 0u; i < OS_EVENT_TBL_SIZE; i++) {
        
/*@ 0 <= i && i < 8 &&
              event_wait_list_init_table_prefix(&(pevent->OSEventTbl[0]), i)
            which implies
              undef_data_at(&(pevent->OSEventTbl[i]), unsigned char) *
              event_wait_list_init_row_frame(&(pevent->OSEventTbl[0]), i)
        */
pevent->OSEventTbl[i] = 0u;
    
/*@ 0 <= i && i < 8 &&
              data_at(&(pevent->OSEventTbl[i]), unsigned char, 0) *
              event_wait_list_init_row_frame(&(pevent->OSEventTbl[0]), i)
            which implies
              event_wait_list_init_table_prefix(&(pevent->OSEventTbl[0]), i + 1)
        */
}

/*@ 0 <= i && i <= 8 && i >= 8 &&
          data_at(&(pevent->OSEventGrp), unsigned char, 0) *
          event_wait_list_init_table_prefix(&(pevent->OSEventTbl[0]), i)
        which implies
          i == 8 &&
          event_wait_list_init_post(&(pevent->OSEventGrp), &(pevent->OSEventTbl[0]))
    */
}
