/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OSStart (void)
/*@ With (env : OsStartEnvironment) (entry : UCOS2_Verify_State)
         (running : Z)
         (X : OsStartObservation -> UCOS2_Verify_State -> Prop)
         (frame : Assertion)
    Require &OSRunning == os_start_running_address(env) &&
            sched_new_global_addresses(os_start_sg(env), OSUnMapTbl, &OSRdyGrp,
              OSRdyTbl, &OSPrioHighRdy) &&
            os_start_global_addresses(env, OSUnMapTbl, &OSRdyGrp, OSRdyTbl,
              &OSPrioHighRdy, &OSPrioCur, OSTCBPrioTbl, &OSTCBCur,
              &OSTCBHighRdy, &OSRunning) &&
            os_start_pre(env, entry, running, X, frame)
    Ensure os_start_post(env, entry, running, X, frame)
*/
{
    /*@ &OSRunning == os_start_running_address(env) &&
        os_start_pre(env, entry, running, X, frame)
        which implies
        os_start_safe(env, running, entry, X) &&
        os_start_entry_facts(env, entry, running) &&
        data_at(&OSRunning, unsigned char, running) *
        os_start_entry_remainder(env, entry, running, frame)
    */
    if (OSRunning == OS_FALSE) {
        /*@ &OSRunning == os_start_running_address(env) &&
            os_start_safe(env, running, entry, X) &&
            os_start_entry_facts(env, entry, running) && running == 0 &&
            data_at(&OSRunning, unsigned char, 0) *
            os_start_entry_remainder(env, entry, running, frame)
            which implies
            os_start_safe(env, 0, entry, X) && os_start_startup(env, entry) &&
            sched_new_rep(os_start_sg(env), os_start_group(entry), os_start_rows(entry),
              os_start_old_high(entry)) *
            os_start_sched_frame(env, entry, frame)
        */
        OS_SchedNew();                               /* Find highest priority's task priority number   */
        /*@ os_start_global_addresses(env, OSUnMapTbl, &OSRdyGrp, OSRdyTbl,
              &OSPrioHighRdy, &OSPrioCur, OSTCBPrioTbl, &OSTCBCur,
              &OSTCBHighRdy, &OSRunning) &&
            sched_new_rep(os_start_sg(env), os_start_group(entry), os_start_rows(entry),
              sched_new_priority(os_start_group(entry), os_start_rows(entry))) *
            os_start_sched_frame(env, entry, frame)
            which implies
            data_at(&OSPrioHighRdy, unsigned char,
              sched_new_priority(os_start_group(entry), os_start_rows(entry))) *
            data_at(&OSPrioCur, unsigned char, os_start_old_priority(entry)) *
            data_at(&OSTCBCur, OS_TCB *, os_start_old_current(env, entry)) *
            data_at(&OSTCBHighRdy, OS_TCB *, os_start_old_high_task(env, entry)) *
            PtrArray::full(OSTCBPrioTbl, 64, os_start_table_values(env, entry)) *
            os_start_c_remainder(env, entry, frame)
        */
        OSPrioCur     = OSPrioHighRdy;
        /*@ os_start_global_addresses(env, OSUnMapTbl, &OSRdyGrp, OSRdyTbl,
              &OSPrioHighRdy, &OSPrioCur, OSTCBPrioTbl, &OSTCBCur,
              &OSTCBHighRdy, &OSRunning) &&
            data_at(&OSPrioHighRdy, unsigned char,
              sched_new_priority(os_start_group(entry), os_start_rows(entry))) *
            data_at(&OSPrioCur, unsigned char,
              sched_new_priority(os_start_group(entry), os_start_rows(entry))) *
            data_at(&OSTCBCur, OS_TCB *, os_start_old_current(env, entry)) *
            data_at(&OSTCBHighRdy, OS_TCB *, os_start_old_high_task(env, entry)) *
            PtrArray::full(OSTCBPrioTbl, 64, os_start_table_values(env, entry)) *
            os_start_c_remainder(env, entry, frame)
            which implies
            data_at(&OSPrioHighRdy, unsigned char,
              sched_new_priority(os_start_group(entry), os_start_rows(entry))) *
            data_at(&OSPrioCur, unsigned char,
              sched_new_priority(os_start_group(entry), os_start_rows(entry))) *
            data_at(&OSTCBCur, OS_TCB *, os_start_old_current(env, entry)) *
            data_at(&OSTCBHighRdy, OS_TCB *, os_start_old_high_task(env, entry)) *
            data_at(pointer_offset(&OSTCBPrioTbl,
              sched_new_priority(os_start_group(entry), os_start_rows(entry)), OS_TCB *), OS_TCB *,
              os_start_pointer(env, entry)) *
            os_start_table_remainder(env, entry, frame)
        */
        OSTCBHighRdy  = OSTCBPrioTbl[OSPrioHighRdy]; /* Point to highest priority task ready to run    */
        OSTCBCur      = OSTCBHighRdy;
        /*@ os_start_global_addresses(env, OSUnMapTbl, &OSRdyGrp, OSRdyTbl,
              &OSPrioHighRdy, &OSPrioCur, OSTCBPrioTbl, &OSTCBCur,
              &OSTCBHighRdy, &OSRunning) &&
            os_start_safe(env, 0, entry, X) && os_start_startup(env, entry) &&
            data_at(&OSPrioHighRdy, unsigned char,
              sched_new_priority(os_start_group(entry), os_start_rows(entry))) *
            data_at(&OSPrioCur, unsigned char,
              sched_new_priority(os_start_group(entry), os_start_rows(entry))) *
            data_at(&OSTCBCur, OS_TCB *, os_start_pointer(env, entry)) *
            data_at(&OSTCBHighRdy, OS_TCB *, os_start_pointer(env, entry)) *
            data_at(pointer_offset(&OSTCBPrioTbl,
              sched_new_priority(os_start_group(entry), os_start_rows(entry)), OS_TCB *), OS_TCB *,
              os_start_pointer(env, entry)) *
            os_start_table_remainder(env, entry, frame)
            which implies
            os_start_high_pre(env, kernel_start_ready_state(entry), X, frame)
        */
        OSStartHighRdy();                            /* Execute target specific code to start task     */
    }
}
