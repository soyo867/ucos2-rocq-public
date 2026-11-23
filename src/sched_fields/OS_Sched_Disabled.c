/* Single-function OS_Sched carrier, using the actual handler execution view.
 * Rebuild from the original configured headers and the adjacent disabled overlay.
 * Executable statements and macros are unchanged.
 */
void OS_Sched (void)
/*@ With (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
         local (sg : StableGlobVars) (view : OsExecutionView) (mask : Z)
         (before : UCOS2_Verify_State) (frame : Assertion)
    Require sched_disabled_addresses(sg, &OSIntNesting, &OSLockNesting) &&
      sched_fields_disabled_pre(environment, critical, local, sg, view, mask, before, frame)
    Ensure sched_disabled_addresses(sg, &OSIntNesting, &OSLockNesting) &&
      sched_fields_disabled_post(environment, critical, sg, view, mask, before, local, frame)
*/

{
#if OS_CRITICAL_METHOD == 3u                           /* Allocate storage for CPU status register     */
    OS_CPU_SR  cpu_sr = 0u;
#endif



    
    /*@ sched_fields_disabled_pre(environment, critical, local, sg, view, mask, before, frame)
        which implies exists (first_heap : model),
        sched_fields_heap_cut(sched_fields_disabled_pre(environment, critical, local, sg,
          view, mask, before, frame), first_heap)
    */
    /*@ Given first_heap */
    OS_ENTER_CRITICAL();
    /*@ Assert exists (entered : OsExecutionView) (acquired : UCOS2_Verify_State)
        (entered_local : Armv7aContinuation -> Assertion) (saved_heap : model),
        sched_disabled_addresses(sg, &OSIntNesting, &OSLockNesting) &&
        sched_fields_disabled_save_event(environment, critical, sg, view, entered, mask, cpu_sr,
          before, acquired, local, entered_local, frame, first_heap, saved_heap) &&
        sched_disabled_completed_clients(critical, entered) &&
        sched_disabled_entry_source(entered, acquired) && UCOS2_state_inv(sg, acquired) &&
        interrupt_saved_value(mask, cpu_sr) &&
        sched_fields_disabled_masked(environment, critical, entered_local, sg, entered,
          cpu_sr, acquired, acquired) * frame
    */
    /*@ Given entered acquired entered_local saved_heap */
    /*@ sched_disabled_addresses(sg, &OSIntNesting, &OSLockNesting) &&
        sched_disabled_entry_source(entered, acquired) &&
        sched_fields_disabled_masked(environment, critical, entered_local, sg, entered,
          cpu_sr, acquired, acquired)
        which implies
        sched_disabled_addresses(sg, &OSIntNesting, &OSLockNesting) &&
        sched_disabled_entry_source(entered, acquired) &&
        0 < os_sched_ints(acquired) + os_sched_locks(acquired) &&
        0 <= os_sched_ints(acquired) && os_sched_ints(acquired) <= 255 &&
        0 <= os_sched_locks(acquired) && os_sched_locks(acquired) <= 255 &&
        data_at(&OSIntNesting, INT8U, os_sched_ints(acquired)) *
        data_at(&OSLockNesting, INT8U, os_sched_locks(acquired)) *
        sched_fields_disabled_counter_frame(environment, critical, entered_local, sg, entered,
          cpu_sr, acquired, acquired)
    */

    
    
    
    if (OSIntNesting == 0u) {                          /* Schedule only if all ISRs done and ...       */
        if (OSLockNesting == 0u) {                     /* ... scheduler is not locked                  */
            
            /*@ Assert 0 == 1 */
            OS_SchedNew();
            OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy];
            if (OSPrioHighRdy != OSPrioCur) {          /* No Ctx Sw if current task is highest rdy     */
#if OS_TASK_PROFILE_EN > 0u
                OSTCBHighRdy->OSTCBCtxSwCtr++;         /* Inc. # of context switches to this task      */
#endif
                OSCtxSwCtr++;                          /* Increment context switch counter             */

#if OS_TASK_CREATE_EXT_EN > 0u
#if defined(OS_TLS_TBL_SIZE) && (OS_TLS_TBL_SIZE > 0u)
                OS_TLS_TaskSw();
#endif
#endif

                OS_TASK_SW();                          /* Perform a context switch                     */
            }
        }
    }
    
    

    /*@ sched_disabled_addresses(sg, &OSIntNesting, &OSLockNesting) &&
        data_at(&OSIntNesting, INT8U, os_sched_ints(acquired)) *
        data_at(&OSLockNesting, INT8U, os_sched_locks(acquired)) *
        sched_fields_disabled_counter_frame(environment, critical, entered_local, sg, entered,
          cpu_sr, acquired, acquired)
        which implies
        sched_disabled_addresses(sg, &OSIntNesting, &OSLockNesting) &&
        sched_fields_disabled_masked(environment, critical, entered_local, sg, entered,
          cpu_sr, acquired, acquired)
    */
    /*@ sched_disabled_completed_clients(critical, entered) &&
        sched_disabled_entry_source(entered, acquired) && UCOS2_state_inv(sg, acquired) &&
        interrupt_saved_value(mask, cpu_sr) &&
        sched_fields_disabled_masked(environment, critical, entered_local, sg, entered,
          cpu_sr, acquired, acquired) * frame
        which implies
        sched_fields_disabled_restore_pre(environment, critical, entered_local, sg, entered,
          mask, cpu_sr, acquired, acquired, frame)
    */
    /*@ sched_fields_disabled_restore_pre(environment, critical, entered_local, sg, entered,
          mask, cpu_sr, acquired, acquired, frame)
        which implies exists (restore_heap : model),
        sched_fields_heap_cut(sched_fields_disabled_restore_pre(environment, critical, entered_local,
          sg, entered, mask, cpu_sr, acquired, acquired, frame), restore_heap)
    */
    /*@ Given restore_heap */
    OS_EXIT_CRITICAL();
}
