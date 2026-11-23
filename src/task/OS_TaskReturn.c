/* Single-function annotation carrier; not a standalone translation unit.
 * Rebuild with its environment overlay and annotation_carrier.py compose.
 * The original headers, configuration and callee contracts remain in place.
 */

void  OS_TaskReturn (void)
/*@ With (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources) saved_local
         (completed : TaskDeleteCompletedEnvironment) (sg : StableGlobVars)
         (call : OsSchedCallContext) (mask : Z) (initial : UCOS2_Verify_State) (LitMap : String -> Z)
    Require
      task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
        &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
      os_sched_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSPrioHighRdy, &OSPrioCur,
        &OSTCBHighRdy, OSTCBPrioTbl, &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
      kernel_sched_ready_clients(critical) &&
      task_delete_entry(environment, critical, saved_local, completed, sg, 255, call, mask, initial) * GlobalStrings(LitMap)
    Ensure task_return_post(environment, critical, saved_local, sg, LitMap("?"), call, mask, initial) * GlobalStrings(LitMap)
*/
{
    /*@ task_delete_global_addresses(sg, &OSIntNesting, &OSLockNesting, &OSTCBCur,
          &OSTCBFreeList, &OSTCBList, &OSTaskCtr, OSTCBPrioTbl, &OSRdyGrp, OSRdyTbl, &OSRunning) &&
        task_delete_entry(environment, critical, saved_local, completed, sg, 255, call, mask, initial)
        which implies
        data_at(&OSTCBCur, OS_TCB*, task_delete_current(sg, initial)) *
        wand(task_delete_ptr_cell(&OSTCBCur, task_delete_current(sg, initial)),
          task_delete_entry(environment, critical, saved_local, completed, sg, 255, call, mask, initial))
    */
    OSTaskReturnHook(OSTCBCur) /*@ where frame =
      wand(task_delete_ptr_cell(&OSTCBCur, task_delete_current(sg, initial)),
        task_delete_entry(environment, critical, saved_local, completed, sg, 255, call, mask, initial))
    */;                   /* Call hook to let user decide on what to do        */

    /*@ data_at(&OSTCBCur, OS_TCB*, task_delete_current(sg, initial)) *
        wand(task_delete_ptr_cell(&OSTCBCur, task_delete_current(sg, initial)),
          task_delete_entry(environment, critical, saved_local, completed, sg, 255, call, mask, initial))
        which implies
        task_delete_entry(environment, critical, saved_local, completed, sg, 255, call, mask, initial)
    */

#if OS_TASK_DEL_EN > 0u
    (void)OSTaskDel(OS_PRIO_SELF) /*@ where environment = environment, critical = critical,
      saved_local = saved_local, completed = completed, sg = sg, requested = 255,
      call = call, mask = mask, initial = initial, LitMap = LitMap
    */;                /* Delete task if it accidentally returns!           */
#else
    for (;;) {
        OSTimeDly(OS_TICKS_PER_SEC);
    }
#endif
}
