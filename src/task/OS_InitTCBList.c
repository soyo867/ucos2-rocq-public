/*@ Import Coq Require Import Ucos2Verify.lib.stable_glob_vars */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_verify_state_def */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_rules_lib */
/*@ Import Coq Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_full_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_full_prio_spec */
/*@ Import Coq Import UCOS2_C_Rules TaskStateDef */
/*@ Import Coq Local Open Scope Z_scope */
/*@ Import Coq Local Open Scope sac */
/*@ Extern Coq (StableGlobVars :: *) */
/*@ Extern Coq
    (init_tcb_list_full_profile : StableGlobVars -> Prop)
    (init_tcb_list_full_global_addresses : StableGlobVars -> Z -> Z -> Z -> Z -> Prop)
    (init_tcb_list_full_layout : StableGlobVars -> Prop)
    (init_tcb_list_full_field_layout : StableGlobVars -> Prop)
    (init_tcb_list_full_pre : StableGlobVars -> Assertion)
    (init_tcb_list_full_roots : StableGlobVars -> Assertion)
    (init_tcb_list_full_priority_zero : StableGlobVars -> Assertion)
    (init_tcb_list_full_prefix : StableGlobVars -> Z -> Z -> Assertion)
    (init_tcb_list_full_loop_state : StableGlobVars -> Z -> Z -> Assertion)
    (init_tcb_list_full_loop_residual : StableGlobVars -> Z -> Z -> Assertion)
    (init_tcb_list_full_post : StableGlobVars -> Z -> Assertion)
    (mem_clr_pre : Z -> Z -> Assertion)
    (mem_clr_post : Z -> Z -> Assertion)
    (GlobalStrings : (String -> Z) -> Assertion)
*/
static  void  OS_InitTCBList (void)
/*@ With (sg : StableGlobVars) (LitMap : String -> Z)
    Require
      init_tcb_list_full_profile(sg) &&
      init_tcb_list_full_global_addresses(sg, OSTCBTbl, OSTCBPrioTbl, &OSTCBList, &OSTCBFreeList) &&
      init_tcb_list_full_layout(sg) && init_tcb_list_full_field_layout(sg) &&
      init_tcb_list_full_pre(sg) * GlobalStrings(LitMap)
    Ensure
      init_tcb_list_full_profile(sg) &&
      init_tcb_list_full_global_addresses(sg, OSTCBTbl, OSTCBPrioTbl, &OSTCBList, &OSTCBFreeList) &&
      init_tcb_list_full_layout(sg) && init_tcb_list_full_field_layout(sg) &&
      init_tcb_list_full_post(sg, LitMap("?")) * GlobalStrings(LitMap)
*/
{
    INT8U    ix;
    INT8U    ix_next;
    OS_TCB  *ptcb1;
    OS_TCB  *ptcb2;


    
/*@
          init_tcb_list_full_profile(sg) &&
          init_tcb_list_full_global_addresses(sg, OSTCBTbl, OSTCBPrioTbl, &OSTCBList, &OSTCBFreeList) &&
          init_tcb_list_full_layout(sg) && init_tcb_list_full_field_layout(sg) && init_tcb_list_full_pre(sg)
        which implies
          init_tcb_list_full_profile(sg) &&
          init_tcb_list_full_global_addresses(sg, OSTCBTbl, OSTCBPrioTbl, &OSTCBList, &OSTCBFreeList) &&
          init_tcb_list_full_layout(sg) && init_tcb_list_full_field_layout(sg) && sizeof(OS_TCB) == 92 &&
          sizeof(struct os_tcb [22]) == 2024 && sizeof(struct os_tcb *[64]) == 256 &&
          0 <= pointer_offset(OSTCBTbl, 0, OS_TCB) &&
          pointer_offset(pointer_offset(OSTCBTbl, 0, OS_TCB), sizeof(struct os_tcb [22]), INT8U) <= 4294967295 &&
          0 <= pointer_offset(OSTCBPrioTbl, 0, OS_TCB *) &&
          pointer_offset(pointer_offset(OSTCBPrioTbl, 0, OS_TCB *), sizeof(struct os_tcb *[64]), INT8U) <= 4294967295 &&
          mem_clr_pre(pointer_offset(OSTCBTbl, 0, OS_TCB), sizeof(struct os_tcb [22])) *
          mem_clr_pre(pointer_offset(OSTCBPrioTbl, 0, OS_TCB *), sizeof(struct os_tcb *[64])) *
          init_tcb_list_full_roots(sg)
    */
OS_MemClr((INT8U *)&OSTCBTbl[0],     sizeof(OSTCBTbl));      /* Clear all the TCBs                 */
    OS_MemClr((INT8U *)&OSTCBPrioTbl[0], sizeof(OSTCBPrioTbl));  /* Clear the priority table           */
    
/*@
          init_tcb_list_full_profile(sg) &&
          init_tcb_list_full_global_addresses(sg, OSTCBTbl, OSTCBPrioTbl, &OSTCBList, &OSTCBFreeList) &&
          init_tcb_list_full_layout(sg) && init_tcb_list_full_field_layout(sg) &&
          mem_clr_post(pointer_offset(OSTCBTbl, 0, OS_TCB), sizeof(struct os_tcb [22])) *
          mem_clr_post(pointer_offset(OSTCBPrioTbl, 0, OS_TCB *), sizeof(struct os_tcb *[64])) *
          init_tcb_list_full_roots(sg)
        which implies
          init_tcb_list_full_profile(sg) &&
          init_tcb_list_full_global_addresses(sg, OSTCBTbl, OSTCBPrioTbl, &OSTCBList, &OSTCBFreeList) &&
          init_tcb_list_full_layout(sg) && init_tcb_list_full_field_layout(sg) &&
          init_tcb_list_full_loop_state(sg, LitMap("?"), 0)
    */

/*@ Inv Assert
          init_tcb_list_full_profile(sg) &&
          init_tcb_list_full_global_addresses(sg, OSTCBTbl, OSTCBPrioTbl, &OSTCBList, &OSTCBFreeList) &&
          init_tcb_list_full_layout(sg) && init_tcb_list_full_field_layout(sg) && 0 <= ix && ix <= 21 &&
          init_tcb_list_full_loop_state(sg, LitMap("?"), ix) * GlobalStrings(LitMap) *
          undef_data_at(&ix_next, INT8U) * undef_data_at(&ptcb1, OS_TCB *) *
          undef_data_at(&ptcb2, OS_TCB *)
    */
for (ix = 0u; ix < (OS_MAX_TASKS + OS_N_SYS_TASKS - 1u); ix++) {    /* Init. list of free TCBs     */
        ix_next =  ix + 1u;
        ptcb1   = &OSTCBTbl[ix];
        ptcb2   = &OSTCBTbl[ix_next];
        
/*@
              init_tcb_list_full_profile(sg) &&
              init_tcb_list_full_global_addresses(sg, OSTCBTbl, OSTCBPrioTbl, &OSTCBList, &OSTCBFreeList) &&
              init_tcb_list_full_layout(sg) && init_tcb_list_full_field_layout(sg) && 0 <= ix && ix < 21 &&
              ix_next == ix + 1 &&
              ptcb1 == pointer_offset(OSTCBTbl, ix, OS_TCB) &&
              ptcb2 == pointer_offset(OSTCBTbl, ix_next, OS_TCB) &&
              init_tcb_list_full_loop_state(sg, LitMap("?"), ix)
            which implies
              init_tcb_list_full_profile(sg) &&
              init_tcb_list_full_global_addresses(sg, OSTCBTbl, OSTCBPrioTbl, &OSTCBList, &OSTCBFreeList) &&
              init_tcb_list_full_layout(sg) && init_tcb_list_full_field_layout(sg) && 0 <= ix && ix < 21 &&
              ix_next == ix + 1 &&
              ptcb1 == pointer_offset(OSTCBTbl, ix, OS_TCB) &&
              ptcb2 == pointer_offset(OSTCBTbl, ix_next, OS_TCB) &&
              data_at(&ptcb1->OSTCBNext, OS_TCB *, 0) *
              data_at(&ptcb1->OSTCBTaskName, INT8U *, 0) *
              init_tcb_list_full_loop_residual(sg, LitMap("?"), ix)
        */
ptcb1->OSTCBNext = ptcb2;
#if OS_TASK_NAME_EN > 0u
        ptcb1->OSTCBTaskName = (INT8U *)(void *)"?";             /* Unknown name                       */
#endif
    
/*@ Assert
              init_tcb_list_full_profile(sg) &&
              init_tcb_list_full_global_addresses(sg, OSTCBTbl, OSTCBPrioTbl, &OSTCBList, &OSTCBFreeList) &&
              init_tcb_list_full_layout(sg) && init_tcb_list_full_field_layout(sg) && 0 <= ix && ix < 21 &&
              init_tcb_list_full_loop_state(sg, LitMap("?"), ix + 1) * GlobalStrings(LitMap) *
              undef_data_at(&ix_next, INT8U) * undef_data_at(&ptcb1, OS_TCB *) *
              undef_data_at(&ptcb2, OS_TCB *)
        */
}
    ptcb1                   = &OSTCBTbl[ix];
    
/*@
          init_tcb_list_full_profile(sg) &&
          init_tcb_list_full_global_addresses(sg, OSTCBTbl, OSTCBPrioTbl, &OSTCBList, &OSTCBFreeList) &&
          init_tcb_list_full_layout(sg) && init_tcb_list_full_field_layout(sg) && 21 <= ix && ix <= 21 &&
          ptcb1 == pointer_offset(OSTCBTbl, ix, OS_TCB) &&
          init_tcb_list_full_loop_state(sg, LitMap("?"), ix)
        which implies
          init_tcb_list_full_profile(sg) &&
          init_tcb_list_full_global_addresses(sg, OSTCBTbl, OSTCBPrioTbl, &OSTCBList, &OSTCBFreeList) &&
          init_tcb_list_full_layout(sg) && init_tcb_list_full_field_layout(sg) && ix == 21 &&
          ptcb1 == pointer_offset(OSTCBTbl, ix, OS_TCB) &&
          data_at(&ptcb1->OSTCBNext, OS_TCB *, 0) *
          data_at(&ptcb1->OSTCBTaskName, INT8U *, 0) *
          init_tcb_list_full_loop_residual(sg, LitMap("?"), ix)
    */
ptcb1->OSTCBNext        = (OS_TCB *)0;                       /* Last OS_TCB                        */
#if OS_TASK_NAME_EN > 0u
    ptcb1->OSTCBTaskName    = (INT8U *)(void *)"?";              /* Unknown name                       */
#endif
    
/*@ Assert
          init_tcb_list_full_profile(sg) &&
          init_tcb_list_full_global_addresses(sg, OSTCBTbl, OSTCBPrioTbl, &OSTCBList, &OSTCBFreeList) &&
          init_tcb_list_full_layout(sg) && init_tcb_list_full_field_layout(sg) &&
          init_tcb_list_full_loop_state(sg, LitMap("?"), 22) * GlobalStrings(LitMap) *
          undef_data_at(&ix, INT8U) *
          undef_data_at(&ix_next, INT8U) * undef_data_at(&ptcb1, OS_TCB *) *
          undef_data_at(&ptcb2, OS_TCB *)
    */

/*@
          init_tcb_list_full_profile(sg) &&
          init_tcb_list_full_global_addresses(sg, OSTCBTbl, OSTCBPrioTbl, &OSTCBList, &OSTCBFreeList) &&
          init_tcb_list_full_layout(sg) && init_tcb_list_full_field_layout(sg) &&
          init_tcb_list_full_loop_state(sg, LitMap("?"), 22)
        which implies
          init_tcb_list_full_profile(sg) &&
          init_tcb_list_full_global_addresses(sg, OSTCBTbl, OSTCBPrioTbl, &OSTCBList, &OSTCBFreeList) &&
          init_tcb_list_full_layout(sg) && init_tcb_list_full_field_layout(sg) &&
          init_tcb_list_full_prefix(sg, LitMap("?"), 22) * init_tcb_list_full_priority_zero(sg) *
          undef_data_at(&OSTCBList, OS_TCB *) * undef_data_at(&OSTCBFreeList, OS_TCB *)
    */
OSTCBList               = (OS_TCB *)0;                       /* TCB lists initializations          */
    OSTCBFreeList           = &OSTCBTbl[0];
}
