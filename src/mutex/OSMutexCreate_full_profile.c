/*@ Import Coq From MonadLib Require Import Monad */
/*@ Import Coq From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib */
/*@ Import Coq Import Monad MonadNotation */
/*@ Import Coq Local Open Scope monad_scope */
/*@ Import Coq Require Import Ucos2Verify.lib.stable_glob_vars */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_verify_state_def */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_rules_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.ucos2_verify_inv */
/*@ Import Coq Require Import Ucos2Verify.lib.atomic_ops_lib */
/*@ Import Coq Require Import Ucos2Verify.lib.interrupt */
/*@ Import Coq Require Import Ucos2Verify.lib.event */
/*@ Import Coq Require Import Ucos2Verify.lib.event_pool */
/*@ Import Coq Require Import Ucos2Verify.lib.mutex_create_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_call_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.mutex.spec.full_interrupt_localization */
/*@ Import Coq Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_publication_full_spec */
/*@ Import Coq Import UCOS2_C_Rules MutexCreateFull MutexCreateCall MutexCreateSpatial MutexCreateInitialization MutexCreatePrivateContext */
/*@ Import Coq Import MutexCreatePublicationFull */
/*@ Import Coq Local Open Scope Z_scope */
/*@ Import Coq Local Open Scope sac */

/*@ Extern Coq addr := Z */
/*@ Extern Coq EventID := Z */
/*@ Extern Coq Priority := Z */
/*@ Extern Coq (program :: * => * => *) (list :: * => *) (option :: * => *) (bool :: *) (nat :: *) */
/*@ Extern Coq (true : bool) (false : bool) */
/*@ Extern Coq (StableGlobVars :: *) (UCOS2_Verify_State :: *)
    (Glob_InterruptAbstractState :: *) (Glob_EventAbstractState :: *)
    (EventStorage :: *) (EventPrivateAllocation :: *) (EventField :: *)
    (InterruptPlatformResources :: *) (CriticalRegionResources :: *) (TaskInvocationOrigin :: *) */
/*@ Extern Coq (nil : {A} -> list A) (cons : {A} -> A -> list A -> list A)
    (GlobalStrings_missing : (String -> Z) -> list String -> Assertion)
    (static_literal_bound : UCOS2_Verify_State -> (String -> Z) -> Prop)
    (store_stringLit : Z -> String -> Assertion)
    (UCOS2_full_inv_without_question_mark : StableGlobVars -> UCOS2_Verify_State -> Z -> Assertion)
    (node_residual_without_question_mark : StableGlobVars -> UCOS2_Verify_State -> EventID -> Z -> Assertion) */
/*@ Extern Coq Record UCOS2_Verify_State {
    IntrState : Glob_InterruptAbstractState;
    EventState : Glob_EventAbstractState;
} */
/*@ Extern Coq
    (safeExec : {Sigma} {A} -> (Sigma -> Prop) -> program Sigma A -> (A -> Sigma -> Prop) -> Prop)
    (return : {Sigma} {A} -> A -> program Sigma A)
    (atomic_cmd : {A} -> program UCOS2_Verify_State A -> program (UCOS2_Verify_State -> Prop) A)
    (LastSeen : UCOS2_Verify_State -> (UCOS2_Verify_State -> Prop) -> Prop)
    (coq_prop : Prop -> Assertion)
    (intNesting : Glob_InterruptAbstractState -> Z)
    (valid_stable_glob_vars : StableGlobVars -> Prop)
    (valid_mutex_pcp : StableGlobVars -> Priority -> Prop)
    (mutex_create_priority_input_prop : Priority -> Priority -> Prop)
    (named_event_table_layout : StableGlobVars -> Prop)
    (event_object_layout_prop : StableGlobVars -> EventID -> Prop)
    (event_addr : StableGlobVars -> EventID -> addr)
    (event_pool_addr : StableGlobVars -> EventID -> addr)
    (event_pointer_eq : StableGlobVars -> EventID -> addr -> Prop)
    (hd_error : {A} -> list A -> option A)
    (event_encode_pool_link : StableGlobVars -> option EventID -> addr)
    (os_int_nesting_addr : StableGlobVars -> addr -> Prop)
    (os_event_free_list_addr : StableGlobVars -> addr -> Prop)
    (os_tcb_prio_tbl_addr : StableGlobVars -> addr -> Prop)
    (UCOS2_full_inv : StableGlobVars -> UCOS2_Verify_State -> Assertion)
    (UCOS2_full_state_inv : StableGlobVars -> UCOS2_Verify_State -> Prop)
    (UCOS2_inv_without_os_int_nesting : StableGlobVars -> UCOS2_Verify_State -> Assertion)
    (interrupt_platform_running : InterruptPlatformResources -> nat -> TaskInvocationOrigin -> Z -> Assertion)
    (critical_region_masked : InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars ->
       nat -> TaskInvocationOrigin -> Z -> UCOS2_Verify_State -> Assertion)
    (closed : InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars ->
       nat -> TaskInvocationOrigin -> Z -> UCOS2_Verify_State -> (String -> Z) -> Assertion)
    (acquire_facts : CriticalRegionResources -> StableGlobVars -> nat -> Z -> Z ->
       UCOS2_Verify_State -> UCOS2_Verify_State -> Prop)
    (publication_call_program : CriticalRegionResources -> StableGlobVars -> nat -> Priority -> addr ->
       program UCOS2_Verify_State addr)
    (publication_result_prop : CriticalRegionResources -> StableGlobVars -> nat -> Priority -> addr ->
       UCOS2_Verify_State -> UCOS2_Verify_State -> Z -> Z -> Prop)
    (priority_value : StableGlobVars -> UCOS2_Verify_State -> Priority -> addr)
    (priority_table : StableGlobVars -> UCOS2_Verify_State -> Assertion)
    (priority_table_missing : StableGlobVars -> UCOS2_Verify_State -> Priority -> Assertion)
    (reserved_priority_table : StableGlobVars -> UCOS2_Verify_State -> Priority -> Assertion)
    (reserved_priority_table_missing : StableGlobVars -> UCOS2_Verify_State -> Priority -> Assertion)
    (slot_available : StableGlobVars -> UCOS2_Verify_State -> Priority -> Prop)
    (free_head : StableGlobVars -> UCOS2_Verify_State -> addr)
    (head_residual : StableGlobVars -> UCOS2_Verify_State -> Assertion)
    (node_residual : StableGlobVars -> UCOS2_Verify_State -> EventID -> Assertion)
    (free_head_facts : StableGlobVars -> UCOS2_Verify_State -> EventID -> list EventID -> EventStorage -> Prop)
    (event_storage_rep : bool -> addr -> EventStorage -> Assertion)
    (event_storage_without_field : bool -> addr -> EventStorage -> EventField -> Assertion)
    (EventPtrField : EventField)
    (event_private_storage_rep : StableGlobVars -> EventID -> EventPrivateAllocation -> Assertion)
    (detached_allocation : StableGlobVars -> Glob_EventAbstractState -> EventStorage -> Priority -> EventPrivateAllocation)
    (publication_state : StableGlobVars -> Priority -> EventID -> list EventID -> addr -> UCOS2_Verify_State -> UCOS2_Verify_State)
    (mutex_create_detached_state : StableGlobVars -> Priority -> EventID -> list EventID ->
       UCOS2_Verify_State -> UCOS2_Verify_State)
    (initialization_context : InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars ->
       nat -> TaskInvocationOrigin -> Z -> UCOS2_Verify_State -> Priority -> EventID -> list EventID -> EventStorage -> Z -> Assertion)
    (initialization_padding : addr -> EventStorage -> Assertion)
    (event_wait_list_init_pre : addr -> addr -> Assertion)
    (event_wait_list_init_post : addr -> addr -> Assertion)
*/


OS_EVENT *OSMutexCreate (INT8U prio, INT8U *perr)
/*@ With (platform: InterruptPlatformResources) (critical: CriticalRegionResources)
         (sg: StableGlobVars) (invocation: nat) (origin: TaskInvocationOrigin)
         (mask: Z) (before: UCOS2_Verify_State) (prio_in perr_in: Z) (LitMap: String -> Z) X
    Require coq_prop(static_literal_bound(before, LitMap)) && prio == prio_in && coq_prop(mutex_create_priority_input_prop(prio, prio_in)) && 0 <= prio_in && prio_in <= 255 && perr != 0 &&
      coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
      coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) &&
      coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
      coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
      safeExec(LastSeen(before), atomic_cmd(publication_call_program(critical, sg, invocation, prio_in, LitMap("?"))), X) &&
      data_at(perr, unsigned char, perr_in) *
      interrupt_platform_running(platform, invocation, origin, mask) *
      UCOS2_full_inv_without_question_mark(sg, before, LitMap("?")) *
      store_stringLit(LitMap("?"), "?") * GlobalStrings_missing(LitMap, cons("?", nil))
    Ensure exists (after: UCOS2_Verify_State) (retv errv: Z),
      __return == retv && prio == prio_in && perr != 0 &&
      coq_prop(publication_result_prop(critical, sg, invocation, prio_in, LitMap("?"), before, after, retv, errv)) &&
      safeExec(LastSeen(after), return(retv), X) &&
      data_at(perr, unsigned char, errv) *
      coq_prop(static_literal_bound(after, LitMap)) *
      interrupt_platform_running(platform, invocation, origin, mask) *
      UCOS2_full_inv_without_question_mark(sg, after, LitMap("?")) *
      store_stringLit(LitMap("?"), "?") * GlobalStrings_missing(LitMap, cons("?", nil))
*/
{
    OS_EVENT  *pevent;
#if OS_CRITICAL_METHOD == 3u                               /* Allocate storage for CPU status register */
    OS_CPU_SR  cpu_sr = 0u;
#endif



/*@ coq_prop(static_literal_bound(before, LitMap)) *
        UCOS2_full_inv_without_question_mark(sg, before, LitMap("?")) * store_stringLit(LitMap("?"), "?")
        which implies coq_prop(static_literal_bound(before, LitMap)) * UCOS2_full_inv(sg, before) */

#ifdef OS_SAFETY_CRITICAL
    if (perr == (INT8U *)0) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        return ((OS_EVENT *)0);
    }
#endif

#ifdef OS_SAFETY_CRITICAL_IEC61508
    if (OSSafetyCriticalStartFlag == OS_TRUE) {
        OS_SAFETY_CRITICAL_EXCEPTION();
        *perr = OS_ERR_ILLEGAL_CREATE_RUN_TIME;
        return ((OS_EVENT *)0);
    }
#endif

#if OS_ARG_CHK_EN > 0u
    if (prio != OS_PRIO_MUTEX_CEIL_DIS) {
        if (prio >= OS_LOWEST_PRIO) {
           *perr = OS_ERR_PRIO_INVALID;
            return ((OS_EVENT *)0);
        }
    }
    
#endif
    /*@ coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) * UCOS2_full_inv(sg, before)
        which implies
        0 <= intNesting(before.IntrState) && intNesting(before.IntrState) <= 255 &&
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) * coq_prop(UCOS2_full_state_inv(sg, before)) *
        data_at(&OSIntNesting, unsigned char, intNesting(before.IntrState)) * UCOS2_inv_without_os_int_nesting(sg, before)
    */
    if (OSIntNesting > 0u) {
    /*@ coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) * coq_prop(UCOS2_full_state_inv(sg, before)) *
        data_at(&OSIntNesting, unsigned char, intNesting(before.IntrState)) * UCOS2_inv_without_os_int_nesting(sg, before)
        which implies
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) * UCOS2_full_inv(sg, before)
    */

        
        *perr = OS_ERR_CREATE_ISR;
        return ((OS_EVENT *)0);
    }

    /*@ coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) * coq_prop(UCOS2_full_state_inv(sg, before)) *
        data_at(&OSIntNesting, unsigned char, intNesting(before.IntrState)) * UCOS2_inv_without_os_int_nesting(sg, before)
        which implies
        coq_prop(os_int_nesting_addr(sg, &OSIntNesting)) * UCOS2_full_inv(sg, before)
    */
    /*@ Branch name
        priority_enabled: prio_in != 255;
        priority_disabled: prio_in == 255
    */
    /*@ 0 <= prio_in && prio_in < 63 && coq_prop(valid_stable_glob_vars(sg))
        $ priority_enabled
        which implies
        coq_prop(valid_stable_glob_vars(sg)) * coq_prop(valid_mutex_pcp(sg, prio_in))
        $ priority_enabled
    */
    /*@ prio_in == 255 && coq_prop(valid_stable_glob_vars(sg))
        $ priority_disabled
        which implies
        coq_prop(valid_stable_glob_vars(sg)) * coq_prop(valid_mutex_pcp(sg, prio_in))
        $ priority_disabled
    */
    /*@ coq_prop(static_literal_bound(before, LitMap)) *
        interrupt_platform_running(platform, invocation, origin, mask) * UCOS2_full_inv(sg, before) *
        GlobalStrings_missing(LitMap, cons("?", nil))
        which implies coq_prop(static_literal_bound(before, LitMap)) *
        closed(platform, critical, sg, invocation, origin, mask, before, LitMap) */
    OS_ENTER_CRITICAL();
    /*@ exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 && coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) && coq_prop(mutex_create_priority_input_prop(prio, prio_in)) && coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) && coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_full_inv(sg, entry)
        which implies
        exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          priority_table(sg, entry) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
    */

    
    if (prio != OS_PRIO_MUTEX_CEIL_DIS) {
        
    /*@ exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          priority_table(sg, entry) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        which implies
        exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), priority_value(sg, entry, prio_in)) *
          priority_table_missing(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
    */
        if (OSTCBPrioTbl[prio] != (OS_TCB *)0) {

    /*@ exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 && priority_value(sg, entry, prio_in) != 0 &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), priority_value(sg, entry, prio_in)) *
          priority_table_missing(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        which implies
        exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) && prio_in != 255 && 0 <= prio_in && prio_in < 64 && priority_value(sg, entry, prio_in) != 0 &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_full_inv(sg, entry)
    */
            OS_EXIT_CRITICAL();
            
           *perr = OS_ERR_PRIO_EXIST;
            return ((OS_EVENT *)0);
        }
        OSTCBPrioTbl[prio] = OS_TCB_RESERVED;
    /*@ exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 && priority_value(sg, entry, prio_in) == 0 &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), 1) *
          priority_table_missing(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        which implies
        exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
    */

        
    }

    /*@ exists (entry: UCOS2_Verify_State),
          prio_in == 255 && coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          priority_table(sg, entry) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        $ priority_disabled
        which implies
        exists (entry: UCOS2_Verify_State),
          prio_in == 255 && coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        $ priority_disabled
    */
    pevent = OSEventFreeList;
    if (pevent == (OS_EVENT *)0) {
        if (prio != OS_PRIO_MUTEX_CEIL_DIS) {
            
    /*@ exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 && free_head(sg, entry) == 0 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        which implies
        exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 && free_head(sg, entry) == 0 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), 1) *
          reserved_priority_table_missing(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
    */
            OSTCBPrioTbl[prio] = (OS_TCB *)0;
    /*@ exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 && free_head(sg, entry) == 0 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          data_at(pointer_offset(OSTCBPrioTbl, prio, OS_TCB *), 0) *
          reserved_priority_table_missing(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        which implies
        exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          prio_in != 255 && 0 <= prio_in && prio_in < 64 && free_head(sg, entry) == 0 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          priority_table(sg, entry) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
    */

            
        }

    /*@ exists (entry: UCOS2_Verify_State),
          prio_in == 255 && coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          free_head(sg, entry) == 0 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        $ priority_disabled
        which implies
        exists (entry: UCOS2_Verify_State),
          prio_in == 255 && coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          free_head(sg, entry) == 0 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          priority_table(sg, entry) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        $ priority_disabled
    */
    /*@ exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          free_head(sg, entry) == 0 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          priority_table(sg, entry) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        which implies
        exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) && free_head(sg, entry) == 0 && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) * UCOS2_full_inv(sg, entry)
    */
        OS_EXIT_CRITICAL();
        
       *perr = OS_ERR_PEVENT_NULL;
        return (pevent);
    }
    
    /*@ exists (entry: UCOS2_Verify_State),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) &&
          free_head(sg, entry) != 0 && pevent == free_head(sg, entry) && coq_prop(slot_available(sg, entry, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          head_residual(sg, entry) *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry))
        which implies
        exists (entry: UCOS2_Verify_State) (eid: EventID) (rest: list EventID) (image: EventStorage),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) && coq_prop(slot_available(sg, entry, prio_in)) &&
          coq_prop(free_head_facts(sg, entry, eid, rest, image)) && coq_prop(event_object_layout_prop(sg, eid)) && coq_prop(event_pointer_eq(sg, eid, pevent)) && pevent == free_head(sg, entry) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          node_residual(sg, entry, eid) *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, free_head(sg, entry)) *
          data_at(&pevent->OSEventPtr, void *, event_encode_pool_link(sg, hd_error(rest))) *
          event_storage_without_field(true, pevent, image, EventPtrField)
    */
    OSEventFreeList = (OS_EVENT *)OSEventFreeList->OSEventPtr;
    /*@ exists (entry: UCOS2_Verify_State) (eid: EventID) (rest: list EventID) (image: EventStorage),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) && coq_prop(slot_available(sg, entry, prio_in)) &&
          coq_prop(free_head_facts(sg, entry, eid, rest, image)) && coq_prop(event_object_layout_prop(sg, eid)) && coq_prop(event_pointer_eq(sg, eid, pevent)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          node_residual(sg, entry, eid) *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, event_encode_pool_link(sg, hd_error(rest))) *
          data_at(&pevent->OSEventPtr, void *, event_encode_pool_link(sg, hd_error(rest))) *
          event_storage_without_field(true, pevent, image, EventPtrField)
        which implies
        exists (entry: UCOS2_Verify_State) (eid: EventID) (rest: list EventID) (image: EventStorage),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) && coq_prop(slot_available(sg, entry, prio_in)) &&
          coq_prop(free_head_facts(sg, entry, eid, rest, image)) && coq_prop(event_object_layout_prop(sg, eid)) && coq_prop(event_pointer_eq(sg, eid, pevent)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          node_residual_without_question_mark(sg, entry, eid, LitMap("?")) *
          store_stringLit(LitMap("?"), "?") *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, event_encode_pool_link(sg, hd_error(rest))) *
          undef_data_at(&pevent->OSEventType, unsigned char) *
          undef_data_at(&pevent->OSEventCnt, unsigned short) *
          undef_data_at(&pevent->OSEventPtr, void *) *
          undef_data_at(&pevent->OSEventName, unsigned char *) *
          event_wait_list_init_pre(&pevent->OSEventGrp, &pevent->OSEventTbl[0]) *
          initialization_padding(pevent, image)
    */
    pevent->OSEventCnt  = (INT16U)((INT16U)prio << 8u) | OS_MUTEX_AVAILABLE;
    pevent->OSEventPtr  = (void *)0;
#if OS_EVENT_NAME_EN > 0u
    pevent->OSEventName = (INT8U *)(void *)"?";
#endif
    OS_EventWaitListInit(pevent);
    pevent->OSEventType = OS_EVENT_TYPE_MUTEX;
    /*@ exists (entry: UCOS2_Verify_State) (eid: EventID) (rest: list EventID) (image: EventStorage),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(entry, LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          coq_prop(os_tcb_prio_tbl_addr(sg, OSTCBPrioTbl)) &&
          coq_prop(os_event_free_list_addr(sg, &OSEventFreeList)) && coq_prop(slot_available(sg, entry, prio_in)) &&
          coq_prop(free_head_facts(sg, entry, eid, rest, image)) && coq_prop(event_object_layout_prop(sg, eid)) && coq_prop(event_pointer_eq(sg, eid, pevent)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          node_residual_without_question_mark(sg, entry, eid, LitMap("?")) *
          store_stringLit(LitMap("?"), "?") *
          reserved_priority_table(sg, entry, prio_in) *
          data_at(&OSEventFreeList, struct os_event *, event_encode_pool_link(sg, hd_error(rest))) *
          data_at(&pevent->OSEventType, unsigned char, 4) *
          data_at(&pevent->OSEventCnt, unsigned short, prio_in * 256 + 255) *
          data_at(&pevent->OSEventPtr, void *, 0) *
          data_at(&pevent->OSEventName, unsigned char *, LitMap("?")) *
          event_wait_list_init_post(&pevent->OSEventGrp, &pevent->OSEventTbl[0]) *
          initialization_padding(pevent, image)
        which implies
        exists (entry: UCOS2_Verify_State) (eid: EventID) (rest: list EventID) (image: EventStorage),
          coq_prop(acquire_facts(critical, sg, invocation, mask, cpu_sr, before, entry)) &&
          coq_prop(static_literal_bound(publication_state(sg, prio_in, eid, rest, LitMap("?"), entry), LitMap)) &&
          0 <= prio_in && prio_in <= 255 && coq_prop(valid_mutex_pcp(sg, prio_in)) && intNesting(before.IntrState) <= 0 &&
          coq_prop(UCOS2_full_state_inv(sg, entry)) &&
          coq_prop(valid_stable_glob_vars(sg)) && coq_prop(named_event_table_layout(sg)) &&
          coq_prop(slot_available(sg, entry, prio_in)) &&
          coq_prop(free_head_facts(sg, entry, eid, rest, image)) && coq_prop(event_pointer_eq(sg, eid, pevent)) &&
          coq_prop(mutex_create_priority_input_prop(prio, prio_in)) &&
          critical_region_masked(platform, critical, sg, invocation, origin, cpu_sr, entry) *
          UCOS2_full_inv(sg, publication_state(sg, prio_in, eid, rest, LitMap("?"), entry))
    */
    OS_EXIT_CRITICAL();
    OS_TRACE_MUTEX_CREATE(pevent, pevent->OSEventName);
    *perr = OS_ERR_NONE;
    return (pevent);
}
