From SimpleC.Verification Require Import VCPrelude.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_sched_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sem_client_sched_case_lib.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_Sched -----*)

Definition OS_Sched_safety_wit_1 :=
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_tcb_stack_field_layout sg )),
  (sem_pend_client_sched_save_output environment critical sg original mask initial observed eid timeout waiting context before retval )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_safety_wit_2 :=
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (returned: OsSchedCallContext) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_tcb_stack_field_layout sg )) (PreH3 : (sem_pend_client_return_source environment critical sg context before scheduled entry )) (PreH4 : (kernel_call_control_rely sg before entry )) (PreH5 : (os_sched_task_body_observation environment critical sg scheduled entry returned final )),
  (sem_pend_client_sched_restore_output environment critical sg original mask initial observed eid timeout waiting returned final )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_entail_wit_1 :=
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_tcb_stack_field_layout sg )),
  (sem_pend_client_sched_save_output environment critical sg original mask initial observed eid timeout waiting context before retval )
|--
  EX (entry_local: (Armv7aContinuation -> Assertion)) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask retval ) ”
  &&  “ (UCOS2_state_inv sg entry ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  “ (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) retval entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
) \/
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_tcb_stack_field_layout sg )),
  (sem_pend_client_sched_save_output environment critical sg original mask initial observed eid timeout waiting context before retval )
|--
  EX (entry_local: (Armv7aContinuation -> Assertion)) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask retval ) ”
  &&  “ (UCOS2_state_inv sg entry ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  “ (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) retval entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
).

Definition OS_Sched_entail_wit_2 :=
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (entry_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) = 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) = 0)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (kernel_tcb_stack_field_layout sg )) (PreH6 : (sem_pend_client_return_source environment critical sg context before scheduled_2 entry_2 )) (PreH7 : (kernel_call_control_rely sg before entry_2 )) (PreH8 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled_2 entry_2 )) (PreH9 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH10 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH11 : (interrupt_saved_value mask cpu_sr )) (PreH12 : (UCOS2_state_inv sg entry_2 )) (PreH13 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH14 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )),
  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (sched_new_priority ((os_sched_group (entry_2))) ((os_sched_rows (entry_2)))) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (os_sched_fields_capsules environment entry_local_2 entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_fields_work_frame sg entry_2 )
|--
  EX (entry_local: (Armv7aContinuation -> Assertion)) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (UCOS2_state_inv sg entry ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  “ (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) ) ”
  &&  “ ((os_sched_ints (entry)) = 0) ”
  &&  “ ((os_sched_locks (entry)) = 0) ”
  &&  “ (0 <= (os_sched_selected (entry))) ”
  &&  “ ((os_sched_selected (entry)) < 64) ”
  &&  “ ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry))) ”
  &&  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
) \/
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (entry_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) = 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) = 0)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (kernel_tcb_stack_field_layout sg )) (PreH6 : (sem_pend_client_return_source environment critical sg context before scheduled_2 entry_2 )) (PreH7 : (kernel_call_control_rely sg before entry_2 )) (PreH8 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled_2 entry_2 )) (PreH9 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH10 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH11 : (interrupt_saved_value mask cpu_sr )) (PreH12 : (UCOS2_state_inv sg entry_2 )) (PreH13 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH14 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )),
  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (sched_new_priority ((os_sched_group (entry_2))) ((os_sched_rows (entry_2)))) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (os_sched_fields_capsules environment entry_local_2 entry_2 )
  **  (os_sched_fields_work_frame sg entry_2 )
|--
  EX (entry_local: (Armv7aContinuation -> Assertion)) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ ((os_sched_table (sg) (entry_2)) = (os_sched_table (sg) (entry))) ”
  &&  “ ((os_sched_counter (entry_2)) = (os_sched_counter (entry))) ”
  &&  “ ((os_sched_old_pointer (sg) (entry_2)) = (os_sched_old_pointer (sg) (entry))) ”
  &&  “ ((os_sched_current (entry_2)) = (os_sched_current (entry))) ”
  &&  “ ((os_sched_locks (entry_2)) = (os_sched_locks (entry))) ”
  &&  “ ((os_sched_ints (entry_2)) = (os_sched_ints (entry))) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (UCOS2_state_inv sg entry ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  “ (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) ) ”
  &&  “ ((os_sched_ints (entry)) = 0) ”
  &&  “ ((os_sched_locks (entry)) = 0) ”
  &&  “ (0 <= (os_sched_selected (entry))) ”
  &&  “ ((os_sched_selected (entry)) < 64) ”
  &&  “ ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry))) ”
  &&  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  (os_sched_fields_work_frame sg entry )
).

Definition OS_Sched_entail_wit_3 :=
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (entry_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_selected (entry_2)) <> (os_sched_current (entry_2)))) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_tcb_stack_field_layout sg )) (PreH4 : (sem_pend_client_return_source environment critical sg context before scheduled_2 entry_2 )) (PreH5 : (kernel_call_control_rely sg before entry_2 )) (PreH6 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled_2 entry_2 )) (PreH7 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH8 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (UCOS2_state_inv sg entry_2 )) (PreH11 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH12 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) (PreH13 : ((os_sched_ints (entry_2)) = 0)) (PreH14 : ((os_sched_locks (entry_2)) = 0)) (PreH15 : (0 <= (os_sched_selected (entry_2)))) (PreH16 : ((os_sched_selected (entry_2)) < 64)) (PreH17 : ((Znth ((os_sched_selected (entry_2))) ((os_sched_table (sg) (entry_2))) (0)) = (os_sched_selected_tcb (sg) (entry_2)))),
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (os_sched_fields_capsules environment entry_local_2 entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry_2)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry_2)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry_2)) (os_sched_table (sg) (entry_2)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)))
  **  (os_sched_fields_work_frame sg entry_2 )
|--
  EX (entry_local: (Armv7aContinuation -> Assertion)) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  (sem_client_sched_switch_input environment entry_local critical sg original mask initial observed eid timeout waiting scheduled cpu_sr entry )
) \/
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (entry_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)) >= 0)) (PreH3 : ((os_sched_selected (entry_2)) <> (os_sched_current (entry_2)))) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (kernel_tcb_stack_field_layout sg )) (PreH6 : (sem_pend_client_return_source environment critical sg context before scheduled_2 entry_2 )) (PreH7 : (kernel_call_control_rely sg before entry_2 )) (PreH8 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled_2 entry_2 )) (PreH9 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH10 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH11 : (interrupt_saved_value mask cpu_sr )) (PreH12 : (UCOS2_state_inv sg entry_2 )) (PreH13 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH14 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) (PreH15 : ((os_sched_ints (entry_2)) = 0)) (PreH16 : ((os_sched_locks (entry_2)) = 0)) (PreH17 : (0 <= (os_sched_selected (entry_2)))) (PreH18 : ((os_sched_selected (entry_2)) < 64)) (PreH19 : ((Znth ((os_sched_selected (entry_2))) ((os_sched_table (sg) (entry_2))) (0)) = (os_sched_selected_tcb (sg) (entry_2)))),
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (os_sched_fields_capsules environment entry_local_2 entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry_2)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry_2)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry_2)) (os_sched_table (sg) (entry_2)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)))
  **  (os_sched_fields_work_frame sg entry_2 )
|--
  EX (entry_local: (Armv7aContinuation -> Assertion)) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  (sem_client_sched_switch_input environment entry_local critical sg original mask initial observed eid timeout waiting scheduled cpu_sr entry )
).

Definition OS_Sched_entail_wit_4_1 :=
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_tcb_stack_field_layout sg )) (PreH3 : (sem_pend_client_return_source environment critical sg context before scheduled_2 entry_2 )) (PreH4 : (kernel_call_control_rely sg before entry_2 )) (PreH5 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled_2 entry_2 )) (PreH6 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH7 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH8 : (interrupt_saved_value mask cpu_sr )) (PreH9 : (os_sched_call_cut sg scheduled_2 entry_2 )),
  (sem_pend_client_sched_body_output environment critical sg original mask initial observed eid timeout waiting scheduled_2 cpu_sr entry_2 )
|--
  EX (final_local: (Armv7aContinuation -> Assertion)) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (os_sched_task_body_observation environment critical sg scheduled entry returned final ) ”
  &&  (sem_pend_client_sched_restore_input environment final_local critical sg original mask initial observed eid timeout waiting returned cpu_sr entry final )
) \/
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_tcb_stack_field_layout sg )) (PreH3 : (sem_pend_client_return_source environment critical sg context before scheduled_2 entry_2 )) (PreH4 : (kernel_call_control_rely sg before entry_2 )) (PreH5 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled_2 entry_2 )) (PreH6 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH7 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH8 : (interrupt_saved_value mask cpu_sr )) (PreH9 : (os_sched_call_cut sg scheduled_2 entry_2 )),
  (sem_pend_client_sched_body_output environment critical sg original mask initial observed eid timeout waiting scheduled_2 cpu_sr entry_2 )
|--
  EX (final_local: (Armv7aContinuation -> Assertion)) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (os_sched_task_body_observation environment critical sg scheduled entry returned final ) ”
  &&  (sem_pend_client_sched_restore_input environment final_local critical sg original mask initial observed eid timeout waiting returned cpu_sr entry final )
).

Definition OS_Sched_entail_wit_4_2 :=
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_selected (entry_2)) = (os_sched_current (entry_2)))) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_tcb_stack_field_layout sg )) (PreH4 : (sem_pend_client_return_source environment critical sg context before scheduled_2 entry_2 )) (PreH5 : (kernel_call_control_rely sg before entry_2 )) (PreH6 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled_2 entry_2 )) (PreH7 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH8 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (UCOS2_state_inv sg entry_2 )) (PreH11 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH12 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) (PreH13 : ((os_sched_ints (entry_2)) = 0)) (PreH14 : ((os_sched_locks (entry_2)) = 0)) (PreH15 : (0 <= (os_sched_selected (entry_2)))) (PreH16 : ((os_sched_selected (entry_2)) < 64)) (PreH17 : ((Znth ((os_sched_selected (entry_2))) ((os_sched_table (sg) (entry_2))) (0)) = (os_sched_selected_tcb (sg) (entry_2)))),
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (os_sched_fields_capsules environment entry_local entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry_2)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry_2)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry_2)) (os_sched_table (sg) (entry_2)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_fields_work_frame sg entry_2 )
|--
  EX (final_local: (Armv7aContinuation -> Assertion)) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (os_sched_task_body_observation environment critical sg scheduled entry returned final ) ”
  &&  (sem_pend_client_sched_restore_input environment final_local critical sg original mask initial observed eid timeout waiting returned cpu_sr entry final )
) \/
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry_2)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (entry_2)) >= 0)) (PreH3 : ((os_sched_selected (entry_2)) = (os_sched_current (entry_2)))) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (kernel_tcb_stack_field_layout sg )) (PreH6 : (sem_pend_client_return_source environment critical sg context before scheduled_2 entry_2 )) (PreH7 : (kernel_call_control_rely sg before entry_2 )) (PreH8 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled_2 entry_2 )) (PreH9 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH10 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH11 : (interrupt_saved_value mask cpu_sr )) (PreH12 : (UCOS2_state_inv sg entry_2 )) (PreH13 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH14 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) (PreH15 : ((os_sched_ints (entry_2)) = 0)) (PreH16 : ((os_sched_locks (entry_2)) = 0)) (PreH17 : (0 <= (os_sched_selected (entry_2)))) (PreH18 : ((os_sched_selected (entry_2)) < 64)) (PreH19 : ((Znth ((os_sched_selected (entry_2))) ((os_sched_table (sg) (entry_2))) (0)) = (os_sched_selected_tcb (sg) (entry_2)))),
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (os_sched_fields_capsules environment entry_local entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry_2)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry_2)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry_2)) (os_sched_table (sg) (entry_2)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_fields_work_frame sg entry_2 )
|--
  EX (final_local: (Armv7aContinuation -> Assertion)) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (os_sched_task_body_observation environment critical sg scheduled entry returned final ) ”
  &&  (sem_pend_client_sched_restore_input environment final_local critical sg original mask initial observed eid timeout waiting returned cpu_sr entry final )
).

Definition OS_Sched_entail_wit_4_3 :=
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) <> 0)) (PreH2 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) = 0)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_tcb_stack_field_layout sg )) (PreH5 : (sem_pend_client_return_source environment critical sg context before scheduled_2 entry_2 )) (PreH6 : (kernel_call_control_rely sg before entry_2 )) (PreH7 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled_2 entry_2 )) (PreH8 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH9 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH10 : (interrupt_saved_value mask cpu_sr )) (PreH11 : (UCOS2_state_inv sg entry_2 )) (PreH12 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH13 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )),
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (os_sched_fields_capsules environment entry_local entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (os_sched_old_high (entry_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_fields_work_frame sg entry_2 )
|--
  EX (final_local: (Armv7aContinuation -> Assertion)) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (os_sched_task_body_observation environment critical sg scheduled entry returned final ) ”
  &&  (sem_pend_client_sched_restore_input environment final_local critical sg original mask initial observed eid timeout waiting returned cpu_sr entry final )
) \/
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry_2)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (entry_2)) >= 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) <> 0)) (PreH4 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) = 0)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (kernel_tcb_stack_field_layout sg )) (PreH7 : (sem_pend_client_return_source environment critical sg context before scheduled_2 entry_2 )) (PreH8 : (kernel_call_control_rely sg before entry_2 )) (PreH9 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled_2 entry_2 )) (PreH10 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH11 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH12 : (interrupt_saved_value mask cpu_sr )) (PreH13 : (UCOS2_state_inv sg entry_2 )) (PreH14 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH15 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )),
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (os_sched_fields_capsules environment entry_local entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (os_sched_old_high (entry_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_fields_work_frame sg entry_2 )
|--
  EX (final_local: (Armv7aContinuation -> Assertion)) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (os_sched_task_body_observation environment critical sg scheduled entry returned final ) ”
  &&  (sem_pend_client_sched_restore_input environment final_local critical sg original mask initial observed eid timeout waiting returned cpu_sr entry final )
).

Definition OS_Sched_entail_wit_4_4 :=
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) <> 0)) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_tcb_stack_field_layout sg )) (PreH4 : (sem_pend_client_return_source environment critical sg context before scheduled_2 entry_2 )) (PreH5 : (kernel_call_control_rely sg before entry_2 )) (PreH6 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled_2 entry_2 )) (PreH7 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH8 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (UCOS2_state_inv sg entry_2 )) (PreH11 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH12 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )),
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (os_sched_fields_capsules environment entry_local entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (os_sched_old_high (entry_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_fields_work_frame sg entry_2 )
|--
  EX (final_local: (Armv7aContinuation -> Assertion)) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (os_sched_task_body_observation environment critical sg scheduled entry returned final ) ”
  &&  (sem_pend_client_sched_restore_input environment final_local critical sg original mask initial observed eid timeout waiting returned cpu_sr entry final )
) \/
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry_2)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (entry_2)) >= 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) <> 0)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (kernel_tcb_stack_field_layout sg )) (PreH6 : (sem_pend_client_return_source environment critical sg context before scheduled_2 entry_2 )) (PreH7 : (kernel_call_control_rely sg before entry_2 )) (PreH8 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled_2 entry_2 )) (PreH9 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH10 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH11 : (interrupt_saved_value mask cpu_sr )) (PreH12 : (UCOS2_state_inv sg entry_2 )) (PreH13 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH14 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )),
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (os_sched_fields_capsules environment entry_local entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (os_sched_old_high (entry_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_fields_work_frame sg entry_2 )
|--
  EX (final_local: (Armv7aContinuation -> Assertion)) (returned: OsSchedCallContext) (final: UCOS2_Verify_State) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State),
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (os_sched_task_body_observation environment critical sg scheduled entry returned final ) ”
  &&  (sem_pend_client_sched_restore_input environment final_local critical sg original mask initial observed eid timeout waiting returned cpu_sr entry final )
).

Definition OS_Sched_return_wit_1 :=
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (returned: OsSchedCallContext) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_tcb_stack_field_layout sg )) (PreH3 : (sem_pend_client_return_source environment critical sg context before scheduled entry )) (PreH4 : (kernel_call_control_rely sg before entry )) (PreH5 : (os_sched_task_body_observation environment critical sg scheduled entry returned final )),
  (sem_pend_client_sched_restore_output environment critical sg original mask initial observed eid timeout waiting returned final )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  (sem_pend_client_sched_output environment critical sg original mask initial observed eid timeout waiting context before )
) \/
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (returned: OsSchedCallContext) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_tcb_stack_field_layout sg )) (PreH3 : (sem_pend_client_return_source environment critical sg context before scheduled entry )) (PreH4 : (kernel_call_control_rely sg before entry )) (PreH5 : (os_sched_task_body_observation environment critical sg scheduled entry returned final )),
  (sem_pend_client_sched_restore_output environment critical sg original mask initial observed eid timeout waiting returned final )
|--
  (sem_pend_client_sched_output environment critical sg original mask initial observed eid timeout waiting context before )
).

Definition OS_Sched_return_wit_1_split_goal_spatial :=
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (returned: OsSchedCallContext) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_tcb_stack_field_layout sg )) (PreH3 : (sem_pend_client_return_source environment critical sg context before scheduled entry )) (PreH4 : (kernel_call_control_rely sg before entry )) (PreH5 : (os_sched_task_body_observation environment critical sg scheduled entry returned final )),
  (sem_pend_client_sched_restore_output environment critical sg original mask initial observed eid timeout waiting returned final )
|--
  (sem_pend_client_sched_output environment critical sg original mask initial observed eid timeout waiting context before )
.

Definition OS_Sched_partial_solve_wit_1 :=
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_tcb_stack_field_layout sg )),
  (sem_pend_client_sched_input environment saved_local critical sg original mask initial observed eid timeout waiting context before )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  (sem_pend_client_sched_input environment saved_local critical sg original mask initial observed eid timeout waiting context before )
.

Definition OS_Sched_partial_solve_wit_2_pure :=
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH2 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_tcb_stack_field_layout sg )) (PreH5 : (sem_pend_client_return_source environment critical sg context before scheduled entry )) (PreH6 : (kernel_call_control_rely sg before entry )) (PreH7 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled entry )) (PreH8 : (task_tcb_init_stack_same_call scheduled context )) (PreH9 : (task_tcb_init_stack_source_preserved context before entry )) (PreH10 : (interrupt_saved_value mask cpu_sr )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (os_sched_call_cut sg scheduled entry )) (PreH13 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
) \/
(
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry)) <= UINT_MAX)) (PreH2 : (cpu_sr <= UINT_MAX)) (PreH3 : ((os_sched_counter (entry)) >= 0)) (PreH4 : (cpu_sr >= 0)) (PreH5 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH6 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (sem_pend_client_return_source environment critical sg context before scheduled entry )) (PreH10 : (kernel_call_control_rely sg before entry )) (PreH11 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled entry )) (PreH12 : (task_tcb_init_stack_same_call scheduled context )) (PreH13 : (task_tcb_init_stack_source_preserved context before entry )) (PreH14 : (interrupt_saved_value mask cpu_sr )) (PreH15 : (UCOS2_state_inv sg entry )) (PreH16 : (os_sched_call_cut sg scheduled entry )) (PreH17 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
).

Definition OS_Sched_partial_solve_wit_2_pure_split_goal_1 :=
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry)) <= UINT_MAX)) (PreH2 : (cpu_sr <= UINT_MAX)) (PreH3 : ((os_sched_counter (entry)) >= 0)) (PreH4 : (cpu_sr >= 0)) (PreH5 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH6 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (kernel_tcb_stack_field_layout sg )) (PreH9 : (sem_pend_client_return_source environment critical sg context before scheduled entry )) (PreH10 : (kernel_call_control_rely sg before entry )) (PreH11 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled entry )) (PreH12 : (task_tcb_init_stack_same_call scheduled context )) (PreH13 : (task_tcb_init_stack_source_preserved context before entry )) (PreH14 : (interrupt_saved_value mask cpu_sr )) (PreH15 : (UCOS2_state_inv sg entry )) (PreH16 : (os_sched_call_cut sg scheduled entry )) (PreH17 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
.

Definition OS_Sched_partial_solve_wit_2_aux :=
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH2 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_tcb_stack_field_layout sg )) (PreH5 : (sem_pend_client_return_source environment critical sg context before scheduled entry )) (PreH6 : (kernel_call_control_rely sg before entry )) (PreH7 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled entry )) (PreH8 : (task_tcb_init_stack_same_call scheduled context )) (PreH9 : (task_tcb_init_stack_source_preserved context before entry )) (PreH10 : (interrupt_saved_value mask cpu_sr )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (os_sched_call_cut sg scheduled entry )) (PreH13 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )),
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
  &&  “ ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0) ”
  &&  “ ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (UCOS2_state_inv sg entry ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  “ (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) ) ”
  &&  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
.

Definition OS_Sched_partial_solve_wit_2 := OS_Sched_partial_solve_wit_2_pure -> OS_Sched_partial_solve_wit_2_aux.

Definition OS_Sched_partial_solve_wit_3 :=
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_tcb_stack_field_layout sg )) (PreH3 : (sem_pend_client_return_source environment critical sg context before scheduled entry )) (PreH4 : (kernel_call_control_rely sg before entry )) (PreH5 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled entry )) (PreH6 : (task_tcb_init_stack_same_call scheduled context )) (PreH7 : (task_tcb_init_stack_source_preserved context before entry )) (PreH8 : (interrupt_saved_value mask cpu_sr )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (os_sched_call_cut sg scheduled entry )) (PreH11 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) (PreH12 : ((os_sched_ints (entry)) = 0)) (PreH13 : ((os_sched_locks (entry)) = 0)) (PreH14 : (0 <= (os_sched_selected (entry)))) (PreH15 : ((os_sched_selected (entry)) < 64)) (PreH16 : ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry)))),
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (UCOS2_state_inv sg entry ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  “ (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) ) ”
  &&  “ ((os_sched_ints (entry)) = 0) ”
  &&  “ ((os_sched_locks (entry)) = 0) ”
  &&  “ (0 <= (os_sched_selected (entry))) ”
  &&  “ ((os_sched_selected (entry)) < 64) ”
  &&  “ ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry))) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + ((os_sched_selected (entry)) * sizeof(PTR)))) # Ptr  |-> (Znth (os_sched_selected (entry)) (os_sched_table (sg) (entry)) 0))
  **  (PtrArray.missing_i ( &( "OSTCBPrioTbl" ) ) (os_sched_selected (entry)) 0 64 (os_sched_table (sg) (entry)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
.

Definition OS_Sched_partial_solve_wit_4 :=
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_tcb_stack_field_layout sg )) (PreH3 : (sem_pend_client_return_source environment critical sg context before scheduled entry )) (PreH4 : (kernel_call_control_rely sg before entry )) (PreH5 : (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled entry )) (PreH6 : (task_tcb_init_stack_same_call scheduled context )) (PreH7 : (task_tcb_init_stack_source_preserved context before entry )) (PreH8 : (interrupt_saved_value mask cpu_sr )) (PreH9 : (os_sched_call_cut sg scheduled entry )),
  (sem_client_sched_switch_input environment entry_local critical sg original mask initial observed eid timeout waiting scheduled cpu_sr entry )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting scheduled entry ) ”
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ”
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ”
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  (sem_client_sched_switch_input environment entry_local critical sg original mask initial observed eid timeout waiting scheduled cpu_sr entry )
.

Definition OS_Sched_partial_solve_wit_5_pure :=
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (returned: OsSchedCallContext) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (final_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_tcb_stack_field_layout sg )) (PreH3 : (sem_pend_client_return_source environment critical sg context before scheduled entry )) (PreH4 : (kernel_call_control_rely sg before entry )) (PreH5 : (os_sched_task_body_observation environment critical sg scheduled entry returned final )),
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (sem_pend_client_sched_restore_input environment final_local critical sg original mask initial observed eid timeout waiting returned cpu_sr entry final )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OS_Sched_partial_solve_wit_5_aux :=
forall (timeout: Z) (eid: Z) (observed: OSEventAbstractState) (waiting: UCOS2_Verify_State) (initial: UCOS2_Verify_State) (before: UCOS2_Verify_State) (mask: Z) (original: OsSchedCallContext) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (returned: OsSchedCallContext) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (final_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_tcb_stack_field_layout sg )) (PreH3 : (sem_pend_client_return_source environment critical sg context before scheduled entry )) (PreH4 : (kernel_call_control_rely sg before entry )) (PreH5 : (os_sched_task_body_observation environment critical sg scheduled entry returned final )),
  (sem_pend_client_sched_restore_input environment final_local critical sg original mask initial observed eid timeout waiting returned cpu_sr entry final )
|--
  “ (cpu_sr = cpu_sr) ”
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  “ (kernel_tcb_stack_field_layout sg ) ”
  &&  “ (sem_pend_client_return_source environment critical sg context before scheduled entry ) ”
  &&  “ (kernel_call_control_rely sg before entry ) ”
  &&  “ (os_sched_task_body_observation environment critical sg scheduled entry returned final ) ”
  &&  (sem_pend_client_sched_restore_input environment final_local critical sg original mask initial observed eid timeout waiting returned cpu_sr entry final )
.

Definition OS_Sched_partial_solve_wit_5 := OS_Sched_partial_solve_wit_5_pure -> OS_Sched_partial_solve_wit_5_aux.

Module Type VC_Correct.


Axiom proof_of_OS_Sched_safety_wit_1 : OS_Sched_safety_wit_1.
Axiom proof_of_OS_Sched_safety_wit_2 : OS_Sched_safety_wit_2.
Axiom proof_of_OS_Sched_entail_wit_1 : OS_Sched_entail_wit_1.
Axiom proof_of_OS_Sched_entail_wit_2 : OS_Sched_entail_wit_2.
Axiom proof_of_OS_Sched_entail_wit_3 : OS_Sched_entail_wit_3.
Axiom proof_of_OS_Sched_entail_wit_4_1 : OS_Sched_entail_wit_4_1.
Axiom proof_of_OS_Sched_entail_wit_4_2 : OS_Sched_entail_wit_4_2.
Axiom proof_of_OS_Sched_entail_wit_4_3 : OS_Sched_entail_wit_4_3.
Axiom proof_of_OS_Sched_entail_wit_4_4 : OS_Sched_entail_wit_4_4.
Axiom proof_of_OS_Sched_return_wit_1 : OS_Sched_return_wit_1.
Axiom proof_of_OS_Sched_partial_solve_wit_1 : OS_Sched_partial_solve_wit_1.
Axiom proof_of_OS_Sched_partial_solve_wit_2_pure : OS_Sched_partial_solve_wit_2_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_2 : OS_Sched_partial_solve_wit_2.
Axiom proof_of_OS_Sched_partial_solve_wit_3 : OS_Sched_partial_solve_wit_3.
Axiom proof_of_OS_Sched_partial_solve_wit_4 : OS_Sched_partial_solve_wit_4.
Axiom proof_of_OS_Sched_partial_solve_wit_5_pure : OS_Sched_partial_solve_wit_5_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_5 : OS_Sched_partial_solve_wit_5.

End VC_Correct.
