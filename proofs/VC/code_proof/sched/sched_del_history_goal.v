Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
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
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_del_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_del_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_Sched -----*)

Definition OS_Sched_safety_wit_1 := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (os_sched_call_cut sg context before )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) ,
  (sched_del_history_save_output environment critical saved_local sg context mask retval before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_safety_wit_2 := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (returned: OsSchedCallContext) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (task_tcb_init_stack_same_call scheduled context )) (PreH4 : (sem_pend_modular_call_history environment critical sg context before scheduled entry )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg scheduled entry )) (PreH8 : (os_sched_c_return (task_stack_call_external (environment)) critical sg entry scheduled returned final )) (PreH9 : (UCOS2_state_inv sg final )) ,
  (sched_del_history_restore_output environment critical saved_local sg returned cpu_sr final )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_entail_wit_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (os_sched_call_cut sg context before )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) ,
  (sched_del_history_save_output environment critical saved_local sg context mask retval before )
|--
  EX (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) retval entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (task_tcb_init_continuation_capsules environment saved_local entry )
  **  (sched_del_continuation_frame sg entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (os_sched_call_cut sg context before )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) ,
  (sched_del_history_save_output environment critical saved_local sg context mask retval before )
|--
  EX (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) retval entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (task_tcb_init_continuation_capsules environment saved_local entry )
  **  (sched_del_continuation_frame sg entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
).

Definition OS_Sched_entail_wit_2 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) = 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) = 0)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH7 : (sem_pend_modular_call_history environment critical sg context before scheduled_2 entry_2 )) (PreH8 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (UCOS2_state_inv sg entry_2 )) (PreH11 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH12 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) ,
  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (sched_new_priority ((os_sched_group (entry_2))) ((os_sched_rows (entry_2)))) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (task_tcb_init_continuation_capsules environment saved_local entry_2 )
  **  (sched_del_continuation_frame sg entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
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
  **  (task_tcb_init_continuation_capsules environment saved_local entry )
  **  (sched_del_continuation_frame sg entry )
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
  **  (os_sched_work_frame sg entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) = 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) = 0)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH7 : (sem_pend_modular_call_history environment critical sg context before scheduled_2 entry_2 )) (PreH8 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (UCOS2_state_inv sg entry_2 )) (PreH11 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH12 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) ,
  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (sched_new_priority ((os_sched_group (entry_2))) ((os_sched_rows (entry_2)))) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (task_tcb_init_continuation_capsules environment saved_local entry_2 )
  **  (sched_del_continuation_frame sg entry_2 )
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ ((os_sched_table (sg) (entry_2)) = (os_sched_table (sg) (entry))) ” 
  &&  “ ((os_sched_counter (entry_2)) = (os_sched_counter (entry))) ” 
  &&  “ ((os_sched_old_pointer (sg) (entry_2)) = (os_sched_old_pointer (sg) (entry))) ” 
  &&  “ ((os_sched_current (entry_2)) = (os_sched_current (entry))) ” 
  &&  “ ((os_sched_locks (entry_2)) = (os_sched_locks (entry))) ” 
  &&  “ ((os_sched_ints (entry_2)) = (os_sched_ints (entry))) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
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
  **  (task_tcb_init_continuation_capsules environment saved_local entry )
  **  (sched_del_continuation_frame sg entry )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  (os_sched_work_frame sg entry )
).

Definition OS_Sched_entail_wit_3 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_selected (entry_2)) <> (os_sched_current (entry_2)))) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH5 : (sem_pend_modular_call_history environment critical sg context before scheduled_2 entry_2 )) (PreH6 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (UCOS2_state_inv sg entry_2 )) (PreH9 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH10 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) (PreH11 : ((os_sched_ints (entry_2)) = 0)) (PreH12 : ((os_sched_locks (entry_2)) = 0)) (PreH13 : (0 <= (os_sched_selected (entry_2)))) (PreH14 : ((os_sched_selected (entry_2)) < 64)) (PreH15 : ((Znth ((os_sched_selected (entry_2))) ((os_sched_table (sg) (entry_2))) (0)) = (os_sched_selected_tcb (sg) (entry_2)))) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (task_tcb_init_continuation_capsules environment saved_local entry_2 )
  **  (sched_del_continuation_frame sg entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry_2)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry_2)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry_2)) (os_sched_table (sg) (entry_2)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  (os_sched_continuation_switch_pre environment critical saved_local mutex_del_stack_resources sg scheduled cpu_sr entry entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)) >= 0)) (PreH3 : ((os_sched_selected (entry_2)) <> (os_sched_current (entry_2)))) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH7 : (sem_pend_modular_call_history environment critical sg context before scheduled_2 entry_2 )) (PreH8 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (UCOS2_state_inv sg entry_2 )) (PreH11 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH12 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) (PreH13 : ((os_sched_ints (entry_2)) = 0)) (PreH14 : ((os_sched_locks (entry_2)) = 0)) (PreH15 : (0 <= (os_sched_selected (entry_2)))) (PreH16 : ((os_sched_selected (entry_2)) < 64)) (PreH17 : ((Znth ((os_sched_selected (entry_2))) ((os_sched_table (sg) (entry_2))) (0)) = (os_sched_selected_tcb (sg) (entry_2)))) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (task_tcb_init_continuation_capsules environment saved_local entry_2 )
  **  (sched_del_continuation_frame sg entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry_2)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry_2)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry_2)) (os_sched_table (sg) (entry_2)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  (os_sched_continuation_switch_pre environment critical saved_local mutex_del_stack_resources sg scheduled cpu_sr entry entry )
).

Definition OS_Sched_entail_wit_4_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH4 : (sem_pend_modular_call_history environment critical sg context before scheduled_2 entry_2 )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg scheduled_2 entry_2 )) ,
  (os_sched_continuation_body_post environment critical saved_local mutex_del_stack_resources sg scheduled_2 cpu_sr entry_2 entry_2 )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State)  (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg entry scheduled returned final ) ” 
  &&  “ (UCOS2_state_inv sg final ) ”
  &&  (sched_del_continuation_restore_input environment critical saved_local sg returned cpu_sr entry final )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH4 : (sem_pend_modular_call_history environment critical sg context before scheduled_2 entry_2 )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg scheduled_2 entry_2 )) ,
  (os_sched_continuation_body_post environment critical saved_local mutex_del_stack_resources sg scheduled_2 cpu_sr entry_2 entry_2 )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State)  (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg entry scheduled returned final ) ” 
  &&  “ (UCOS2_state_inv sg final ) ”
  &&  (sched_del_continuation_restore_input environment critical saved_local sg returned cpu_sr entry final )
).

Definition OS_Sched_entail_wit_4_2 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_selected (entry_2)) = (os_sched_current (entry_2)))) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH5 : (sem_pend_modular_call_history environment critical sg context before scheduled_2 entry_2 )) (PreH6 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (UCOS2_state_inv sg entry_2 )) (PreH9 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH10 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) (PreH11 : ((os_sched_ints (entry_2)) = 0)) (PreH12 : ((os_sched_locks (entry_2)) = 0)) (PreH13 : (0 <= (os_sched_selected (entry_2)))) (PreH14 : ((os_sched_selected (entry_2)) < 64)) (PreH15 : ((Znth ((os_sched_selected (entry_2))) ((os_sched_table (sg) (entry_2))) (0)) = (os_sched_selected_tcb (sg) (entry_2)))) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (task_tcb_init_continuation_capsules environment saved_local entry_2 )
  **  (sched_del_continuation_frame sg entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry_2)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry_2)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry_2)) (os_sched_table (sg) (entry_2)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State)  (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg entry scheduled returned final ) ” 
  &&  “ (UCOS2_state_inv sg final ) ”
  &&  (sched_del_continuation_restore_input environment critical saved_local sg returned cpu_sr entry final )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry_2)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (entry_2)) >= 0)) (PreH3 : ((os_sched_selected (entry_2)) = (os_sched_current (entry_2)))) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH7 : (sem_pend_modular_call_history environment critical sg context before scheduled_2 entry_2 )) (PreH8 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (UCOS2_state_inv sg entry_2 )) (PreH11 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH12 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) (PreH13 : ((os_sched_ints (entry_2)) = 0)) (PreH14 : ((os_sched_locks (entry_2)) = 0)) (PreH15 : (0 <= (os_sched_selected (entry_2)))) (PreH16 : ((os_sched_selected (entry_2)) < 64)) (PreH17 : ((Znth ((os_sched_selected (entry_2))) ((os_sched_table (sg) (entry_2))) (0)) = (os_sched_selected_tcb (sg) (entry_2)))) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (task_tcb_init_continuation_capsules environment saved_local entry_2 )
  **  (sched_del_continuation_frame sg entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry_2)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry_2)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry_2)) (os_sched_table (sg) (entry_2)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State)  (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg entry scheduled returned final ) ” 
  &&  “ (UCOS2_state_inv sg final ) ”
  &&  (sched_del_continuation_restore_input environment critical saved_local sg returned cpu_sr entry final )
).

Definition OS_Sched_entail_wit_4_3 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) <> 0)) (PreH2 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) = 0)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients critical )) (PreH5 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH6 : (sem_pend_modular_call_history environment critical sg context before scheduled_2 entry_2 )) (PreH7 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH8 : (interrupt_saved_value mask cpu_sr )) (PreH9 : (UCOS2_state_inv sg entry_2 )) (PreH10 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH11 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) ,
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (task_tcb_init_continuation_capsules environment saved_local entry_2 )
  **  (sched_del_continuation_frame sg entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (os_sched_old_high (entry_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State)  (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg entry scheduled returned final ) ” 
  &&  “ (UCOS2_state_inv sg final ) ”
  &&  (sched_del_continuation_restore_input environment critical saved_local sg returned cpu_sr entry final )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry_2)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (entry_2)) >= 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) <> 0)) (PreH4 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) = 0)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (kernel_sched_ready_clients critical )) (PreH7 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH8 : (sem_pend_modular_call_history environment critical sg context before scheduled_2 entry_2 )) (PreH9 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH10 : (interrupt_saved_value mask cpu_sr )) (PreH11 : (UCOS2_state_inv sg entry_2 )) (PreH12 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH13 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) ,
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (task_tcb_init_continuation_capsules environment saved_local entry_2 )
  **  (sched_del_continuation_frame sg entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (os_sched_old_high (entry_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State)  (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg entry scheduled returned final ) ” 
  &&  “ (UCOS2_state_inv sg final ) ”
  &&  (sched_del_continuation_restore_input environment critical saved_local sg returned cpu_sr entry final )
).

Definition OS_Sched_entail_wit_4_4 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) <> 0)) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH5 : (sem_pend_modular_call_history environment critical sg context before scheduled_2 entry_2 )) (PreH6 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (UCOS2_state_inv sg entry_2 )) (PreH9 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH10 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) ,
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (task_tcb_init_continuation_capsules environment saved_local entry_2 )
  **  (sched_del_continuation_frame sg entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (os_sched_old_high (entry_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State)  (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg entry scheduled returned final ) ” 
  &&  “ (UCOS2_state_inv sg final ) ”
  &&  (sched_del_continuation_restore_input environment critical saved_local sg returned cpu_sr entry final )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry_2)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (entry_2)) >= 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) <> 0)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH7 : (sem_pend_modular_call_history environment critical sg context before scheduled_2 entry_2 )) (PreH8 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (UCOS2_state_inv sg entry_2 )) (PreH11 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH12 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) ,
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (task_tcb_init_continuation_capsules environment saved_local entry_2 )
  **  (sched_del_continuation_frame sg entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (os_sched_old_high (entry_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State)  (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg entry scheduled returned final ) ” 
  &&  “ (UCOS2_state_inv sg final ) ”
  &&  (sched_del_continuation_restore_input environment critical saved_local sg returned cpu_sr entry final )
).

Definition OS_Sched_return_wit_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (returned: OsSchedCallContext) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (task_tcb_init_stack_same_call scheduled context )) (PreH4 : (sem_pend_modular_call_history environment critical sg context before scheduled entry )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg scheduled entry )) (PreH8 : (os_sched_c_return (task_stack_call_external (environment)) critical sg entry scheduled returned final )) (PreH9 : (UCOS2_state_inv sg final )) ,
  (sched_del_history_restore_output environment critical saved_local sg returned cpu_sr final )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (sched_del_history_return_post environment critical saved_local sg context mask before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (returned: OsSchedCallContext) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (task_tcb_init_stack_same_call scheduled context )) (PreH4 : (sem_pend_modular_call_history environment critical sg context before scheduled entry )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg scheduled entry )) (PreH8 : (os_sched_c_return (task_stack_call_external (environment)) critical sg entry scheduled returned final )) (PreH9 : (UCOS2_state_inv sg final )) ,
  (sched_del_history_restore_output environment critical saved_local sg returned cpu_sr final )
|--
  (sched_del_history_return_post environment critical saved_local sg context mask before )
).

Definition OS_Sched_return_wit_1_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (returned: OsSchedCallContext) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (task_tcb_init_stack_same_call scheduled context )) (PreH4 : (sem_pend_modular_call_history environment critical sg context before scheduled entry )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg scheduled entry )) (PreH8 : (os_sched_c_return (task_stack_call_external (environment)) critical sg entry scheduled returned final )) (PreH9 : (UCOS2_state_inv sg final )) ,
  (sched_del_history_restore_output environment critical saved_local sg returned cpu_sr final )
|--
  (sched_del_history_return_post environment critical saved_local sg context mask before )
.

Definition OS_Sched_partial_solve_wit_1 := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) ,
  (os_sched_continuation_call_pre environment saved_local mutex_del_stack_resources sg context mask before )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  (os_sched_continuation_call_pre environment saved_local mutex_del_stack_resources sg context mask before )
.

Definition OS_Sched_partial_solve_wit_2_pure := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (os_sched_call_cut sg context before )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) ,
  (sched_del_continuation_save_input environment critical saved_local sg context mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_call_cut sg context before ) ”
.

Definition OS_Sched_partial_solve_wit_2_aux := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (os_sched_call_cut sg context before )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) ,
  (sched_del_continuation_save_input environment critical saved_local sg context mask before )
|--
  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_call_cut sg context before ) ” 
  &&  “ (os_sched_call_cut sg context before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ”
  &&  (sched_del_continuation_save_input environment critical saved_local sg context mask before )
.

Definition OS_Sched_partial_solve_wit_2 := OS_Sched_partial_solve_wit_2_pure -> OS_Sched_partial_solve_wit_2_aux.

Definition OS_Sched_partial_solve_wit_3_pure := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH2 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients critical )) (PreH5 : (task_tcb_init_stack_same_call scheduled context )) (PreH6 : (sem_pend_modular_call_history environment critical sg context before scheduled entry )) (PreH7 : (task_tcb_init_stack_source_preserved context before entry )) (PreH8 : (interrupt_saved_value mask cpu_sr )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (os_sched_call_cut sg scheduled entry )) (PreH11 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (task_tcb_init_continuation_capsules environment saved_local entry )
  **  (sched_del_continuation_frame sg entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry)) <= UINT_MAX)) (PreH2 : (cpu_sr <= UINT_MAX)) (PreH3 : ((os_sched_counter (entry)) >= 0)) (PreH4 : (cpu_sr >= 0)) (PreH5 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH6 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (task_tcb_init_stack_same_call scheduled context )) (PreH10 : (sem_pend_modular_call_history environment critical sg context before scheduled entry )) (PreH11 : (task_tcb_init_stack_source_preserved context before entry )) (PreH12 : (interrupt_saved_value mask cpu_sr )) (PreH13 : (UCOS2_state_inv sg entry )) (PreH14 : (os_sched_call_cut sg scheduled entry )) (PreH15 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (task_tcb_init_continuation_capsules environment saved_local entry )
  **  (sched_del_continuation_frame sg entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
).

Definition OS_Sched_partial_solve_wit_3_pure_split_goal_1 := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry)) <= UINT_MAX)) (PreH2 : (cpu_sr <= UINT_MAX)) (PreH3 : ((os_sched_counter (entry)) >= 0)) (PreH4 : (cpu_sr >= 0)) (PreH5 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH6 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (task_tcb_init_stack_same_call scheduled context )) (PreH10 : (sem_pend_modular_call_history environment critical sg context before scheduled entry )) (PreH11 : (task_tcb_init_stack_source_preserved context before entry )) (PreH12 : (interrupt_saved_value mask cpu_sr )) (PreH13 : (UCOS2_state_inv sg entry )) (PreH14 : (os_sched_call_cut sg scheduled entry )) (PreH15 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (task_tcb_init_continuation_capsules environment saved_local entry )
  **  (sched_del_continuation_frame sg entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
.

Definition OS_Sched_partial_solve_wit_3_aux := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH2 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients critical )) (PreH5 : (task_tcb_init_stack_same_call scheduled context )) (PreH6 : (sem_pend_modular_call_history environment critical sg context before scheduled entry )) (PreH7 : (task_tcb_init_stack_source_preserved context before entry )) (PreH8 : (interrupt_saved_value mask cpu_sr )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (os_sched_call_cut sg scheduled entry )) (PreH11 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) ,
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (task_tcb_init_continuation_capsules environment saved_local entry )
  **  (sched_del_continuation_frame sg entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0) ” 
  &&  “ ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) ) ”
  &&  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (task_tcb_init_continuation_capsules environment saved_local entry )
  **  (sched_del_continuation_frame sg entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
.

Definition OS_Sched_partial_solve_wit_3 := OS_Sched_partial_solve_wit_3_pure -> OS_Sched_partial_solve_wit_3_aux.

Definition OS_Sched_partial_solve_wit_4 := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (task_tcb_init_stack_same_call scheduled context )) (PreH4 : (sem_pend_modular_call_history environment critical sg context before scheduled entry )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (UCOS2_state_inv sg entry )) (PreH8 : (os_sched_call_cut sg scheduled entry )) (PreH9 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) (PreH10 : ((os_sched_ints (entry)) = 0)) (PreH11 : ((os_sched_locks (entry)) = 0)) (PreH12 : (0 <= (os_sched_selected (entry)))) (PreH13 : ((os_sched_selected (entry)) < 64)) (PreH14 : ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry)))) ,
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (task_tcb_init_continuation_capsules environment saved_local entry )
  **  (sched_del_continuation_frame sg entry )
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
  **  (os_sched_work_frame sg entry )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
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
  **  (task_tcb_init_continuation_capsules environment saved_local entry )
  **  (sched_del_continuation_frame sg entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_work_frame sg entry )
.

Definition OS_Sched_partial_solve_wit_5_pure := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (task_tcb_init_stack_same_call scheduled context )) (PreH4 : (sem_pend_modular_call_history environment critical sg context before scheduled entry )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg scheduled entry )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_continuation_switch_pre environment critical saved_local mutex_del_stack_resources sg scheduled cpu_sr entry entry )
|--
  “ (kernel_sched_ready_clients critical ) ”
.

Definition OS_Sched_partial_solve_wit_5_aux := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (task_tcb_init_stack_same_call scheduled context )) (PreH4 : (sem_pend_modular_call_history environment critical sg context before scheduled entry )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg scheduled entry )) ,
  (os_sched_continuation_switch_pre environment critical saved_local mutex_del_stack_resources sg scheduled cpu_sr entry entry )
|--
  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ”
  &&  (os_sched_continuation_switch_pre environment critical saved_local mutex_del_stack_resources sg scheduled cpu_sr entry entry )
.

Definition OS_Sched_partial_solve_wit_5 := OS_Sched_partial_solve_wit_5_pure -> OS_Sched_partial_solve_wit_5_aux.

Definition OS_Sched_partial_solve_wit_6_pure := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (returned: OsSchedCallContext) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (task_tcb_init_stack_same_call scheduled context )) (PreH4 : (sem_pend_modular_call_history environment critical sg context before scheduled entry )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg scheduled entry )) (PreH8 : (os_sched_c_return (task_stack_call_external (environment)) critical sg entry scheduled returned final )) (PreH9 : (UCOS2_state_inv sg final )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (sched_del_continuation_restore_input environment critical saved_local sg returned cpu_sr entry final )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OS_Sched_partial_solve_wit_6_aux := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (returned: OsSchedCallContext) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (task_tcb_init_stack_same_call scheduled context )) (PreH4 : (sem_pend_modular_call_history environment critical sg context before scheduled entry )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg scheduled entry )) (PreH8 : (os_sched_c_return (task_stack_call_external (environment)) critical sg entry scheduled returned final )) (PreH9 : (UCOS2_state_inv sg final )) ,
  (sched_del_continuation_restore_input environment critical saved_local sg returned cpu_sr entry final )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (sem_pend_modular_call_history environment critical sg context before scheduled entry ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg entry scheduled returned final ) ” 
  &&  “ (UCOS2_state_inv sg final ) ”
  &&  (sched_del_continuation_restore_input environment critical saved_local sg returned cpu_sr entry final )
.

Definition OS_Sched_partial_solve_wit_6 := OS_Sched_partial_solve_wit_6_pure -> OS_Sched_partial_solve_wit_6_aux.

Definition OS_Sched_which_implies_wit_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) ,
  (os_sched_continuation_call_pre environment saved_local mutex_del_stack_resources sg context mask before )
|--
  “ (os_sched_call_cut sg context before ) ”
  &&  (sched_del_continuation_save_input environment critical saved_local sg context mask before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) ,
  (os_sched_continuation_call_pre environment saved_local mutex_del_stack_resources sg context mask before )
|--
  “ (os_sched_call_cut sg context before ) ”
  &&  (sched_del_continuation_save_input environment critical saved_local sg context mask before )
).

Definition OS_Sched_which_implies_wit_1_split_goal_1 := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) ,
  (os_sched_continuation_call_pre environment saved_local mutex_del_stack_resources sg context mask before )
|--
  “ (os_sched_call_cut sg context before ) ”
.

Definition OS_Sched_which_implies_wit_1_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) ,
  (os_sched_continuation_call_pre environment saved_local mutex_del_stack_resources sg context mask before )
|--
  (sched_del_continuation_save_input environment critical saved_local sg context mask before )
.

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
Axiom proof_of_OS_Sched_partial_solve_wit_3_pure : OS_Sched_partial_solve_wit_3_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_3 : OS_Sched_partial_solve_wit_3.
Axiom proof_of_OS_Sched_partial_solve_wit_4 : OS_Sched_partial_solve_wit_4.
Axiom proof_of_OS_Sched_partial_solve_wit_5_pure : OS_Sched_partial_solve_wit_5_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_5 : OS_Sched_partial_solve_wit_5.
Axiom proof_of_OS_Sched_partial_solve_wit_6_pure : OS_Sched_partial_solve_wit_6_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_6 : OS_Sched_partial_solve_wit_6.
Axiom proof_of_OS_Sched_which_implies_wit_1 : OS_Sched_which_implies_wit_1.

End VC_Correct.
