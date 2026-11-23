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
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Local Open Scope sac.

(*----- Function OS_Sched -----*)

Definition OS_Sched_safety_wit_1 := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (first_heap: model) (retval: Z) (PreH1 : (os_sched_active_local_stable active )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (os_sched_active_local_stable active )) ,
  (os_sched_active_save_output environment critical local active sg context mask retval before first_heap )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_safety_wit_2 := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (os_sched_active_local_stable active )) (PreH4 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH5 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH8 : (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH9 : (UCOS2_state_inv sg history_final )) (PreH10 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry )) ,
  (os_sched_active_restore_output environment critical history_local active sg history_returned cpu_sr history_entry history_final restore_heap )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (unmap_table_rep sg )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_entail_wit_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (first_heap: model) (retval: Z) (PreH1 : (os_sched_active_local_stable active )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (os_sched_active_local_stable active )) ,
  (os_sched_active_save_output environment critical local active sg context mask retval before first_heap )
  **  (unmap_table_rep sg )
|--
  EX (entry_local: (Armv7aContinuation -> Assertion))  (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask retval before scheduled entry ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) retval entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
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
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (first_heap: model) (retval: Z) (PreH1 : (os_sched_active_local_stable active )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (os_sched_active_local_stable active )) ,
  (os_sched_active_save_output environment critical local active sg context mask retval before first_heap )
  **  (unmap_table_rep sg )
|--
  EX (entry_local: (Armv7aContinuation -> Assertion))  (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask retval before scheduled entry ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) retval entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
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
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (entry_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) = 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) = 0)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (os_sched_active_local_stable active )) (PreH7 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH8 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (UCOS2_state_inv sg entry_2 )) (PreH11 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH12 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) (PreH13 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled_2 entry_2 )) ,
  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (sched_new_priority ((os_sched_group (entry_2))) ((os_sched_rows (entry_2)))) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (os_sched_fields_capsules environment entry_local_2 entry_2 )
  **  (active scheduled_2 entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_fields_work_frame sg entry_2 )
|--
  EX (entry_local: (Armv7aContinuation -> Assertion))  (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
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
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
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
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (entry_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) = 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) = 0)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (os_sched_active_local_stable active )) (PreH7 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH8 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (UCOS2_state_inv sg entry_2 )) (PreH11 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH12 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) (PreH13 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled_2 entry_2 )) ,
  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (sched_new_priority ((os_sched_group (entry_2))) ((os_sched_rows (entry_2)))) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (os_sched_fields_capsules environment entry_local_2 entry_2 )
  **  (active scheduled_2 entry_2 )
  **  (os_sched_fields_work_frame sg entry_2 )
|--
  EX (entry_local: (Armv7aContinuation -> Assertion))  (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ ((os_sched_table (sg) (entry_2)) = (os_sched_table (sg) (entry))) ” 
  &&  “ ((os_sched_counter (entry_2)) = (os_sched_counter (entry))) ” 
  &&  “ ((os_sched_old_pointer (sg) (entry_2)) = (os_sched_old_pointer (sg) (entry))) ” 
  &&  “ ((os_sched_current (entry_2)) = (os_sched_current (entry))) ” 
  &&  “ ((os_sched_locks (entry_2)) = (os_sched_locks (entry))) ” 
  &&  “ ((os_sched_ints (entry_2)) = (os_sched_ints (entry))) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
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
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  (os_sched_fields_work_frame sg entry )
).

Definition OS_Sched_entail_wit_3 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (entry_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_selected (entry_2)) <> (os_sched_current (entry_2)))) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (os_sched_active_local_stable active )) (PreH5 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH6 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (UCOS2_state_inv sg entry_2 )) (PreH9 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH10 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) (PreH11 : ((os_sched_ints (entry_2)) = 0)) (PreH12 : ((os_sched_locks (entry_2)) = 0)) (PreH13 : (0 <= (os_sched_selected (entry_2)))) (PreH14 : ((os_sched_selected (entry_2)) < 64)) (PreH15 : ((Znth ((os_sched_selected (entry_2))) ((os_sched_table (sg) (entry_2))) (0)) = (os_sched_selected_tcb (sg) (entry_2)))) (PreH16 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled_2 entry_2 )) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (os_sched_fields_capsules environment entry_local_2 entry_2 )
  **  (active scheduled_2 entry_2 )
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
  EX (entry_local: (Armv7aContinuation -> Assertion))  (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry ) ”
  &&  (os_sched_active_switch_pre environment critical entry_local active sg scheduled cpu_sr entry entry )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (entry_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)) >= 0)) (PreH3 : ((os_sched_selected (entry_2)) <> (os_sched_current (entry_2)))) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (os_sched_active_local_stable active )) (PreH7 : (task_tcb_init_stack_same_call scheduled_2 context )) (PreH8 : (task_tcb_init_stack_source_preserved context before entry_2 )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (UCOS2_state_inv sg entry_2 )) (PreH11 : (os_sched_call_cut sg scheduled_2 entry_2 )) (PreH12 : (task_stack_live_coverage (TskState (entry_2)) (task_stack_call_active_key (scheduled_2)) )) (PreH13 : ((os_sched_ints (entry_2)) = 0)) (PreH14 : ((os_sched_locks (entry_2)) = 0)) (PreH15 : (0 <= (os_sched_selected (entry_2)))) (PreH16 : ((os_sched_selected (entry_2)) < 64)) (PreH17 : ((Znth ((os_sched_selected (entry_2))) ((os_sched_table (sg) (entry_2))) (0)) = (os_sched_selected_tcb (sg) (entry_2)))) (PreH18 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled_2 entry_2 )) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled_2)) (os_sched_call_origin (scheduled_2)) cpu_sr entry_2 )
  **  (task_tcb_init_stack_context environment scheduled_2 )
  **  (os_sched_fields_capsules environment entry_local_2 entry_2 )
  **  (active scheduled_2 entry_2 )
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
  EX (entry_local: (Armv7aContinuation -> Assertion))  (entry: UCOS2_Verify_State)  (scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry ) ”
  &&  (os_sched_active_switch_pre environment critical entry_local active sg scheduled cpu_sr entry entry )
).

Definition OS_Sched_entail_wit_4_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (switch_heap: model) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (os_sched_active_local_stable active )) (PreH4 : (task_tcb_init_stack_same_call scheduled context )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg scheduled entry )) (PreH8 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry )) ,
  (os_sched_active_switch_output environment critical entry_local active sg scheduled cpu_sr entry entry switch_heap )
|--
  EX (history_local: (Armv7aContinuation -> Assertion))  (history_returned: OsSchedCallContext)  (history_final: UCOS2_Verify_State)  (history_entry: UCOS2_Verify_State)  (history_scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final ) ” 
  &&  “ (UCOS2_state_inv sg history_final ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  (os_sched_active_restore_input environment critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (switch_heap: model) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (os_sched_active_local_stable active )) (PreH4 : (task_tcb_init_stack_same_call scheduled context )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg scheduled entry )) (PreH8 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry )) ,
  (os_sched_active_switch_output environment critical entry_local active sg scheduled cpu_sr entry entry switch_heap )
|--
  EX (history_local: (Armv7aContinuation -> Assertion))  (history_returned: OsSchedCallContext)  (history_final: UCOS2_Verify_State)  (history_entry: UCOS2_Verify_State)  (history_scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final ) ” 
  &&  “ (UCOS2_state_inv sg history_final ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  (os_sched_active_restore_input environment critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_entail_wit_4_2 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_selected (entry)) = (os_sched_current (entry)))) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (os_sched_active_local_stable active )) (PreH5 : (task_tcb_init_stack_same_call scheduled context )) (PreH6 : (task_tcb_init_stack_source_preserved context before entry )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (UCOS2_state_inv sg entry )) (PreH9 : (os_sched_call_cut sg scheduled entry )) (PreH10 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) (PreH11 : ((os_sched_ints (entry)) = 0)) (PreH12 : ((os_sched_locks (entry)) = 0)) (PreH13 : (0 <= (os_sched_selected (entry)))) (PreH14 : ((os_sched_selected (entry)) < 64)) (PreH15 : ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry)))) (PreH16 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry )) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry)) (os_sched_table (sg) (entry)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
|--
  EX (history_local: (Armv7aContinuation -> Assertion))  (history_returned: OsSchedCallContext)  (history_final: UCOS2_Verify_State)  (history_entry: UCOS2_Verify_State)  (history_scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final ) ” 
  &&  “ (UCOS2_state_inv sg history_final ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  (os_sched_active_restore_input environment critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (entry)) >= 0)) (PreH3 : ((os_sched_selected (entry)) = (os_sched_current (entry)))) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (os_sched_active_local_stable active )) (PreH7 : (task_tcb_init_stack_same_call scheduled context )) (PreH8 : (task_tcb_init_stack_source_preserved context before entry )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (UCOS2_state_inv sg entry )) (PreH11 : (os_sched_call_cut sg scheduled entry )) (PreH12 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) (PreH13 : ((os_sched_ints (entry)) = 0)) (PreH14 : ((os_sched_locks (entry)) = 0)) (PreH15 : (0 <= (os_sched_selected (entry)))) (PreH16 : ((os_sched_selected (entry)) < 64)) (PreH17 : ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry)))) (PreH18 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry )) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth (os_sched_selected (entry)) (os_sched_table (sg) (entry)) 0))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
|--
  EX (history_local: (Armv7aContinuation -> Assertion))  (history_returned: OsSchedCallContext)  (history_final: UCOS2_Verify_State)  (history_entry: UCOS2_Verify_State)  (history_scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final ) ” 
  &&  “ (UCOS2_state_inv sg history_final ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  (os_sched_active_restore_input environment critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_entail_wit_4_3 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) <> 0)) (PreH2 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients critical )) (PreH5 : (os_sched_active_local_stable active )) (PreH6 : (task_tcb_init_stack_same_call scheduled context )) (PreH7 : (task_tcb_init_stack_source_preserved context before entry )) (PreH8 : (interrupt_saved_value mask cpu_sr )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (os_sched_call_cut sg scheduled entry )) (PreH11 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) (PreH12 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry )) ,
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
|--
  EX (history_local: (Armv7aContinuation -> Assertion))  (history_returned: OsSchedCallContext)  (history_final: UCOS2_Verify_State)  (history_entry: UCOS2_Verify_State)  (history_scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final ) ” 
  &&  “ (UCOS2_state_inv sg history_final ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  (os_sched_active_restore_input environment critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (entry)) >= 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) <> 0)) (PreH4 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (kernel_sched_ready_clients critical )) (PreH7 : (os_sched_active_local_stable active )) (PreH8 : (task_tcb_init_stack_same_call scheduled context )) (PreH9 : (task_tcb_init_stack_source_preserved context before entry )) (PreH10 : (interrupt_saved_value mask cpu_sr )) (PreH11 : (UCOS2_state_inv sg entry )) (PreH12 : (os_sched_call_cut sg scheduled entry )) (PreH13 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) (PreH14 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry )) ,
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
|--
  EX (history_local: (Armv7aContinuation -> Assertion))  (history_returned: OsSchedCallContext)  (history_final: UCOS2_Verify_State)  (history_entry: UCOS2_Verify_State)  (history_scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final ) ” 
  &&  “ (UCOS2_state_inv sg history_final ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  (os_sched_active_restore_input environment critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_entail_wit_4_4 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) <> 0)) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (os_sched_active_local_stable active )) (PreH5 : (task_tcb_init_stack_same_call scheduled context )) (PreH6 : (task_tcb_init_stack_source_preserved context before entry )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (UCOS2_state_inv sg entry )) (PreH9 : (os_sched_call_cut sg scheduled entry )) (PreH10 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) (PreH11 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry )) ,
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
|--
  EX (history_local: (Armv7aContinuation -> Assertion))  (history_returned: OsSchedCallContext)  (history_final: UCOS2_Verify_State)  (history_entry: UCOS2_Verify_State)  (history_scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final ) ” 
  &&  “ (UCOS2_state_inv sg history_final ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  (os_sched_active_restore_input environment critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (entry)) >= 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) <> 0)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (os_sched_active_local_stable active )) (PreH7 : (task_tcb_init_stack_same_call scheduled context )) (PreH8 : (task_tcb_init_stack_source_preserved context before entry )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (UCOS2_state_inv sg entry )) (PreH11 : (os_sched_call_cut sg scheduled entry )) (PreH12 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) (PreH13 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry )) ,
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
|--
  EX (history_local: (Armv7aContinuation -> Assertion))  (history_returned: OsSchedCallContext)  (history_final: UCOS2_Verify_State)  (history_entry: UCOS2_Verify_State)  (history_scheduled: OsSchedCallContext) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final ) ” 
  &&  “ (UCOS2_state_inv sg history_final ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  (os_sched_active_restore_input environment critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_return_wit_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (os_sched_active_local_stable active )) (PreH4 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH5 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH8 : (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH9 : (UCOS2_state_inv sg history_final )) (PreH10 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry )) ,
  (os_sched_active_restore_output environment critical history_local active sg history_returned cpu_sr history_entry history_final restore_heap )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_sched_active_history_return_post environment critical active sg context mask before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (os_sched_active_local_stable active )) (PreH4 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH5 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH8 : (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH9 : (UCOS2_state_inv sg history_final )) (PreH10 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry )) ,
  (os_sched_active_restore_output environment critical history_local active sg history_returned cpu_sr history_entry history_final restore_heap )
  **  (unmap_table_rep sg )
|--
  (os_sched_active_history_return_post environment critical active sg context mask before )
).

Definition OS_Sched_return_wit_1_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (os_sched_active_local_stable active )) (PreH4 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH5 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH8 : (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH9 : (UCOS2_state_inv sg history_final )) (PreH10 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry )) ,
  (os_sched_active_restore_output environment critical history_local active sg history_returned cpu_sr history_entry history_final restore_heap )
  **  (unmap_table_rep sg )
|--
  (os_sched_active_history_return_post environment critical active sg context mask before )
.

Definition OS_Sched_partial_solve_wit_1_pure := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (os_sched_active_local_stable active )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  (os_sched_active_call_pre environment local active sg context mask before )
|--
  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ”
.

Definition OS_Sched_partial_solve_wit_1_aux := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (os_sched_active_local_stable active )) ,
  (os_sched_active_call_pre environment local active sg context mask before )
|--
  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ”
  &&  (os_sched_active_call_pre environment local active sg context mask before )
.

Definition OS_Sched_partial_solve_wit_1 := OS_Sched_partial_solve_wit_1_pure -> OS_Sched_partial_solve_wit_1_aux.

Definition OS_Sched_partial_solve_wit_2 := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (os_sched_active_local_stable active )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (os_sched_active_local_stable active )) ,
  (os_sched_active_save_input environment critical local active sg context mask before )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_active_local_stable active ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ”
  &&  (os_sched_active_save_input environment critical local active sg context mask before )
  **  (unmap_table_rep sg )
.

Definition OS_Sched_partial_solve_wit_3 := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (first_heap: model) (PreH1 : (os_sched_active_local_stable active )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (os_sched_active_local_stable active )) ,
  (os_sched_active_heap_cut (os_sched_active_save_input (environment) (critical) (local) (active) (sg) (context) (mask) (before)) first_heap )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_active_local_stable active ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ”
  &&  (os_sched_active_heap_cut (os_sched_active_save_input (environment) (critical) (local) (active) (sg) (context) (mask) (before)) first_heap )
  **  (unmap_table_rep sg )
.

Definition OS_Sched_partial_solve_wit_4_pure := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH2 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients critical )) (PreH5 : (os_sched_active_local_stable active )) (PreH6 : (task_tcb_init_stack_same_call scheduled context )) (PreH7 : (task_tcb_init_stack_source_preserved context before entry )) (PreH8 : (interrupt_saved_value mask cpu_sr )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (os_sched_call_cut sg scheduled entry )) (PreH11 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) (PreH12 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
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
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry)) <= UINT_MAX)) (PreH2 : (cpu_sr <= UINT_MAX)) (PreH3 : ((os_sched_counter (entry)) >= 0)) (PreH4 : (cpu_sr >= 0)) (PreH5 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH6 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (os_sched_active_local_stable active )) (PreH10 : (task_tcb_init_stack_same_call scheduled context )) (PreH11 : (task_tcb_init_stack_source_preserved context before entry )) (PreH12 : (interrupt_saved_value mask cpu_sr )) (PreH13 : (UCOS2_state_inv sg entry )) (PreH14 : (os_sched_call_cut sg scheduled entry )) (PreH15 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) (PreH16 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
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

Definition OS_Sched_partial_solve_wit_4_pure_split_goal_1 := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry)) <= UINT_MAX)) (PreH2 : (cpu_sr <= UINT_MAX)) (PreH3 : ((os_sched_counter (entry)) >= 0)) (PreH4 : (cpu_sr >= 0)) (PreH5 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH6 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (os_sched_active_local_stable active )) (PreH10 : (task_tcb_init_stack_same_call scheduled context )) (PreH11 : (task_tcb_init_stack_source_preserved context before entry )) (PreH12 : (interrupt_saved_value mask cpu_sr )) (PreH13 : (UCOS2_state_inv sg entry )) (PreH14 : (os_sched_call_cut sg scheduled entry )) (PreH15 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) (PreH16 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
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

Definition OS_Sched_partial_solve_wit_4_aux := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH2 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (kernel_sched_ready_clients critical )) (PreH5 : (os_sched_active_local_stable active )) (PreH6 : (task_tcb_init_stack_same_call scheduled context )) (PreH7 : (task_tcb_init_stack_source_preserved context before entry )) (PreH8 : (interrupt_saved_value mask cpu_sr )) (PreH9 : (UCOS2_state_inv sg entry )) (PreH10 : (os_sched_call_cut sg scheduled entry )) (PreH11 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) (PreH12 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry )) ,
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
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
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry ) ”
  &&  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry)))
  **  (os_sched_fields_work_frame sg entry )
.

Definition OS_Sched_partial_solve_wit_4 := OS_Sched_partial_solve_wit_4_pure -> OS_Sched_partial_solve_wit_4_aux.

Definition OS_Sched_partial_solve_wit_5 := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (os_sched_active_local_stable active )) (PreH4 : (task_tcb_init_stack_same_call scheduled context )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (UCOS2_state_inv sg entry )) (PreH8 : (os_sched_call_cut sg scheduled entry )) (PreH9 : (task_stack_live_coverage (TskState (entry)) (task_stack_call_active_key (scheduled)) )) (PreH10 : ((os_sched_ints (entry)) = 0)) (PreH11 : ((os_sched_locks (entry)) = 0)) (PreH12 : (0 <= (os_sched_selected (entry)))) (PreH13 : ((os_sched_selected (entry)) < 64)) (PreH14 : ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry)))) (PreH15 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry )) ,
  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
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
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
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
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + ((os_sched_selected (entry)) * sizeof(PTR)))) # Ptr  |-> (Znth (os_sched_selected (entry)) (os_sched_table (sg) (entry)) 0))
  **  (PtrArray.missing_i ( &( "OSTCBPrioTbl" ) ) (os_sched_selected (entry)) 0 64 (os_sched_table (sg) (entry)) )
  **  (critical_region_masked (task_stack_call_platform (environment)) critical sg (os_sched_call_invocation (scheduled)) (os_sched_call_origin (scheduled)) cpu_sr entry )
  **  (task_tcb_init_stack_context environment scheduled )
  **  (os_sched_fields_capsules environment entry_local entry )
  **  (active scheduled entry )
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

Definition OS_Sched_partial_solve_wit_6 := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (os_sched_active_local_stable active )) (PreH4 : (task_tcb_init_stack_same_call scheduled context )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg scheduled entry )) (PreH8 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry )) ,
  (os_sched_active_switch_pre environment critical entry_local active sg scheduled cpu_sr entry entry )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry ) ”
  &&  (os_sched_active_switch_pre environment critical entry_local active sg scheduled cpu_sr entry entry )
.

Definition OS_Sched_partial_solve_wit_7_pure := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (switch_heap: model) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (os_sched_active_local_stable active )) (PreH4 : (task_tcb_init_stack_same_call scheduled context )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg scheduled entry )) (PreH8 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_active_heap_cut (os_sched_active_switch_pre (environment) (critical) (entry_local) (active) (sg) (scheduled) (cpu_sr) (entry) (entry)) switch_heap )
|--
  “ (kernel_sched_ready_clients critical ) ”
.

Definition OS_Sched_partial_solve_wit_7_aux := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (switch_heap: model) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (os_sched_active_local_stable active )) (PreH4 : (task_tcb_init_stack_same_call scheduled context )) (PreH5 : (task_tcb_init_stack_source_preserved context before entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg scheduled entry )) (PreH8 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry )) ,
  (os_sched_active_heap_cut (os_sched_active_switch_pre (environment) (critical) (entry_local) (active) (sg) (scheduled) (cpu_sr) (entry) (entry)) switch_heap )
|--
  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg scheduled entry ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before scheduled entry ) ”
  &&  (os_sched_active_heap_cut (os_sched_active_switch_pre (environment) (critical) (entry_local) (active) (sg) (scheduled) (cpu_sr) (entry) (entry)) switch_heap )
.

Definition OS_Sched_partial_solve_wit_7 := OS_Sched_partial_solve_wit_7_pure -> OS_Sched_partial_solve_wit_7_aux.

Definition OS_Sched_partial_solve_wit_8 := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (os_sched_active_local_stable active )) (PreH4 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH5 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH8 : (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH9 : (UCOS2_state_inv sg history_final )) (PreH10 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry )) ,
  (os_sched_active_restore_input environment critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final ) ” 
  &&  “ (UCOS2_state_inv sg history_final ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  (os_sched_active_restore_input environment critical history_local active sg history_returned cpu_sr history_entry history_final )
  **  (unmap_table_rep sg )
.

Definition OS_Sched_partial_solve_wit_9_pure := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (os_sched_active_local_stable active )) (PreH4 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH5 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH8 : (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH9 : (UCOS2_state_inv sg history_final )) (PreH10 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_active_heap_cut (os_sched_active_restore_input (environment) (critical) (history_local) (active) (sg) (history_returned) (cpu_sr) (history_entry) (history_final)) restore_heap )
  **  (unmap_table_rep sg )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OS_Sched_partial_solve_wit_9_aux := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (history_scheduled: OsSchedCallContext) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (restore_heap: model) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (kernel_sched_ready_clients critical )) (PreH3 : (os_sched_active_local_stable active )) (PreH4 : (task_tcb_init_stack_same_call history_scheduled context )) (PreH5 : (task_tcb_init_stack_source_preserved context before history_entry )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (os_sched_call_cut sg history_scheduled history_entry )) (PreH8 : (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final )) (PreH9 : (UCOS2_state_inv sg history_final )) (PreH10 : (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry )) ,
  (os_sched_active_heap_cut (os_sched_active_restore_input (environment) (critical) (history_local) (active) (sg) (history_returned) (cpu_sr) (history_entry) (history_final)) restore_heap )
  **  (unmap_table_rep sg )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable active ) ” 
  &&  “ (task_tcb_init_stack_same_call history_scheduled context ) ” 
  &&  “ (task_tcb_init_stack_source_preserved context before history_entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_call_cut sg history_scheduled history_entry ) ” 
  &&  “ (os_sched_c_return (task_stack_call_external (environment)) critical sg history_entry history_scheduled history_returned history_final ) ” 
  &&  “ (UCOS2_state_inv sg history_final ) ” 
  &&  “ (os_sched_continuation_save_effect environment critical sg context mask cpu_sr before history_scheduled history_entry ) ”
  &&  (os_sched_active_heap_cut (os_sched_active_restore_input (environment) (critical) (history_local) (active) (sg) (history_returned) (cpu_sr) (history_entry) (history_final)) restore_heap )
  **  (unmap_table_rep sg )
.

Definition OS_Sched_partial_solve_wit_9 := OS_Sched_partial_solve_wit_9_pure -> OS_Sched_partial_solve_wit_9_aux.

Definition OS_Sched_which_implies_wit_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (kernel_sched_ready_clients critical )) (PreH2 : (os_sched_active_local_stable active )) ,
  (os_sched_active_call_pre environment local active sg context mask before )
|--
  “ (os_sched_active_local_stable active ) ”
  &&  (os_sched_active_save_input environment critical local active sg context mask before )
  **  (unmap_table_rep sg )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (kernel_sched_ready_clients critical )) (PreH2 : (os_sched_active_local_stable active )) ,
  (os_sched_active_call_pre environment local active sg context mask before )
|--
  (os_sched_active_save_input environment critical local active sg context mask before )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_which_implies_wit_1_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (kernel_sched_ready_clients critical )) (PreH2 : (os_sched_active_local_stable active )) ,
  (os_sched_active_call_pre environment local active sg context mask before )
|--
  (os_sched_active_save_input environment critical local active sg context mask before )
  **  (unmap_table_rep sg )
.

Definition OS_Sched_which_implies_wit_2 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) ,
  (os_sched_active_save_input environment critical local active sg context mask before )
|--
  EX (first_heap: model) ,
  (os_sched_active_heap_cut (os_sched_active_save_input (environment) (critical) (local) (active) (sg) (context) (mask) (before)) first_heap )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) ,
  (os_sched_active_save_input environment critical local active sg context mask before )
|--
  EX (first_heap: model) ,
  (os_sched_active_heap_cut (os_sched_active_save_input (environment) (critical) (local) (active) (sg) (context) (mask) (before)) first_heap )
).

Definition OS_Sched_which_implies_wit_3 := 
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) ,
  (os_sched_active_switch_pre environment critical entry_local active sg scheduled cpu_sr entry entry )
|--
  EX (switch_heap: model) ,
  (os_sched_active_heap_cut (os_sched_active_switch_pre (environment) (critical) (entry_local) (active) (sg) (scheduled) (cpu_sr) (entry) (entry)) switch_heap )
) \/
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (scheduled: OsSchedCallContext) (entry: UCOS2_Verify_State) (entry_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) ,
  (os_sched_active_switch_pre environment critical entry_local active sg scheduled cpu_sr entry entry )
|--
  EX (switch_heap: model) ,
  (os_sched_active_heap_cut (os_sched_active_switch_pre (environment) (critical) (entry_local) (active) (sg) (scheduled) (cpu_sr) (entry) (entry)) switch_heap )
).

Definition OS_Sched_which_implies_wit_4 := 
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) ,
  (os_sched_active_restore_input environment critical history_local active sg history_returned cpu_sr history_entry history_final )
|--
  EX (restore_heap: model) ,
  (os_sched_active_heap_cut (os_sched_active_restore_input (environment) (critical) (history_local) (active) (sg) (history_returned) (cpu_sr) (history_entry) (history_final)) restore_heap )
) \/
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (active: (OsSchedCallContext -> (UCOS2_Verify_State -> Assertion))) (environment: TaskStackCallEnvironment) (history_returned: OsSchedCallContext) (history_entry: UCOS2_Verify_State) (history_final: UCOS2_Verify_State) (history_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) ,
  (os_sched_active_restore_input environment critical history_local active sg history_returned cpu_sr history_entry history_final )
|--
  EX (restore_heap: model) ,
  (os_sched_active_heap_cut (os_sched_active_restore_input (environment) (critical) (history_local) (active) (sg) (history_returned) (cpu_sr) (history_entry) (history_final)) restore_heap )
).

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
Axiom proof_of_OS_Sched_partial_solve_wit_1_pure : OS_Sched_partial_solve_wit_1_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_1 : OS_Sched_partial_solve_wit_1.
Axiom proof_of_OS_Sched_partial_solve_wit_2 : OS_Sched_partial_solve_wit_2.
Axiom proof_of_OS_Sched_partial_solve_wit_3 : OS_Sched_partial_solve_wit_3.
Axiom proof_of_OS_Sched_partial_solve_wit_4_pure : OS_Sched_partial_solve_wit_4_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_4 : OS_Sched_partial_solve_wit_4.
Axiom proof_of_OS_Sched_partial_solve_wit_5 : OS_Sched_partial_solve_wit_5.
Axiom proof_of_OS_Sched_partial_solve_wit_6 : OS_Sched_partial_solve_wit_6.
Axiom proof_of_OS_Sched_partial_solve_wit_7_pure : OS_Sched_partial_solve_wit_7_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_7 : OS_Sched_partial_solve_wit_7.
Axiom proof_of_OS_Sched_partial_solve_wit_8 : OS_Sched_partial_solve_wit_8.
Axiom proof_of_OS_Sched_partial_solve_wit_9_pure : OS_Sched_partial_solve_wit_9_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_9 : OS_Sched_partial_solve_wit_9.
Axiom proof_of_OS_Sched_which_implies_wit_1 : OS_Sched_which_implies_wit_1.
Axiom proof_of_OS_Sched_which_implies_wit_2 : OS_Sched_which_implies_wit_2.
Axiom proof_of_OS_Sched_which_implies_wit_3 : OS_Sched_which_implies_wit_3.
Axiom proof_of_OS_Sched_which_implies_wit_4 : OS_Sched_which_implies_wit_4.

End VC_Correct.
