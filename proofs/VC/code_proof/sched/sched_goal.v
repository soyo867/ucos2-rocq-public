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
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_Sched -----*)

Definition OS_Sched_safety_wit_1 := 
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before acquired )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (os_sched_acquire_safety external critical sg context before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) retval acquired )
  **  (UCOS2_raw_rep sg acquired )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_safety_wit_2 := 
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (returned: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (os_sched_c_return external critical sg entry context returned final )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg (os_sched_call_invocation (context)) final )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_sched_context_resources external returned )
  **  (unmap_table_rep sg )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_entail_wit_1 := 
(
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before acquired )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (os_sched_acquire_safety external critical sg context before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) retval acquired )
  **  (UCOS2_raw_rep sg acquired )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (os_sched_entry_safety external sg context entry ) ”
  &&  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) retval entry )
  **  (os_sched_context_resources external context )
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
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before acquired )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (os_sched_acquire_safety external critical sg context before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) retval acquired )
  **  (UCOS2_raw_rep sg acquired )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (os_sched_entry_safety external sg context entry ) ”
  &&  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) retval entry )
  **  (os_sched_context_resources external context )
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
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) = 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) = 0)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry_2 )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (UCOS2_state_inv sg entry_2 )) (PreH8 : (os_sched_entry_safety external sg context entry_2 )) ,
  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (sched_new_priority ((os_sched_group (entry_2))) ((os_sched_rows (entry_2)))) )
  **  (os_sched_context_resources external context )
  **  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry_2 )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (os_sched_entry_safety external sg context entry ) ” 
  &&  “ ((os_sched_ints (entry)) = 0) ” 
  &&  “ ((os_sched_locks (entry)) = 0) ” 
  &&  “ (0 <= (os_sched_selected (entry))) ” 
  &&  “ ((os_sched_selected (entry)) < 64) ” 
  &&  “ ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry))) ”
  &&  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (os_sched_context_resources external context )
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
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) = 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) = 0)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry_2 )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (UCOS2_state_inv sg entry_2 )) (PreH8 : (os_sched_entry_safety external sg context entry_2 )) ,
  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (sched_new_priority ((os_sched_group (entry_2))) ((os_sched_rows (entry_2)))) )
  **  (os_sched_context_resources external context )
  **  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry_2 )
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State) ,
  “ ((os_sched_table (sg) (entry_2)) = (os_sched_table (sg) (entry))) ” 
  &&  “ ((os_sched_counter (entry_2)) = (os_sched_counter (entry))) ” 
  &&  “ ((os_sched_old_pointer (sg) (entry_2)) = (os_sched_old_pointer (sg) (entry))) ” 
  &&  “ ((os_sched_current (entry_2)) = (os_sched_current (entry))) ” 
  &&  “ ((os_sched_locks (entry_2)) = (os_sched_locks (entry))) ” 
  &&  “ ((os_sched_ints (entry_2)) = (os_sched_ints (entry))) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (os_sched_entry_safety external sg context entry ) ” 
  &&  “ ((os_sched_ints (entry)) = 0) ” 
  &&  “ ((os_sched_locks (entry)) = 0) ” 
  &&  “ (0 <= (os_sched_selected (entry))) ” 
  &&  “ ((os_sched_selected (entry)) < 64) ” 
  &&  “ ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry))) ”
  &&  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (os_sched_context_resources external context )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (entry)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (entry)) )
  **  (unmap_table_rep sg )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (os_sched_selected (entry)))
  **  (os_sched_work_frame sg entry )
).

Definition OS_Sched_entail_wit_3 := 
(
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_selected (entry_2)) <> (os_sched_current (entry_2)))) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (UCOS2_state_inv sg entry_2 )) (PreH6 : (os_sched_entry_safety external sg context entry_2 )) (PreH7 : ((os_sched_ints (entry_2)) = 0)) (PreH8 : ((os_sched_locks (entry_2)) = 0)) (PreH9 : (0 <= (os_sched_selected (entry_2)))) (PreH10 : ((os_sched_selected (entry_2)) < 64)) (PreH11 : ((Znth ((os_sched_selected (entry_2))) ((os_sched_table (sg) (entry_2))) (0)) = (os_sched_selected_tcb (sg) (entry_2)))) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry_2 )
  **  (os_sched_context_resources external context )
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
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_switch_requested entry ) ” 
  &&  “ (os_sched_switch_input external sg context entry ) ”
  &&  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_prefix_state (entry)) )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
) \/
(
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((os_sched_counter (entry_2)) + 1 )) (32)) >= 0)) (PreH3 : ((os_sched_selected (entry_2)) <> (os_sched_current (entry_2)))) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry_2 )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (UCOS2_state_inv sg entry_2 )) (PreH8 : (os_sched_entry_safety external sg context entry_2 )) (PreH9 : ((os_sched_ints (entry_2)) = 0)) (PreH10 : ((os_sched_locks (entry_2)) = 0)) (PreH11 : (0 <= (os_sched_selected (entry_2)))) (PreH12 : ((os_sched_selected (entry_2)) < 64)) (PreH13 : ((Znth ((os_sched_selected (entry_2))) ((os_sched_table (sg) (entry_2))) (0)) = (os_sched_selected_tcb (sg) (entry_2)))) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry_2 )
  **  (os_sched_context_resources external context )
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
  EX (entry: UCOS2_Verify_State) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_switch_requested entry ) ” 
  &&  “ (os_sched_switch_input external sg context entry ) ”
  &&  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_prefix_state (entry)) )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_entail_wit_4_1 := 
(
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (returned_2: OsSchedCallContext) (final_2: UCOS2_Verify_State) (PreH1 : (os_sched_switch_outcome external critical sg entry_2 context (OsSchedOriginalResumed (returned_2) (final_2)) )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (os_sched_switch_requested entry_2 )) (PreH6 : (os_sched_switch_input external sg context entry_2 )) ,
  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry_2 )
  **  (UCOS2_inv sg final_2 )
  **  (os_sched_context_resources external returned_2 )
  **  (unmap_table_rep sg )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State)  (entry: UCOS2_Verify_State) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_c_return external critical sg entry context returned final ) ”
  &&  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (UCOS2_inv sg final )
  **  (os_sched_context_resources external returned )
  **  (unmap_table_rep sg )
) \/
(
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (returned_2: OsSchedCallContext) (final_2: UCOS2_Verify_State) (PreH1 : (os_sched_switch_outcome external critical sg entry_2 context (OsSchedOriginalResumed (returned_2) (final_2)) )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (os_sched_switch_requested entry_2 )) (PreH6 : (os_sched_switch_input external sg context entry_2 )) ,
  TT && emp 
|--
  “ (os_sched_c_return external critical sg entry_2 context returned_2 final_2 ) ”
  &&  emp
).

Definition OS_Sched_entail_wit_4_1_split_goal_1 := 
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (returned_2: OsSchedCallContext) (final_2: UCOS2_Verify_State) (PreH1 : (os_sched_switch_outcome external critical sg entry_2 context (OsSchedOriginalResumed (returned_2) (final_2)) )) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (os_sched_switch_requested entry_2 )) (PreH6 : (os_sched_switch_input external sg context entry_2 )) ,
  (os_sched_c_return external critical sg entry_2 context returned_2 final_2 )
.

Definition OS_Sched_entail_wit_4_2 := 
(
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_selected (entry_2)) = (os_sched_current (entry_2)))) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (UCOS2_state_inv sg entry_2 )) (PreH6 : (os_sched_entry_safety external sg context entry_2 )) (PreH7 : ((os_sched_ints (entry_2)) = 0)) (PreH8 : ((os_sched_locks (entry_2)) = 0)) (PreH9 : (0 <= (os_sched_selected (entry_2)))) (PreH10 : ((os_sched_selected (entry_2)) < 64)) (PreH11 : ((Znth ((os_sched_selected (entry_2))) ((os_sched_table (sg) (entry_2))) (0)) = (os_sched_selected_tcb (sg) (entry_2)))) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry_2 )
  **  (os_sched_context_resources external context )
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
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State)  (entry: UCOS2_Verify_State) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_c_return external critical sg entry context returned final ) ”
  &&  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (UCOS2_inv sg final )
  **  (os_sched_context_resources external returned )
  **  (unmap_table_rep sg )
) \/
(
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry_2)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (entry_2)) >= 0)) (PreH3 : ((os_sched_selected (entry_2)) = (os_sched_current (entry_2)))) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry_2 )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (UCOS2_state_inv sg entry_2 )) (PreH8 : (os_sched_entry_safety external sg context entry_2 )) (PreH9 : ((os_sched_ints (entry_2)) = 0)) (PreH10 : ((os_sched_locks (entry_2)) = 0)) (PreH11 : (0 <= (os_sched_selected (entry_2)))) (PreH12 : ((os_sched_selected (entry_2)) < 64)) (PreH13 : ((Znth ((os_sched_selected (entry_2))) ((os_sched_table (sg) (entry_2))) (0)) = (os_sched_selected_tcb (sg) (entry_2)))) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry_2 )
  **  (os_sched_context_resources external context )
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
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State)  (entry: UCOS2_Verify_State) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_c_return external critical sg entry context returned final ) ”
  &&  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (UCOS2_inv sg final )
  **  (os_sched_context_resources external returned )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_entail_wit_4_3 := 
(
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) <> 0)) (PreH2 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) = 0)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry_2 )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (UCOS2_state_inv sg entry_2 )) (PreH7 : (os_sched_entry_safety external sg context entry_2 )) ,
  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry_2 )
  **  (os_sched_context_resources external context )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (os_sched_old_high (entry_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State)  (entry: UCOS2_Verify_State) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_c_return external critical sg entry context returned final ) ”
  &&  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (UCOS2_inv sg final )
  **  (os_sched_context_resources external returned )
  **  (unmap_table_rep sg )
) \/
(
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry_2)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (entry_2)) >= 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_locks (entry_2))) (32)) <> 0)) (PreH4 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) = 0)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry_2 )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (UCOS2_state_inv sg entry_2 )) (PreH9 : (os_sched_entry_safety external sg context entry_2 )) ,
  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry_2 )
  **  (os_sched_context_resources external context )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (os_sched_old_high (entry_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State)  (entry: UCOS2_Verify_State) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_c_return external critical sg entry context returned final ) ”
  &&  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (UCOS2_inv sg final )
  **  (os_sched_context_resources external returned )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_entail_wit_4_4 := 
(
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) <> 0)) (PreH2 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry_2 )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (UCOS2_state_inv sg entry_2 )) (PreH6 : (os_sched_entry_safety external sg context entry_2 )) ,
  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry_2 )
  **  (os_sched_context_resources external context )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (os_sched_old_high (entry_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State)  (entry: UCOS2_Verify_State) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_c_return external critical sg entry context returned final ) ”
  &&  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (UCOS2_inv sg final )
  **  (os_sched_context_resources external returned )
  **  (unmap_table_rep sg )
) \/
(
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry_2)) <= UINT_MAX)) (PreH2 : ((os_sched_counter (entry_2)) >= 0)) (PreH3 : ((unsigned_last_nbits ((os_sched_ints (entry_2))) (32)) <> 0)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry_2 )) (PreH6 : (interrupt_saved_value mask cpu_sr )) (PreH7 : (UCOS2_state_inv sg entry_2 )) (PreH8 : (os_sched_entry_safety external sg context entry_2 )) ,
  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry_2 )
  **  (os_sched_context_resources external context )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (entry_2)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (entry_2)))
  **  (sched_new_rep sg (os_sched_group (entry_2)) (os_sched_rows (entry_2)) (os_sched_old_high (entry_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_sched_table (sg) (entry_2)) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_sched_current (entry_2)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_sched_old_pointer (sg) (entry_2)))
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> (os_sched_counter (entry_2)))
  **  (os_sched_work_frame sg entry_2 )
|--
  EX (returned: OsSchedCallContext)  (final: UCOS2_Verify_State)  (entry: UCOS2_Verify_State) ,
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_c_return external critical sg entry context returned final ) ”
  &&  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (UCOS2_inv sg final )
  **  (os_sched_context_resources external returned )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_return_wit_1 := 
(
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (returned: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (os_sched_c_return external critical sg entry context returned final )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg (os_sched_call_invocation (context)) final )
  **  (os_sched_context_resources external returned )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_sched_post external platform critical sg context mask before )
) \/
(
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (returned: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (os_sched_c_return external critical sg entry context returned final )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg (os_sched_call_invocation (context)) final )
  **  (os_sched_context_resources external returned )
  **  (unmap_table_rep sg )
|--
  (os_sched_post external platform critical sg context mask before )
).

Definition OS_Sched_return_wit_1_split_goal_spatial := 
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (returned: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (os_sched_c_return external critical sg entry context returned final )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg (os_sched_call_invocation (context)) final )
  **  (os_sched_context_resources external returned )
  **  (unmap_table_rep sg )
|--
  (os_sched_post external platform critical sg context mask before )
.

Definition OS_Sched_partial_solve_wit_1 := 
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (os_sched_pre external platform critical sg context mask before )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_sched_pre external platform critical sg context mask before )
.

Definition OS_Sched_partial_solve_wit_2 := 
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (os_sched_acquire_safety external critical sg context before )) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (critical_region_outside critical sg (os_sched_call_invocation (context)) before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_sched_acquire_safety external critical sg context before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (critical_region_outside critical sg (os_sched_call_invocation (context)) before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
.

Definition OS_Sched_partial_solve_wit_3_pure := 
(
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH2 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (os_sched_entry_safety external sg context entry )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (os_sched_context_resources external context )
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
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry)) <= UINT_MAX)) (PreH2 : (cpu_sr <= UINT_MAX)) (PreH3 : ((os_sched_counter (entry)) >= 0)) (PreH4 : (cpu_sr >= 0)) (PreH5 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH6 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (UCOS2_state_inv sg entry )) (PreH11 : (os_sched_entry_safety external sg context entry )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (os_sched_context_resources external context )
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
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((os_sched_counter (entry)) <= UINT_MAX)) (PreH2 : (cpu_sr <= UINT_MAX)) (PreH3 : ((os_sched_counter (entry)) >= 0)) (PreH4 : (cpu_sr >= 0)) (PreH5 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH6 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry )) (PreH9 : (interrupt_saved_value mask cpu_sr )) (PreH10 : (UCOS2_state_inv sg entry )) (PreH11 : (os_sched_entry_safety external sg context entry )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (os_sched_context_resources external context )
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
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((os_sched_locks (entry))) (32)) = 0)) (PreH2 : ((unsigned_last_nbits ((os_sched_ints (entry))) (32)) = 0)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (os_sched_entry_safety external sg context entry )) ,
  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (os_sched_context_resources external context )
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
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (os_sched_entry_safety external sg context entry ) ”
  &&  (sched_new_rep sg (os_sched_group (entry)) (os_sched_rows (entry)) (os_sched_old_high (entry)) )
  **  (os_sched_context_resources external context )
  **  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
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
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (UCOS2_state_inv sg entry )) (PreH5 : (os_sched_entry_safety external sg context entry )) (PreH6 : ((os_sched_ints (entry)) = 0)) (PreH7 : ((os_sched_locks (entry)) = 0)) (PreH8 : (0 <= (os_sched_selected (entry)))) (PreH9 : ((os_sched_selected (entry)) < 64)) (PreH10 : ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry)))) ,
  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (os_sched_context_resources external context )
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
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (os_sched_entry_safety external sg context entry ) ” 
  &&  “ ((os_sched_ints (entry)) = 0) ” 
  &&  “ ((os_sched_locks (entry)) = 0) ” 
  &&  “ (0 <= (os_sched_selected (entry))) ” 
  &&  “ ((os_sched_selected (entry)) < 64) ” 
  &&  “ ((Znth ((os_sched_selected (entry))) ((os_sched_table (sg) (entry))) (0)) = (os_sched_selected_tcb (sg) (entry))) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + ((os_sched_selected (entry)) * sizeof(PTR)))) # Ptr  |-> (Znth (os_sched_selected (entry)) (os_sched_table (sg) (entry)) 0))
  **  (PtrArray.missing_i ( &( "OSTCBPrioTbl" ) ) (os_sched_selected (entry)) 0 64 (os_sched_table (sg) (entry)) )
  **  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (os_sched_context_resources external context )
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
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (os_sched_switch_requested entry )) (PreH5 : (os_sched_switch_input external sg context entry )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_prefix_state (entry)) )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_switch_requested entry ) ” 
  &&  “ (os_sched_switch_input external sg context entry ) ”
.

Definition OS_Sched_partial_solve_wit_5_aux := 
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (os_sched_switch_requested entry )) (PreH5 : (os_sched_switch_input external sg context entry )) ,
  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_prefix_state (entry)) )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_switch_requested entry ) ” 
  &&  “ (os_sched_switch_input external sg context entry ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_switch_requested entry ) ” 
  &&  “ (os_sched_switch_input external sg context entry ) ”
  &&  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (UCOS2_inv sg (os_sched_prefix_state (entry)) )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
.

Definition OS_Sched_partial_solve_wit_5 := OS_Sched_partial_solve_wit_5_pure -> OS_Sched_partial_solve_wit_5_aux.

Definition OS_Sched_partial_solve_wit_6_pure := 
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (returned: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (os_sched_c_return external critical sg entry context returned final )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (UCOS2_inv sg final )
  **  (os_sched_context_resources external returned )
  **  (unmap_table_rep sg )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OS_Sched_partial_solve_wit_6_aux := 
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (entry: UCOS2_Verify_State) (final: UCOS2_Verify_State) (returned: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (os_sched_c_return external critical sg entry context returned final )) ,
  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (UCOS2_inv sg final )
  **  (os_sched_context_resources external returned )
  **  (unmap_table_rep sg )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (critical_region_interval critical sg (os_sched_call_invocation (context)) before entry ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (os_sched_c_return external critical sg entry context returned final ) ”
  &&  (critical_region_masked platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (UCOS2_inv sg final )
  **  (os_sched_context_resources external returned )
  **  (unmap_table_rep sg )
.

Definition OS_Sched_partial_solve_wit_6 := OS_Sched_partial_solve_wit_6_pure -> OS_Sched_partial_solve_wit_6_aux.

Definition OS_Sched_which_implies_wit_1 := 
(
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) ,
  (os_sched_pre external platform critical sg context mask before )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_sched_acquire_safety external critical sg context before ) ”
  &&  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (critical_region_outside critical sg (os_sched_call_invocation (context)) before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
) \/
(
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) ,
  (os_sched_pre external platform critical sg context mask before )
|--
  “ (os_sched_acquire_safety external critical sg context before ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
  &&  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (critical_region_outside critical sg (os_sched_call_invocation (context)) before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
).

Definition OS_Sched_which_implies_wit_1_split_goal_1 := 
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) ,
  (os_sched_pre external platform critical sg context mask before )
|--
  “ (os_sched_acquire_safety external critical sg context before ) ”
.

Definition OS_Sched_which_implies_wit_1_split_goal_2 := 
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) ,
  (os_sched_pre external platform critical sg context mask before )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OS_Sched_which_implies_wit_1_split_goal_spatial := 
forall (mask: Z) (context: OsSchedCallContext) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) ,
  (os_sched_pre external platform critical sg context mask before )
|--
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (critical_region_outside critical sg (os_sched_call_invocation (context)) before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
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
