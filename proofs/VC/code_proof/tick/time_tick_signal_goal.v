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
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_hook_isr_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OSTmrSignal -----*)

Definition OSTmrSignal_return_wit_1 := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (after_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (time_tick_sem_result sg (time_tick_signal_pointer (before)) before retval after_2 )) (PreH2 : (time_tick_signal_entry sg before )) (PreH3 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH4 : (time_tick_signal_entry sg before )) (PreH5 : (event_table_layout_prop sg )) (PreH6 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH7 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry after_2 )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (time_tick_sem_result sg (time_tick_signal_pointer (before)) before retval after ) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry after )
.

Definition OSTmrSignal_partial_solve_wit_1_pure := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_signal_entry sg before )) (PreH2 : (event_table_layout_prop sg )) (PreH3 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH4 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "err" ) )) # UChar  |->_)
  **  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
|--
  “ (time_tick_signal_entry sg before ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ”
.

Definition OSTmrSignal_partial_solve_wit_1_aux := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_signal_entry sg before )) (PreH2 : (event_table_layout_prop sg )) (PreH3 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH4 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
|--
  “ (time_tick_signal_entry sg before ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_signal_entry sg before ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
.

Definition OSTmrSignal_partial_solve_wit_1 := OSTmrSignal_partial_solve_wit_1_pure -> OSTmrSignal_partial_solve_wit_1_aux.

Definition OSTmrSignal_partial_solve_wit_2_pure := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_signal_entry sg before )) (PreH2 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH3 : (time_tick_signal_entry sg before )) (PreH4 : (event_table_layout_prop sg )) (PreH5 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH6 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> (time_tick_signal_pointer (before)))
  **  (time_tick_signal_read_frame sg before )
  **  ((( &( "err" ) )) # UChar  |->_)
|--
  “ ((time_tick_signal_pointer (before)) = (time_tick_signal_pointer (before))) ” 
  &&  “ (time_tick_signal_entry sg before ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrSignal_partial_solve_wit_2_aux := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_signal_entry sg before )) (PreH2 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH3 : (time_tick_signal_entry sg before )) (PreH4 : (event_table_layout_prop sg )) (PreH5 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH6 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> (time_tick_signal_pointer (before)))
  **  (time_tick_signal_read_frame sg before )
|--
  “ ((time_tick_signal_pointer (before)) = (time_tick_signal_pointer (before))) ” 
  &&  “ (time_tick_signal_entry sg before ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_signal_entry sg before ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_signal_entry sg before ) ” 
  &&  “ (event_table_layout_prop sg ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> (time_tick_signal_pointer (before)))
  **  (time_tick_signal_read_frame sg before )
.

Definition OSTmrSignal_partial_solve_wit_2 := OSTmrSignal_partial_solve_wit_2_pure -> OSTmrSignal_partial_solve_wit_2_aux.

Definition OSTmrSignal_which_implies_wit_1 := 
(
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_signal_entry sg before )) (PreH2 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
|--
  “ (time_tick_signal_entry sg before ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> (time_tick_signal_pointer (before)))
  **  (time_tick_signal_read_frame sg before )
) \/
(
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_signal_entry sg before )) (PreH2 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
|--
  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> (time_tick_signal_pointer (before)))
  **  (time_tick_signal_read_frame sg before )
).

Definition OSTmrSignal_which_implies_wit_1_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_signal_entry sg before )) (PreH2 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) ,
  (time_tick_sched_owned platform critical sg invocation origin region_entry before )
|--
  (interrupt_platform_running platform invocation origin 192 )
  **  (critical_region_inside critical sg invocation region_entry )
  **  (unmap_table_rep sg )
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> (time_tick_signal_pointer (before)))
  **  (time_tick_signal_read_frame sg before )
.

Definition OSSemPost_derive_tick_signal_read_by_tick_sem_source := 
forall (pevent_pre: Z) (before_tick_signal_read: UCOS2_Verify_State) (region_entry_tick_signal_read: UCOS2_Verify_State) (origin_tick_signal_read: TaskInvocationOrigin) (invocation_tick_signal_read: nat) (sg_tick_signal_read: StableGlobVars) (critical_tick_signal_read: CriticalRegionResources) (platform_tick_signal_read: InterruptPlatformResources) ,
  “ (pevent_pre = (time_tick_signal_pointer (before_tick_signal_read))) ” 
  &&  “ (time_tick_signal_entry sg_tick_signal_read before_tick_signal_read ) ” 
  &&  “ (event_table_layout_prop sg_tick_signal_read ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg_tick_signal_read))) ” 
  &&  “ (time_tick_internal_addresses sg_tick_signal_read ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (interrupt_platform_running platform_tick_signal_read invocation_tick_signal_read origin_tick_signal_read 192 )
  **  (critical_region_inside critical_tick_signal_read sg_tick_signal_read invocation_tick_signal_read region_entry_tick_signal_read )
  **  (unmap_table_rep sg_tick_signal_read )
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> (time_tick_signal_pointer (before_tick_signal_read)))
  **  (time_tick_signal_read_frame sg_tick_signal_read before_tick_signal_read )
|--
EX (platform_tick_sem_source: InterruptPlatformResources) (critical_tick_sem_source: CriticalRegionResources) (sg_tick_sem_source: StableGlobVars) (invocation_tick_sem_source: nat) (origin_tick_sem_source: TaskInvocationOrigin) (region_entry_tick_sem_source: UCOS2_Verify_State) (before_tick_sem_source: UCOS2_Verify_State) (pe_tick_sem_source: Z) ,
  (“ (pevent_pre = pe_tick_sem_source) ” 
  &&  “ (sem_post_profile sg_tick_sem_source ) ” 
  &&  “ (time_tick_post_readable sg_tick_sem_source before_tick_sem_source pe_tick_sem_source ) ” 
  &&  “ (event_table_layout_prop sg_tick_sem_source ) ” 
  &&  “ (time_tick_internal_addresses sg_tick_sem_source ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_ints (before_tick_sem_source)) > 0) ”
  &&  (time_tick_sched_owned platform_tick_sem_source critical_tick_sem_source sg_tick_sem_source invocation_tick_sem_source origin_tick_sem_source region_entry_tick_sem_source before_tick_sem_source ))
  **
  ((EX after_2 retval_2,
  “ (time_tick_sem_result sg_tick_sem_source pe_tick_sem_source before_tick_sem_source retval_2 after_2 ) ”
  &&  (time_tick_sched_owned platform_tick_sem_source critical_tick_sem_source sg_tick_sem_source invocation_tick_sem_source origin_tick_sem_source region_entry_tick_sem_source after_2 ))
  -*
  (EX after retval,
  “ (time_tick_sem_result sg_tick_signal_read (time_tick_signal_pointer (before_tick_signal_read)) before_tick_signal_read retval after ) ”
  &&  (time_tick_sched_owned platform_tick_signal_read critical_tick_signal_read sg_tick_signal_read invocation_tick_signal_read origin_tick_signal_read region_entry_tick_signal_read after )))
.

Module Type VC_Correct.


Axiom proof_of_OSTmrSignal_return_wit_1 : OSTmrSignal_return_wit_1.
Axiom proof_of_OSTmrSignal_partial_solve_wit_1_pure : OSTmrSignal_partial_solve_wit_1_pure.
Axiom proof_of_OSTmrSignal_partial_solve_wit_1 : OSTmrSignal_partial_solve_wit_1.
Axiom proof_of_OSTmrSignal_partial_solve_wit_2_pure : OSTmrSignal_partial_solve_wit_2_pure.
Axiom proof_of_OSTmrSignal_partial_solve_wit_2 : OSTmrSignal_partial_solve_wit_2.
Axiom proof_of_OSTmrSignal_which_implies_wit_1 : OSTmrSignal_which_implies_wit_1.
Axiom proof_of_OSSemPost_derive_tick_signal_read_by_tick_sem_source : OSSemPost_derive_tick_signal_read_by_tick_sem_source.

End VC_Correct.
