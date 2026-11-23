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
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_disabled_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_Sched -----*)

Definition OS_Sched_safety_wit_1 := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_completed_clients critical view )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (sched_disabled_entry_source view before )) ,
  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) retval acquired )
  **  (UCOS2_raw_rep sg acquired )
  **  (os_execution_view_resources external view )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_safety_wit_2 := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((os_sched_locks (acquired)) = 0)) (PreH2 : ((os_sched_ints (acquired)) = 0)) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_entry_source view acquired )) (PreH5 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH6 : (0 <= (os_sched_ints (acquired)))) (PreH7 : ((os_sched_ints (acquired)) <= 255)) (PreH8 : (0 <= (os_sched_locks (acquired)))) (PreH9 : ((os_sched_locks (acquired)) <= 255)) (PreH10 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : (sched_disabled_completed_clients critical view )) (PreH12 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired )) (PreH13 : (interrupt_saved_value mask cpu_sr )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (sched_disabled_context_rely view sg before acquired )) (PreH16 : (sched_disabled_entry_source view acquired )) (PreH17 : (sched_disabled_protected_identity acquired )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_disabled_counter_frame sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (os_execution_view_resources external view )
|--
  “ False ”
.

Definition OS_Sched_safety_wit_3 := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg (os_execution_invocation (view)) acquired current )) (PreH2 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : (sched_disabled_completed_clients critical view )) (PreH4 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (sched_disabled_context_rely view sg before acquired )) (PreH8 : (sched_disabled_entry_source view acquired )) (PreH9 : (sched_disabled_protected_identity acquired )) ,
  (interrupt_platform_running platform (os_execution_invocation (view)) (os_execution_origin (view)) (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg (os_execution_invocation (view)) current )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (os_execution_view_resources external view )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_entail_wit_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_completed_clients critical view )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (sched_disabled_entry_source view before )) ,
  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) retval acquired_2 )
  **  (UCOS2_raw_rep sg acquired_2 )
  **  (os_execution_view_resources external view )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_completed_clients critical view ) ” 
  &&  “ (critical_region_interval critical sg (os_execution_invocation (view)) before acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (sched_disabled_context_rely view sg before acquired ) ” 
  &&  “ (sched_disabled_entry_source view acquired ) ” 
  &&  “ (sched_disabled_protected_identity acquired ) ”
  &&  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) retval acquired )
  **  (UCOS2_inv sg acquired )
  **  (os_execution_view_resources external view )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_completed_clients critical view )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (sched_disabled_entry_source view before )) ,
  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) retval acquired_2 )
  **  (UCOS2_raw_rep sg acquired_2 )
  **  (os_execution_view_resources external view )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_completed_clients critical view ) ” 
  &&  “ (critical_region_interval critical sg (os_execution_invocation (view)) before acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (sched_disabled_context_rely view sg before acquired ) ” 
  &&  “ (sched_disabled_entry_source view acquired ) ” 
  &&  “ (sched_disabled_protected_identity acquired ) ”
  &&  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) retval acquired )
  **  (UCOS2_inv sg acquired )
  **  (os_execution_view_resources external view )
).

Definition OS_Sched_entail_wit_2_1 := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_locks (acquired)) <> 0)) (PreH3 : ((os_sched_ints (acquired)) = 0)) (PreH4 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : (sched_disabled_entry_source view acquired )) (PreH6 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH7 : (0 <= (os_sched_ints (acquired)))) (PreH8 : ((os_sched_ints (acquired)) <= 255)) (PreH9 : (0 <= (os_sched_locks (acquired)))) (PreH10 : ((os_sched_locks (acquired)) <= 255)) (PreH11 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : (sched_disabled_completed_clients critical view )) (PreH13 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired )) (PreH14 : (interrupt_saved_value mask cpu_sr )) (PreH15 : (UCOS2_state_inv sg acquired )) (PreH16 : (sched_disabled_context_rely view sg before acquired )) (PreH17 : (sched_disabled_entry_source view acquired )) (PreH18 : (sched_disabled_protected_identity acquired )) ,
  (UCOS2_inv sg acquired )
  **  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (os_execution_view_resources external view )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_completed_clients critical view ) ” 
  &&  “ (critical_region_interval critical sg (os_execution_invocation (view)) before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (sched_disabled_context_rely view sg before acquired ) ” 
  &&  “ (sched_disabled_entry_source view acquired ) ” 
  &&  “ (sched_disabled_protected_identity acquired ) ”
  &&  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (os_execution_view_resources external view )
.

Definition OS_Sched_entail_wit_2_2 := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_ints (acquired)) <> 0)) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_entry_source view acquired )) (PreH5 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH6 : (0 <= (os_sched_ints (acquired)))) (PreH7 : ((os_sched_ints (acquired)) <= 255)) (PreH8 : (0 <= (os_sched_locks (acquired)))) (PreH9 : ((os_sched_locks (acquired)) <= 255)) (PreH10 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : (sched_disabled_completed_clients critical view )) (PreH12 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired )) (PreH13 : (interrupt_saved_value mask cpu_sr )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (sched_disabled_context_rely view sg before acquired )) (PreH16 : (sched_disabled_entry_source view acquired )) (PreH17 : (sched_disabled_protected_identity acquired )) ,
  (UCOS2_inv sg acquired )
  **  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (os_execution_view_resources external view )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_completed_clients critical view ) ” 
  &&  “ (critical_region_interval critical sg (os_execution_invocation (view)) before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (sched_disabled_context_rely view sg before acquired ) ” 
  &&  “ (sched_disabled_entry_source view acquired ) ” 
  &&  “ (sched_disabled_protected_identity acquired ) ”
  &&  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (os_execution_view_resources external view )
.

Definition OS_Sched_return_wit_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg (os_execution_invocation (view)) acquired current )) (PreH2 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : (sched_disabled_completed_clients critical view )) (PreH4 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (sched_disabled_context_rely view sg before acquired )) (PreH8 : (sched_disabled_entry_source view acquired )) (PreH9 : (sched_disabled_protected_identity acquired )) ,
  (interrupt_platform_running platform (os_execution_invocation (view)) (os_execution_origin (view)) (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg (os_execution_invocation (view)) current )
  **  (os_execution_view_resources external view )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (sched_disabled_contextual_post external platform critical sg view mask before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg (os_execution_invocation (view)) acquired current )) (PreH2 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : (sched_disabled_completed_clients critical view )) (PreH4 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (sched_disabled_context_rely view sg before acquired )) (PreH8 : (sched_disabled_entry_source view acquired )) (PreH9 : (sched_disabled_protected_identity acquired )) ,
  (interrupt_platform_running platform (os_execution_invocation (view)) (os_execution_origin (view)) (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg (os_execution_invocation (view)) current )
  **  (os_execution_view_resources external view )
|--
  (sched_disabled_contextual_post external platform critical sg view mask before )
).

Definition OS_Sched_return_wit_1_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (current: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg (os_execution_invocation (view)) acquired current )) (PreH2 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : (sched_disabled_completed_clients critical view )) (PreH4 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired )) (PreH5 : (interrupt_saved_value mask cpu_sr )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (sched_disabled_context_rely view sg before acquired )) (PreH8 : (sched_disabled_entry_source view acquired )) (PreH9 : (sched_disabled_protected_identity acquired )) ,
  (interrupt_platform_running platform (os_execution_invocation (view)) (os_execution_origin (view)) (armv7a_irq_fiq_mask (cpu_sr)) )
  **  (critical_region_outside critical sg (os_execution_invocation (view)) current )
  **  (os_execution_view_resources external view )
|--
  (sched_disabled_contextual_post external platform critical sg view mask before )
.

Definition OS_Sched_partial_solve_wit_1 := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_completed_clients critical view )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sched_disabled_entry_source view before )) ,
  (sched_disabled_closed external platform critical sg view mask before )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_completed_clients critical view ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sched_disabled_entry_source view before ) ”
  &&  (sched_disabled_closed external platform critical sg view mask before )
.

Definition OS_Sched_partial_solve_wit_2 := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_completed_clients critical view )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sched_disabled_entry_source view before )) ,
  (interrupt_platform_running platform (os_execution_invocation (view)) (os_execution_origin (view)) mask )
  **  (critical_region_outside critical sg (os_execution_invocation (view)) before )
  **  (os_execution_view_resources external view )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_completed_clients critical view ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sched_disabled_entry_source view before ) ”
  &&  (interrupt_platform_running platform (os_execution_invocation (view)) (os_execution_origin (view)) mask )
  **  (critical_region_outside critical sg (os_execution_invocation (view)) before )
  **  (os_execution_view_resources external view )
.

Definition OS_Sched_partial_solve_wit_3_pure := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_completed_clients critical view )) (PreH3 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (sched_disabled_context_rely view sg before acquired )) (PreH7 : (sched_disabled_entry_source view acquired )) (PreH8 : (sched_disabled_protected_identity acquired )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (os_execution_view_resources external view )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_entry_source view acquired ) ”
.

Definition OS_Sched_partial_solve_wit_3_aux := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_completed_clients critical view )) (PreH3 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (sched_disabled_context_rely view sg before acquired )) (PreH7 : (sched_disabled_entry_source view acquired )) (PreH8 : (sched_disabled_protected_identity acquired )) ,
  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (os_execution_view_resources external view )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_entry_source view acquired ) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_completed_clients critical view ) ” 
  &&  “ (critical_region_interval critical sg (os_execution_invocation (view)) before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (sched_disabled_context_rely view sg before acquired ) ” 
  &&  “ (sched_disabled_entry_source view acquired ) ” 
  &&  “ (sched_disabled_protected_identity acquired ) ”
  &&  (UCOS2_inv sg acquired )
  **  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (os_execution_view_resources external view )
.

Definition OS_Sched_partial_solve_wit_3 := OS_Sched_partial_solve_wit_3_pure -> OS_Sched_partial_solve_wit_3_aux.

Definition OS_Sched_partial_solve_wit_4_pure := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((os_sched_ints (acquired)) <> 0)) (PreH2 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : (sched_disabled_entry_source view acquired )) (PreH4 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH5 : (0 <= (os_sched_ints (acquired)))) (PreH6 : ((os_sched_ints (acquired)) <= 255)) (PreH7 : (0 <= (os_sched_locks (acquired)))) (PreH8 : ((os_sched_locks (acquired)) <= 255)) (PreH9 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH10 : (sched_disabled_completed_clients critical view )) (PreH11 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired )) (PreH12 : (interrupt_saved_value mask cpu_sr )) (PreH13 : (UCOS2_state_inv sg acquired )) (PreH14 : (sched_disabled_context_rely view sg before acquired )) (PreH15 : (sched_disabled_entry_source view acquired )) (PreH16 : (sched_disabled_protected_identity acquired )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_disabled_counter_frame sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (os_execution_view_resources external view )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
.

Definition OS_Sched_partial_solve_wit_4_aux := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((os_sched_ints (acquired)) <> 0)) (PreH2 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : (sched_disabled_entry_source view acquired )) (PreH4 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH5 : (0 <= (os_sched_ints (acquired)))) (PreH6 : ((os_sched_ints (acquired)) <= 255)) (PreH7 : (0 <= (os_sched_locks (acquired)))) (PreH8 : ((os_sched_locks (acquired)) <= 255)) (PreH9 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH10 : (sched_disabled_completed_clients critical view )) (PreH11 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired )) (PreH12 : (interrupt_saved_value mask cpu_sr )) (PreH13 : (UCOS2_state_inv sg acquired )) (PreH14 : (sched_disabled_context_rely view sg before acquired )) (PreH15 : (sched_disabled_entry_source view acquired )) (PreH16 : (sched_disabled_protected_identity acquired )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_disabled_counter_frame sg acquired )
  **  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (os_execution_view_resources external view )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((os_sched_ints (acquired)) <> 0) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_entry_source view acquired ) ” 
  &&  “ (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) )) ” 
  &&  “ (0 <= (os_sched_ints (acquired))) ” 
  &&  “ ((os_sched_ints (acquired)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (acquired))) ” 
  &&  “ ((os_sched_locks (acquired)) <= 255) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_completed_clients critical view ) ” 
  &&  “ (critical_region_interval critical sg (os_execution_invocation (view)) before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (sched_disabled_context_rely view sg before acquired ) ” 
  &&  “ (sched_disabled_entry_source view acquired ) ” 
  &&  “ (sched_disabled_protected_identity acquired ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_disabled_counter_frame sg acquired )
  **  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (os_execution_view_resources external view )
.

Definition OS_Sched_partial_solve_wit_4 := OS_Sched_partial_solve_wit_4_pure -> OS_Sched_partial_solve_wit_4_aux.

Definition OS_Sched_partial_solve_wit_5_pure := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((os_sched_locks (acquired)) <> 0)) (PreH2 : ((os_sched_ints (acquired)) = 0)) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_entry_source view acquired )) (PreH5 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH6 : (0 <= (os_sched_ints (acquired)))) (PreH7 : ((os_sched_ints (acquired)) <= 255)) (PreH8 : (0 <= (os_sched_locks (acquired)))) (PreH9 : ((os_sched_locks (acquired)) <= 255)) (PreH10 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : (sched_disabled_completed_clients critical view )) (PreH12 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired )) (PreH13 : (interrupt_saved_value mask cpu_sr )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (sched_disabled_context_rely view sg before acquired )) (PreH16 : (sched_disabled_entry_source view acquired )) (PreH17 : (sched_disabled_protected_identity acquired )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_disabled_counter_frame sg acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (os_execution_view_resources external view )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
.

Definition OS_Sched_partial_solve_wit_5_aux := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((os_sched_locks (acquired)) <> 0)) (PreH2 : ((os_sched_ints (acquired)) = 0)) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_entry_source view acquired )) (PreH5 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH6 : (0 <= (os_sched_ints (acquired)))) (PreH7 : ((os_sched_ints (acquired)) <= 255)) (PreH8 : (0 <= (os_sched_locks (acquired)))) (PreH9 : ((os_sched_locks (acquired)) <= 255)) (PreH10 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : (sched_disabled_completed_clients critical view )) (PreH12 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired )) (PreH13 : (interrupt_saved_value mask cpu_sr )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (sched_disabled_context_rely view sg before acquired )) (PreH16 : (sched_disabled_entry_source view acquired )) (PreH17 : (sched_disabled_protected_identity acquired )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_disabled_counter_frame sg acquired )
  **  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (os_execution_view_resources external view )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((os_sched_locks (acquired)) <> 0) ” 
  &&  “ ((os_sched_ints (acquired)) = 0) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_entry_source view acquired ) ” 
  &&  “ (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) )) ” 
  &&  “ (0 <= (os_sched_ints (acquired))) ” 
  &&  “ ((os_sched_ints (acquired)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (acquired))) ” 
  &&  “ ((os_sched_locks (acquired)) <= 255) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_completed_clients critical view ) ” 
  &&  “ (critical_region_interval critical sg (os_execution_invocation (view)) before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (sched_disabled_context_rely view sg before acquired ) ” 
  &&  “ (sched_disabled_entry_source view acquired ) ” 
  &&  “ (sched_disabled_protected_identity acquired ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_disabled_counter_frame sg acquired )
  **  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (os_execution_view_resources external view )
.

Definition OS_Sched_partial_solve_wit_5 := OS_Sched_partial_solve_wit_5_pure -> OS_Sched_partial_solve_wit_5_aux.

Definition OS_Sched_partial_solve_wit_6_pure := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_completed_clients critical view )) (PreH3 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (sched_disabled_context_rely view sg before acquired )) (PreH7 : (sched_disabled_entry_source view acquired )) (PreH8 : (sched_disabled_protected_identity acquired )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (os_execution_view_resources external view )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OS_Sched_partial_solve_wit_6_aux := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_completed_clients critical view )) (PreH3 : (critical_region_interval critical sg (os_execution_invocation (view)) before acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (sched_disabled_context_rely view sg before acquired )) (PreH7 : (sched_disabled_entry_source view acquired )) (PreH8 : (sched_disabled_protected_identity acquired )) ,
  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (os_execution_view_resources external view )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_completed_clients critical view ) ” 
  &&  “ (critical_region_interval critical sg (os_execution_invocation (view)) before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (sched_disabled_context_rely view sg before acquired ) ” 
  &&  “ (sched_disabled_entry_source view acquired ) ” 
  &&  “ (sched_disabled_protected_identity acquired ) ”
  &&  (critical_region_masked platform critical sg (os_execution_invocation (view)) (os_execution_origin (view)) cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (os_execution_view_resources external view )
.

Definition OS_Sched_partial_solve_wit_6 := OS_Sched_partial_solve_wit_6_pure -> OS_Sched_partial_solve_wit_6_aux.

Definition OS_Sched_which_implies_wit_1 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) ,
  (sched_disabled_closed external platform critical sg view mask before )
|--
  (interrupt_platform_running platform (os_execution_invocation (view)) (os_execution_origin (view)) mask )
  **  (critical_region_outside critical sg (os_execution_invocation (view)) before )
  **  (os_execution_view_resources external view )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) ,
  (sched_disabled_closed external platform critical sg view mask before )
|--
  (interrupt_platform_running platform (os_execution_invocation (view)) (os_execution_origin (view)) mask )
  **  (critical_region_outside critical sg (os_execution_invocation (view)) before )
  **  (os_execution_view_resources external view )
).

Definition OS_Sched_which_implies_wit_1_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) ,
  (sched_disabled_closed external platform critical sg view mask before )
|--
  (interrupt_platform_running platform (os_execution_invocation (view)) (os_execution_origin (view)) mask )
  **  (critical_region_outside critical sg (os_execution_invocation (view)) before )
  **  (os_execution_view_resources external view )
.

Definition OS_Sched_which_implies_wit_2 := 
(
forall (view: OsExecutionView) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_entry_source view acquired )) ,
  (UCOS2_inv sg acquired )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_entry_source view acquired ) ” 
  &&  “ (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) )) ” 
  &&  “ (0 <= (os_sched_ints (acquired))) ” 
  &&  “ ((os_sched_ints (acquired)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (acquired))) ” 
  &&  “ ((os_sched_locks (acquired)) <= 255) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_disabled_counter_frame sg acquired )
) \/
(
forall (view: OsExecutionView) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_entry_source view acquired )) ,
  (UCOS2_inv sg acquired )
|--
  “ ((os_sched_locks (acquired)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (acquired))) ” 
  &&  “ ((os_sched_ints (acquired)) <= 255) ” 
  &&  “ (0 <= (os_sched_ints (acquired))) ” 
  &&  “ (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) )) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_disabled_counter_frame sg acquired )
).

Definition OS_Sched_which_implies_wit_2_split_goal_1 := 
forall (view: OsExecutionView) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_entry_source view acquired )) ,
  (UCOS2_inv sg acquired )
|--
  “ ((os_sched_locks (acquired)) <= 255) ”
.

Definition OS_Sched_which_implies_wit_2_split_goal_2 := 
forall (view: OsExecutionView) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_entry_source view acquired )) ,
  (UCOS2_inv sg acquired )
|--
  “ (0 <= (os_sched_locks (acquired))) ”
.

Definition OS_Sched_which_implies_wit_2_split_goal_3 := 
forall (view: OsExecutionView) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_entry_source view acquired )) ,
  (UCOS2_inv sg acquired )
|--
  “ ((os_sched_ints (acquired)) <= 255) ”
.

Definition OS_Sched_which_implies_wit_2_split_goal_4 := 
forall (view: OsExecutionView) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_entry_source view acquired )) ,
  (UCOS2_inv sg acquired )
|--
  “ (0 <= (os_sched_ints (acquired))) ”
.

Definition OS_Sched_which_implies_wit_2_split_goal_5 := 
forall (view: OsExecutionView) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_entry_source view acquired )) ,
  (UCOS2_inv sg acquired )
|--
  “ (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) )) ”
.

Definition OS_Sched_which_implies_wit_2_split_goal_spatial := 
forall (view: OsExecutionView) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_entry_source view acquired )) ,
  (UCOS2_inv sg acquired )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_disabled_counter_frame sg acquired )
.

Definition OS_Sched_which_implies_wit_3 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_disabled_counter_frame sg acquired )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (UCOS2_inv sg acquired )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_disabled_counter_frame sg acquired )
|--
  (UCOS2_inv sg acquired )
).

Definition OS_Sched_which_implies_wit_3_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_disabled_counter_frame sg acquired )
|--
  (UCOS2_inv sg acquired )
.

Module Type VC_Correct.


Axiom proof_of_OS_Sched_safety_wit_1 : OS_Sched_safety_wit_1.
Axiom proof_of_OS_Sched_safety_wit_2 : OS_Sched_safety_wit_2.
Axiom proof_of_OS_Sched_safety_wit_3 : OS_Sched_safety_wit_3.
Axiom proof_of_OS_Sched_entail_wit_1 : OS_Sched_entail_wit_1.
Axiom proof_of_OS_Sched_entail_wit_2_1 : OS_Sched_entail_wit_2_1.
Axiom proof_of_OS_Sched_entail_wit_2_2 : OS_Sched_entail_wit_2_2.
Axiom proof_of_OS_Sched_return_wit_1 : OS_Sched_return_wit_1.
Axiom proof_of_OS_Sched_partial_solve_wit_1 : OS_Sched_partial_solve_wit_1.
Axiom proof_of_OS_Sched_partial_solve_wit_2 : OS_Sched_partial_solve_wit_2.
Axiom proof_of_OS_Sched_partial_solve_wit_3_pure : OS_Sched_partial_solve_wit_3_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_3 : OS_Sched_partial_solve_wit_3.
Axiom proof_of_OS_Sched_partial_solve_wit_4_pure : OS_Sched_partial_solve_wit_4_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_4 : OS_Sched_partial_solve_wit_4.
Axiom proof_of_OS_Sched_partial_solve_wit_5_pure : OS_Sched_partial_solve_wit_5_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_5 : OS_Sched_partial_solve_wit_5.
Axiom proof_of_OS_Sched_partial_solve_wit_6_pure : OS_Sched_partial_solve_wit_6_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_6 : OS_Sched_partial_solve_wit_6.
Axiom proof_of_OS_Sched_which_implies_wit_1 : OS_Sched_which_implies_wit_1.
Axiom proof_of_OS_Sched_which_implies_wit_2 : OS_Sched_which_implies_wit_2.
Axiom proof_of_OS_Sched_which_implies_wit_3 : OS_Sched_which_implies_wit_3.

End VC_Correct.
