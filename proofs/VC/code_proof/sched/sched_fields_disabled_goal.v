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
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_disabled_spec.
Local Open Scope sac.

(*----- Function OS_Sched -----*)

Definition OS_Sched_safety_wit_1 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (retval: Z) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (sched_fields_disabled_save_output environment critical sg view mask before local frame first_heap retval )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_safety_wit_2 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (PreH1 : ((os_sched_locks (acquired)) = 0)) (PreH2 : ((os_sched_ints (acquired)) = 0)) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_entry_source entered acquired )) (PreH5 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH6 : (0 <= (os_sched_ints (acquired)))) (PreH7 : ((os_sched_ints (acquired)) <= 255)) (PreH8 : (0 <= (os_sched_locks (acquired)))) (PreH9 : ((os_sched_locks (acquired)) <= 255)) (PreH10 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH12 : (sched_disabled_completed_clients critical entered )) (PreH13 : (sched_disabled_entry_source entered acquired )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (interrupt_saved_value mask cpu_sr )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (sched_fields_disabled_counter_frame environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
|--
  “ False ”
.

Definition OS_Sched_safety_wit_3 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (restore_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_locks (acquired)) <> 0)) (PreH3 : ((os_sched_ints (acquired)) = 0)) (PreH4 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : (sched_disabled_entry_source entered acquired )) (PreH6 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH7 : (0 <= (os_sched_ints (acquired)))) (PreH8 : ((os_sched_ints (acquired)) <= 255)) (PreH9 : (0 <= (os_sched_locks (acquired)))) (PreH10 : ((os_sched_locks (acquired)) <= 255)) (PreH11 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH13 : (sched_disabled_completed_clients critical entered )) (PreH14 : (sched_disabled_entry_source entered acquired )) (PreH15 : (UCOS2_state_inv sg acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_disabled_restore_output environment critical sg entered mask cpu_sr acquired acquired entered_local frame restore_heap )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_safety_wit_4 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (restore_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_ints (acquired)) <> 0)) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_entry_source entered acquired )) (PreH5 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH6 : (0 <= (os_sched_ints (acquired)))) (PreH7 : ((os_sched_ints (acquired)) <= 255)) (PreH8 : (0 <= (os_sched_locks (acquired)))) (PreH9 : ((os_sched_locks (acquired)) <= 255)) (PreH10 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH12 : (sched_disabled_completed_clients critical entered )) (PreH13 : (sched_disabled_entry_source entered acquired )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_disabled_restore_output environment critical sg entered mask cpu_sr acquired acquired entered_local frame restore_heap )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_Sched_entail_wit_1 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (retval: Z) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (sched_fields_disabled_save_output environment critical sg view mask before local frame first_heap retval )
|--
  EX (entered: OsExecutionView)  (acquired: UCOS2_Verify_State)  (entered_local: (Armv7aContinuation -> Assertion))  (saved_heap: model) ,
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_fields_disabled_save_event environment critical sg view entered mask retval before acquired local entered_local frame first_heap saved_heap ) ” 
  &&  “ (sched_disabled_completed_clients critical entered ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ”
  &&  (sched_fields_disabled_masked environment critical entered_local sg entered retval acquired acquired )
  **  (frame )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (retval: Z) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (sched_fields_disabled_save_output environment critical sg view mask before local frame first_heap retval )
|--
  EX (entered: OsExecutionView)  (acquired: UCOS2_Verify_State)  (entered_local: (Armv7aContinuation -> Assertion))  (saved_heap: model) ,
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_fields_disabled_save_event environment critical sg view entered mask retval before acquired local entered_local frame first_heap saved_heap ) ” 
  &&  “ (sched_disabled_completed_clients critical entered ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ”
  &&  (sched_fields_disabled_masked environment critical entered_local sg entered retval acquired acquired )
  **  (frame )
).

Definition OS_Sched_return_wit_1 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (restore_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_locks (acquired)) <> 0)) (PreH3 : ((os_sched_ints (acquired)) = 0)) (PreH4 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : (sched_disabled_entry_source entered acquired )) (PreH6 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH7 : (0 <= (os_sched_ints (acquired)))) (PreH8 : ((os_sched_ints (acquired)) <= 255)) (PreH9 : (0 <= (os_sched_locks (acquired)))) (PreH10 : ((os_sched_locks (acquired)) <= 255)) (PreH11 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH13 : (sched_disabled_completed_clients critical entered )) (PreH14 : (sched_disabled_entry_source entered acquired )) (PreH15 : (UCOS2_state_inv sg acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_disabled_restore_output environment critical sg entered mask cpu_sr acquired acquired entered_local frame restore_heap )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (sched_fields_disabled_post environment critical sg view mask before local frame )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (restore_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_locks (acquired)) <> 0)) (PreH3 : ((os_sched_ints (acquired)) = 0)) (PreH4 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : (sched_disabled_entry_source entered acquired )) (PreH6 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH7 : (0 <= (os_sched_ints (acquired)))) (PreH8 : ((os_sched_ints (acquired)) <= 255)) (PreH9 : (0 <= (os_sched_locks (acquired)))) (PreH10 : ((os_sched_locks (acquired)) <= 255)) (PreH11 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH13 : (sched_disabled_completed_clients critical entered )) (PreH14 : (sched_disabled_entry_source entered acquired )) (PreH15 : (UCOS2_state_inv sg acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_disabled_restore_output environment critical sg entered mask cpu_sr acquired acquired entered_local frame restore_heap )
|--
  (sched_fields_disabled_post environment critical sg view mask before local frame )
).

Definition OS_Sched_return_wit_1_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (restore_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_locks (acquired)) <> 0)) (PreH3 : ((os_sched_ints (acquired)) = 0)) (PreH4 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : (sched_disabled_entry_source entered acquired )) (PreH6 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH7 : (0 <= (os_sched_ints (acquired)))) (PreH8 : ((os_sched_ints (acquired)) <= 255)) (PreH9 : (0 <= (os_sched_locks (acquired)))) (PreH10 : ((os_sched_locks (acquired)) <= 255)) (PreH11 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH13 : (sched_disabled_completed_clients critical entered )) (PreH14 : (sched_disabled_entry_source entered acquired )) (PreH15 : (UCOS2_state_inv sg acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_disabled_restore_output environment critical sg entered mask cpu_sr acquired acquired entered_local frame restore_heap )
|--
  (sched_fields_disabled_post environment critical sg view mask before local frame )
.

Definition OS_Sched_return_wit_2 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (restore_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_ints (acquired)) <> 0)) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_entry_source entered acquired )) (PreH5 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH6 : (0 <= (os_sched_ints (acquired)))) (PreH7 : ((os_sched_ints (acquired)) <= 255)) (PreH8 : (0 <= (os_sched_locks (acquired)))) (PreH9 : ((os_sched_locks (acquired)) <= 255)) (PreH10 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH12 : (sched_disabled_completed_clients critical entered )) (PreH13 : (sched_disabled_entry_source entered acquired )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_disabled_restore_output environment critical sg entered mask cpu_sr acquired acquired entered_local frame restore_heap )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (sched_fields_disabled_post environment critical sg view mask before local frame )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (restore_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_ints (acquired)) <> 0)) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_entry_source entered acquired )) (PreH5 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH6 : (0 <= (os_sched_ints (acquired)))) (PreH7 : ((os_sched_ints (acquired)) <= 255)) (PreH8 : (0 <= (os_sched_locks (acquired)))) (PreH9 : ((os_sched_locks (acquired)) <= 255)) (PreH10 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH12 : (sched_disabled_completed_clients critical entered )) (PreH13 : (sched_disabled_entry_source entered acquired )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_disabled_restore_output environment critical sg entered mask cpu_sr acquired acquired entered_local frame restore_heap )
|--
  (sched_fields_disabled_post environment critical sg view mask before local frame )
).

Definition OS_Sched_return_wit_2_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (restore_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_ints (acquired)) <> 0)) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_entry_source entered acquired )) (PreH5 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH6 : (0 <= (os_sched_ints (acquired)))) (PreH7 : ((os_sched_ints (acquired)) <= 255)) (PreH8 : (0 <= (os_sched_locks (acquired)))) (PreH9 : ((os_sched_locks (acquired)) <= 255)) (PreH10 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH12 : (sched_disabled_completed_clients critical entered )) (PreH13 : (sched_disabled_entry_source entered acquired )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_disabled_restore_output environment critical sg entered mask cpu_sr acquired acquired entered_local frame restore_heap )
|--
  (sched_fields_disabled_post environment critical sg view mask before local frame )
.

Definition OS_Sched_partial_solve_wit_1 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (sched_fields_disabled_pre environment critical local sg view mask before frame )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (sched_fields_disabled_pre environment critical local sg view mask before frame )
.

Definition OS_Sched_partial_solve_wit_2 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (sched_fields_heap_cut (sched_fields_disabled_pre (environment) (critical) (local) (sg) (view) (mask) (before) (frame)) first_heap )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (sched_fields_heap_cut (sched_fields_disabled_pre (environment) (critical) (local) (sg) (view) (mask) (before) (frame)) first_heap )
.

Definition OS_Sched_partial_solve_wit_3_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH3 : (sched_disabled_completed_clients critical entered )) (PreH4 : (sched_disabled_entry_source entered acquired )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (interrupt_saved_value mask cpu_sr )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ”
.

Definition OS_Sched_partial_solve_wit_3_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH3 : (sched_disabled_completed_clients critical entered )) (PreH4 : (sched_disabled_entry_source entered acquired )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap ) ” 
  &&  “ (sched_disabled_completed_clients critical entered ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
.

Definition OS_Sched_partial_solve_wit_3 := OS_Sched_partial_solve_wit_3_pure -> OS_Sched_partial_solve_wit_3_aux.

Definition OS_Sched_partial_solve_wit_4_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (PreH1 : ((os_sched_ints (acquired)) <> 0)) (PreH2 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : (sched_disabled_entry_source entered acquired )) (PreH4 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH5 : (0 <= (os_sched_ints (acquired)))) (PreH6 : ((os_sched_ints (acquired)) <= 255)) (PreH7 : (0 <= (os_sched_locks (acquired)))) (PreH8 : ((os_sched_locks (acquired)) <= 255)) (PreH9 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH10 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH11 : (sched_disabled_completed_clients critical entered )) (PreH12 : (sched_disabled_entry_source entered acquired )) (PreH13 : (UCOS2_state_inv sg acquired )) (PreH14 : (interrupt_saved_value mask cpu_sr )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (sched_fields_disabled_counter_frame environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
.

Definition OS_Sched_partial_solve_wit_4_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (PreH1 : ((os_sched_ints (acquired)) <> 0)) (PreH2 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : (sched_disabled_entry_source entered acquired )) (PreH4 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH5 : (0 <= (os_sched_ints (acquired)))) (PreH6 : ((os_sched_ints (acquired)) <= 255)) (PreH7 : (0 <= (os_sched_locks (acquired)))) (PreH8 : ((os_sched_locks (acquired)) <= 255)) (PreH9 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH10 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH11 : (sched_disabled_completed_clients critical entered )) (PreH12 : (sched_disabled_entry_source entered acquired )) (PreH13 : (UCOS2_state_inv sg acquired )) (PreH14 : (interrupt_saved_value mask cpu_sr )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_fields_disabled_counter_frame environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((os_sched_ints (acquired)) <> 0) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) )) ” 
  &&  “ (0 <= (os_sched_ints (acquired))) ” 
  &&  “ ((os_sched_ints (acquired)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (acquired))) ” 
  &&  “ ((os_sched_locks (acquired)) <= 255) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap ) ” 
  &&  “ (sched_disabled_completed_clients critical entered ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_fields_disabled_counter_frame environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
.

Definition OS_Sched_partial_solve_wit_4 := OS_Sched_partial_solve_wit_4_pure -> OS_Sched_partial_solve_wit_4_aux.

Definition OS_Sched_partial_solve_wit_5_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (PreH1 : ((os_sched_locks (acquired)) <> 0)) (PreH2 : ((os_sched_ints (acquired)) = 0)) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_entry_source entered acquired )) (PreH5 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH6 : (0 <= (os_sched_ints (acquired)))) (PreH7 : ((os_sched_ints (acquired)) <= 255)) (PreH8 : (0 <= (os_sched_locks (acquired)))) (PreH9 : ((os_sched_locks (acquired)) <= 255)) (PreH10 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH12 : (sched_disabled_completed_clients critical entered )) (PreH13 : (sched_disabled_entry_source entered acquired )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (interrupt_saved_value mask cpu_sr )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (sched_fields_disabled_counter_frame environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
.

Definition OS_Sched_partial_solve_wit_5_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (PreH1 : ((os_sched_locks (acquired)) <> 0)) (PreH2 : ((os_sched_ints (acquired)) = 0)) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_entry_source entered acquired )) (PreH5 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH6 : (0 <= (os_sched_ints (acquired)))) (PreH7 : ((os_sched_ints (acquired)) <= 255)) (PreH8 : (0 <= (os_sched_locks (acquired)))) (PreH9 : ((os_sched_locks (acquired)) <= 255)) (PreH10 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH12 : (sched_disabled_completed_clients critical entered )) (PreH13 : (sched_disabled_entry_source entered acquired )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (interrupt_saved_value mask cpu_sr )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_fields_disabled_counter_frame environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((os_sched_locks (acquired)) <> 0) ” 
  &&  “ ((os_sched_ints (acquired)) = 0) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) )) ” 
  &&  “ (0 <= (os_sched_ints (acquired))) ” 
  &&  “ ((os_sched_ints (acquired)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (acquired))) ” 
  &&  “ ((os_sched_locks (acquired)) <= 255) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap ) ” 
  &&  “ (sched_disabled_completed_clients critical entered ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_fields_disabled_counter_frame environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
.

Definition OS_Sched_partial_solve_wit_5 := OS_Sched_partial_solve_wit_5_pure -> OS_Sched_partial_solve_wit_5_aux.

Definition OS_Sched_partial_solve_wit_6_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_ints (acquired)) <> 0)) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_entry_source entered acquired )) (PreH5 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH6 : (0 <= (os_sched_ints (acquired)))) (PreH7 : ((os_sched_ints (acquired)) <= 255)) (PreH8 : (0 <= (os_sched_locks (acquired)))) (PreH9 : ((os_sched_locks (acquired)) <= 255)) (PreH10 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH12 : (sched_disabled_completed_clients critical entered )) (PreH13 : (sched_disabled_entry_source entered acquired )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (interrupt_saved_value mask cpu_sr )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
|--
  “ (sched_disabled_completed_clients critical entered ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
.

Definition OS_Sched_partial_solve_wit_6_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_ints (acquired)) <> 0)) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_entry_source entered acquired )) (PreH5 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH6 : (0 <= (os_sched_ints (acquired)))) (PreH7 : ((os_sched_ints (acquired)) <= 255)) (PreH8 : (0 <= (os_sched_locks (acquired)))) (PreH9 : ((os_sched_locks (acquired)) <= 255)) (PreH10 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH12 : (sched_disabled_completed_clients critical entered )) (PreH13 : (sched_disabled_entry_source entered acquired )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
|--
  “ (sched_disabled_completed_clients critical entered ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((os_sched_ints (acquired)) <> 0) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) )) ” 
  &&  “ (0 <= (os_sched_ints (acquired))) ” 
  &&  “ ((os_sched_ints (acquired)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (acquired))) ” 
  &&  “ ((os_sched_locks (acquired)) <= 255) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap ) ” 
  &&  “ (sched_disabled_completed_clients critical entered ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
.

Definition OS_Sched_partial_solve_wit_6 := OS_Sched_partial_solve_wit_6_pure -> OS_Sched_partial_solve_wit_6_aux.

Definition OS_Sched_partial_solve_wit_7_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_locks (acquired)) <> 0)) (PreH3 : ((os_sched_ints (acquired)) = 0)) (PreH4 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : (sched_disabled_entry_source entered acquired )) (PreH6 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH7 : (0 <= (os_sched_ints (acquired)))) (PreH8 : ((os_sched_ints (acquired)) <= 255)) (PreH9 : (0 <= (os_sched_locks (acquired)))) (PreH10 : ((os_sched_locks (acquired)) <= 255)) (PreH11 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH13 : (sched_disabled_completed_clients critical entered )) (PreH14 : (sched_disabled_entry_source entered acquired )) (PreH15 : (UCOS2_state_inv sg acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
|--
  “ (sched_disabled_completed_clients critical entered ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
.

Definition OS_Sched_partial_solve_wit_7_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_locks (acquired)) <> 0)) (PreH3 : ((os_sched_ints (acquired)) = 0)) (PreH4 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : (sched_disabled_entry_source entered acquired )) (PreH6 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH7 : (0 <= (os_sched_ints (acquired)))) (PreH8 : ((os_sched_ints (acquired)) <= 255)) (PreH9 : (0 <= (os_sched_locks (acquired)))) (PreH10 : ((os_sched_locks (acquired)) <= 255)) (PreH11 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH13 : (sched_disabled_completed_clients critical entered )) (PreH14 : (sched_disabled_entry_source entered acquired )) (PreH15 : (UCOS2_state_inv sg acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
|--
  “ (sched_disabled_completed_clients critical entered ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((os_sched_locks (acquired)) <> 0) ” 
  &&  “ ((os_sched_ints (acquired)) = 0) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) )) ” 
  &&  “ (0 <= (os_sched_ints (acquired))) ” 
  &&  “ ((os_sched_ints (acquired)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (acquired))) ” 
  &&  “ ((os_sched_locks (acquired)) <= 255) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap ) ” 
  &&  “ (sched_disabled_completed_clients critical entered ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
.

Definition OS_Sched_partial_solve_wit_7 := OS_Sched_partial_solve_wit_7_pure -> OS_Sched_partial_solve_wit_7_aux.

Definition OS_Sched_partial_solve_wit_8 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_ints (acquired)) <> 0)) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_entry_source entered acquired )) (PreH5 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH6 : (0 <= (os_sched_ints (acquired)))) (PreH7 : ((os_sched_ints (acquired)) <= 255)) (PreH8 : (0 <= (os_sched_locks (acquired)))) (PreH9 : ((os_sched_locks (acquired)) <= 255)) (PreH10 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH12 : (sched_disabled_completed_clients critical entered )) (PreH13 : (sched_disabled_entry_source entered acquired )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_disabled_restore_pre environment critical entered_local sg entered mask cpu_sr acquired acquired frame )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((os_sched_ints (acquired)) <> 0) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) )) ” 
  &&  “ (0 <= (os_sched_ints (acquired))) ” 
  &&  “ ((os_sched_ints (acquired)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (acquired))) ” 
  &&  “ ((os_sched_locks (acquired)) <= 255) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap ) ” 
  &&  “ (sched_disabled_completed_clients critical entered ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  (sched_fields_disabled_restore_pre environment critical entered_local sg entered mask cpu_sr acquired acquired frame )
.

Definition OS_Sched_partial_solve_wit_9 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_locks (acquired)) <> 0)) (PreH3 : ((os_sched_ints (acquired)) = 0)) (PreH4 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : (sched_disabled_entry_source entered acquired )) (PreH6 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH7 : (0 <= (os_sched_ints (acquired)))) (PreH8 : ((os_sched_ints (acquired)) <= 255)) (PreH9 : (0 <= (os_sched_locks (acquired)))) (PreH10 : ((os_sched_locks (acquired)) <= 255)) (PreH11 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH13 : (sched_disabled_completed_clients critical entered )) (PreH14 : (sched_disabled_entry_source entered acquired )) (PreH15 : (UCOS2_state_inv sg acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_disabled_restore_pre environment critical entered_local sg entered mask cpu_sr acquired acquired frame )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((os_sched_locks (acquired)) <> 0) ” 
  &&  “ ((os_sched_ints (acquired)) = 0) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) )) ” 
  &&  “ (0 <= (os_sched_ints (acquired))) ” 
  &&  “ ((os_sched_ints (acquired)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (acquired))) ” 
  &&  “ ((os_sched_locks (acquired)) <= 255) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap ) ” 
  &&  “ (sched_disabled_completed_clients critical entered ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  (sched_fields_disabled_restore_pre environment critical entered_local sg entered mask cpu_sr acquired acquired frame )
.

Definition OS_Sched_partial_solve_wit_10_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (restore_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_locks (acquired)) <> 0)) (PreH3 : ((os_sched_ints (acquired)) = 0)) (PreH4 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : (sched_disabled_entry_source entered acquired )) (PreH6 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH7 : (0 <= (os_sched_ints (acquired)))) (PreH8 : ((os_sched_ints (acquired)) <= 255)) (PreH9 : (0 <= (os_sched_locks (acquired)))) (PreH10 : ((os_sched_locks (acquired)) <= 255)) (PreH11 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH13 : (sched_disabled_completed_clients critical entered )) (PreH14 : (sched_disabled_entry_source entered acquired )) (PreH15 : (UCOS2_state_inv sg acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (sched_fields_heap_cut (sched_fields_disabled_restore_pre (environment) (critical) (entered_local) (sg) (entered) (mask) (cpu_sr) (acquired) (acquired) (frame)) restore_heap )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OS_Sched_partial_solve_wit_10_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (restore_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_locks (acquired)) <> 0)) (PreH3 : ((os_sched_ints (acquired)) = 0)) (PreH4 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : (sched_disabled_entry_source entered acquired )) (PreH6 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH7 : (0 <= (os_sched_ints (acquired)))) (PreH8 : ((os_sched_ints (acquired)) <= 255)) (PreH9 : (0 <= (os_sched_locks (acquired)))) (PreH10 : ((os_sched_locks (acquired)) <= 255)) (PreH11 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH13 : (sched_disabled_completed_clients critical entered )) (PreH14 : (sched_disabled_entry_source entered acquired )) (PreH15 : (UCOS2_state_inv sg acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_heap_cut (sched_fields_disabled_restore_pre (environment) (critical) (entered_local) (sg) (entered) (mask) (cpu_sr) (acquired) (acquired) (frame)) restore_heap )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((os_sched_locks (acquired)) <> 0) ” 
  &&  “ ((os_sched_ints (acquired)) = 0) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) )) ” 
  &&  “ (0 <= (os_sched_ints (acquired))) ” 
  &&  “ ((os_sched_ints (acquired)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (acquired))) ” 
  &&  “ ((os_sched_locks (acquired)) <= 255) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap ) ” 
  &&  “ (sched_disabled_completed_clients critical entered ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  (sched_fields_heap_cut (sched_fields_disabled_restore_pre (environment) (critical) (entered_local) (sg) (entered) (mask) (cpu_sr) (acquired) (acquired) (frame)) restore_heap )
.

Definition OS_Sched_partial_solve_wit_10 := OS_Sched_partial_solve_wit_10_pure -> OS_Sched_partial_solve_wit_10_aux.

Definition OS_Sched_partial_solve_wit_11_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (restore_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_ints (acquired)) <> 0)) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_entry_source entered acquired )) (PreH5 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH6 : (0 <= (os_sched_ints (acquired)))) (PreH7 : ((os_sched_ints (acquired)) <= 255)) (PreH8 : (0 <= (os_sched_locks (acquired)))) (PreH9 : ((os_sched_locks (acquired)) <= 255)) (PreH10 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH12 : (sched_disabled_completed_clients critical entered )) (PreH13 : (sched_disabled_entry_source entered acquired )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (interrupt_saved_value mask cpu_sr )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (sched_fields_heap_cut (sched_fields_disabled_restore_pre (environment) (critical) (entered_local) (sg) (entered) (mask) (cpu_sr) (acquired) (acquired) (frame)) restore_heap )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OS_Sched_partial_solve_wit_11_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_heap: model) (cpu_sr: Z) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (saved_heap: model) (restore_heap: model) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : ((os_sched_ints (acquired)) <> 0)) (PreH3 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH4 : (sched_disabled_entry_source entered acquired )) (PreH5 : (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) ))) (PreH6 : (0 <= (os_sched_ints (acquired)))) (PreH7 : ((os_sched_ints (acquired)) <= 255)) (PreH8 : (0 <= (os_sched_locks (acquired)))) (PreH9 : ((os_sched_locks (acquired)) <= 255)) (PreH10 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap )) (PreH12 : (sched_disabled_completed_clients critical entered )) (PreH13 : (sched_disabled_entry_source entered acquired )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_heap_cut (sched_fields_disabled_restore_pre (environment) (critical) (entered_local) (sg) (entered) (mask) (cpu_sr) (acquired) (acquired) (frame)) restore_heap )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((os_sched_ints (acquired)) <> 0) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) )) ” 
  &&  “ (0 <= (os_sched_ints (acquired))) ” 
  &&  “ ((os_sched_ints (acquired)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (acquired))) ” 
  &&  “ ((os_sched_locks (acquired)) <= 255) ” 
  &&  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_fields_disabled_save_event environment critical sg view entered mask cpu_sr before acquired local entered_local frame first_heap saved_heap ) ” 
  &&  “ (sched_disabled_completed_clients critical entered ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  (sched_fields_heap_cut (sched_fields_disabled_restore_pre (environment) (critical) (entered_local) (sg) (entered) (mask) (cpu_sr) (acquired) (acquired) (frame)) restore_heap )
.

Definition OS_Sched_partial_solve_wit_11 := OS_Sched_partial_solve_wit_11_pure -> OS_Sched_partial_solve_wit_11_aux.

Definition OS_Sched_which_implies_wit_1 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  (sched_fields_disabled_pre environment critical local sg view mask before frame )
|--
  EX (first_heap: model) ,
  (sched_fields_heap_cut (sched_fields_disabled_pre (environment) (critical) (local) (sg) (view) (mask) (before) (frame)) first_heap )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (view: OsExecutionView) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  (sched_fields_disabled_pre environment critical local sg view mask before frame )
|--
  EX (first_heap: model) ,
  (sched_fields_heap_cut (sched_fields_disabled_pre (environment) (critical) (local) (sg) (view) (mask) (before) (frame)) first_heap )
).

Definition OS_Sched_which_implies_wit_2 := 
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_entry_source entered acquired )) ,
  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (sched_disabled_entry_source entered acquired ) ” 
  &&  “ (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) )) ” 
  &&  “ (0 <= (os_sched_ints (acquired))) ” 
  &&  “ ((os_sched_ints (acquired)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (acquired))) ” 
  &&  “ ((os_sched_locks (acquired)) <= 255) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_fields_disabled_counter_frame environment critical entered_local sg entered cpu_sr acquired acquired )
) \/
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_entry_source entered acquired )) ,
  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
|--
  “ ((os_sched_locks (acquired)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (acquired))) ” 
  &&  “ ((os_sched_ints (acquired)) <= 255) ” 
  &&  “ (0 <= (os_sched_ints (acquired))) ” 
  &&  “ (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) )) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_fields_disabled_counter_frame environment critical entered_local sg entered cpu_sr acquired acquired )
).

Definition OS_Sched_which_implies_wit_2_split_goal_1 := 
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_entry_source entered acquired )) ,
  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
|--
  “ ((os_sched_locks (acquired)) <= 255) ”
.

Definition OS_Sched_which_implies_wit_2_split_goal_2 := 
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_entry_source entered acquired )) ,
  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
|--
  “ (0 <= (os_sched_locks (acquired))) ”
.

Definition OS_Sched_which_implies_wit_2_split_goal_3 := 
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_entry_source entered acquired )) ,
  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
|--
  “ ((os_sched_ints (acquired)) <= 255) ”
.

Definition OS_Sched_which_implies_wit_2_split_goal_4 := 
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_entry_source entered acquired )) ,
  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
|--
  “ (0 <= (os_sched_ints (acquired))) ”
.

Definition OS_Sched_which_implies_wit_2_split_goal_5 := 
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_entry_source entered acquired )) ,
  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
|--
  “ (0 < ((os_sched_ints (acquired)) + (os_sched_locks (acquired)) )) ”
.

Definition OS_Sched_which_implies_wit_2_split_goal_spatial := 
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH2 : (sched_disabled_entry_source entered acquired )) ,
  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_fields_disabled_counter_frame environment critical entered_local sg entered cpu_sr acquired acquired )
.

Definition OS_Sched_which_implies_wit_3 := 
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_fields_disabled_counter_frame environment critical entered_local sg entered cpu_sr acquired acquired )
|--
  “ (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
) \/
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_fields_disabled_counter_frame environment critical entered_local sg entered cpu_sr acquired acquired )
|--
  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
).

Definition OS_Sched_which_implies_wit_3_split_goal_spatial := 
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_disabled_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (acquired)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (acquired)))
  **  (sched_fields_disabled_counter_frame environment critical entered_local sg entered cpu_sr acquired acquired )
|--
  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
.

Definition OS_Sched_which_implies_wit_4 := 
(
forall (frame: Assertion) (mask: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_disabled_completed_clients critical entered )) (PreH2 : (sched_disabled_entry_source entered acquired )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
|--
  (sched_fields_disabled_restore_pre environment critical entered_local sg entered mask cpu_sr acquired acquired frame )
) \/
(
forall (frame: Assertion) (mask: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_disabled_completed_clients critical entered )) (PreH2 : (sched_disabled_entry_source entered acquired )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
|--
  (sched_fields_disabled_restore_pre environment critical entered_local sg entered mask cpu_sr acquired acquired frame )
).

Definition OS_Sched_which_implies_wit_4_split_goal_spatial := 
forall (frame: Assertion) (mask: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (PreH1 : (sched_disabled_completed_clients critical entered )) (PreH2 : (sched_disabled_entry_source entered acquired )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (interrupt_saved_value mask cpu_sr )) ,
  (sched_fields_disabled_masked environment critical entered_local sg entered cpu_sr acquired acquired )
  **  (frame )
|--
  (sched_fields_disabled_restore_pre environment critical entered_local sg entered mask cpu_sr acquired acquired frame )
.

Definition OS_Sched_which_implies_wit_5 := 
(
forall (frame: Assertion) (mask: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) ,
  (sched_fields_disabled_restore_pre environment critical entered_local sg entered mask cpu_sr acquired acquired frame )
|--
  EX (restore_heap: model) ,
  (sched_fields_heap_cut (sched_fields_disabled_restore_pre (environment) (critical) (entered_local) (sg) (entered) (mask) (cpu_sr) (acquired) (acquired) (frame)) restore_heap )
) \/
(
forall (frame: Assertion) (mask: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (entered: OsExecutionView) (acquired: UCOS2_Verify_State) (entered_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) ,
  (sched_fields_disabled_restore_pre environment critical entered_local sg entered mask cpu_sr acquired acquired frame )
|--
  EX (restore_heap: model) ,
  (sched_fields_heap_cut (sched_fields_disabled_restore_pre (environment) (critical) (entered_local) (sg) (entered) (mask) (cpu_sr) (acquired) (acquired) (frame)) restore_heap )
).

Module Type VC_Correct.


Axiom proof_of_OS_Sched_safety_wit_1 : OS_Sched_safety_wit_1.
Axiom proof_of_OS_Sched_safety_wit_2 : OS_Sched_safety_wit_2.
Axiom proof_of_OS_Sched_safety_wit_3 : OS_Sched_safety_wit_3.
Axiom proof_of_OS_Sched_safety_wit_4 : OS_Sched_safety_wit_4.
Axiom proof_of_OS_Sched_entail_wit_1 : OS_Sched_entail_wit_1.
Axiom proof_of_OS_Sched_return_wit_1 : OS_Sched_return_wit_1.
Axiom proof_of_OS_Sched_return_wit_2 : OS_Sched_return_wit_2.
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
Axiom proof_of_OS_Sched_partial_solve_wit_7_pure : OS_Sched_partial_solve_wit_7_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_7 : OS_Sched_partial_solve_wit_7.
Axiom proof_of_OS_Sched_partial_solve_wit_8 : OS_Sched_partial_solve_wit_8.
Axiom proof_of_OS_Sched_partial_solve_wit_9 : OS_Sched_partial_solve_wit_9.
Axiom proof_of_OS_Sched_partial_solve_wit_10_pure : OS_Sched_partial_solve_wit_10_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_10 : OS_Sched_partial_solve_wit_10.
Axiom proof_of_OS_Sched_partial_solve_wit_11_pure : OS_Sched_partial_solve_wit_11_pure.
Axiom proof_of_OS_Sched_partial_solve_wit_11 : OS_Sched_partial_solve_wit_11.
Axiom proof_of_OS_Sched_which_implies_wit_1 : OS_Sched_which_implies_wit_1.
Axiom proof_of_OS_Sched_which_implies_wit_2 : OS_Sched_which_implies_wit_2.
Axiom proof_of_OS_Sched_which_implies_wit_3 : OS_Sched_which_implies_wit_3.
Axiom proof_of_OS_Sched_which_implies_wit_4 : OS_Sched_which_implies_wit_4.
Axiom proof_of_OS_Sched_which_implies_wit_5 : OS_Sched_which_implies_wit_5.

End VC_Correct.
