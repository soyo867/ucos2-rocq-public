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
Require Import Ucos2Verify.VC.code.task.spec.task_query_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OSTaskQuery -----*)

Definition OSTaskQuery_safety_wit_1 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre = 255)) (PreH2 : (prio_pre > 63)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (prio_pre = request)) (PreH8 : (p_task_data_pre = output)) (PreH9 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH10 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
  **  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskQuery_safety_wit_2 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <= 63)) (PreH2 : (0 <= request)) (PreH3 : (request <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (prio_pre = request)) (PreH7 : (p_task_data_pre = output)) (PreH8 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH9 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
  **  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskQuery_safety_wit_3 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (p_task_data_pre <> 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (0 <= request)) (PreH5 : (request <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (prio_pre = request)) (PreH9 : (p_task_data_pre = output)) (PreH10 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH11 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_save_post platform critical sg invocation origin mask before retval )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskQuery_safety_wit_4 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (p_task_data_pre <> 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (prio_pre = request)) (PreH8 : (p_task_data_pre = output)) (PreH9 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH10 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_save_post platform critical sg invocation origin mask before retval )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskQuery_safety_wit_5 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (critical_region_interval critical sg invocation before acquired )) (PreH4 : (p_task_data_pre <> 0)) (PreH5 : (prio_pre = 255)) (PreH6 : (prio_pre > 63)) (PreH7 : (0 <= request)) (PreH8 : (request <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (prio_pre = request)) (PreH12 : (p_task_data_pre = output)) (PreH13 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH14 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ False ”
.

Definition OSTaskQuery_safety_wit_6 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (critical_region_interval critical sg invocation before acquired )) (PreH4 : (p_task_data_pre <> 0)) (PreH5 : (prio_pre <= 63)) (PreH6 : (0 <= request)) (PreH7 : (request <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (prio_pre = request)) (PreH11 : (p_task_data_pre = output)) (PreH12 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH13 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ False ”
.

Definition OSTaskQuery_safety_wit_7 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_priority_resolution sg acquired caller request key )) (PreH4 : (key = resolved)) (PreH5 : (request = 255)) (PreH6 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH7 : (request = 255)) (PreH8 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH9 : (request = 255)) (PreH10 : (retval <= UINT_MAX)) (PreH11 : (retval >= 0)) (PreH12 : (prio_pre = 255)) (PreH13 : (interrupt_saved_value mask retval )) (PreH14 : (critical_region_interval critical sg invocation before acquired )) (PreH15 : (p_task_data_pre <> 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (prio_pre > 63)) (PreH18 : (0 <= request)) (PreH19 : (request <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (prio_pre = request)) (PreH23 : (p_task_data_pre = output)) (PreH24 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH25 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskQuery_safety_wit_8 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_priority_resolution sg acquired caller request key )) (PreH4 : (key = prio_pre)) (PreH5 : (prio_pre <> 255)) (PreH6 : (interrupt_saved_value mask retval )) (PreH7 : (critical_region_interval critical sg invocation before acquired )) (PreH8 : (p_task_data_pre <> 0)) (PreH9 : (prio_pre <= 63)) (PreH10 : (0 <= request)) (PreH11 : (request <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (prio_pre = request)) (PreH15 : (p_task_data_pre = output)) (PreH16 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH17 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskQuery_safety_wit_9 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : ((task_query_table_value (sg) (acquired) (key)) = 0)) (PreH3 : (0 <= key)) (PreH4 : (key <= 63)) (PreH5 : (task_query_priority_resolution sg acquired caller request key )) (PreH6 : (key = resolved)) (PreH7 : (request = 255)) (PreH8 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH9 : (request = 255)) (PreH10 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH11 : (request = 255)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : (retval >= 0)) (PreH14 : (prio_pre = 255)) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (p_task_data_pre <> 0)) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre > 63)) (PreH20 : (0 <= request)) (PreH21 : (request <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (prio_pre = request)) (PreH25 : (p_task_data_pre = output)) (PreH26 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH27 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskQuery_safety_wit_10 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = 0)) (PreH5 : (0 <= key)) (PreH6 : (key <= 63)) (PreH7 : (task_query_priority_resolution sg acquired caller request key )) (PreH8 : (key = prio_pre)) (PreH9 : (prio_pre <> 255)) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (p_task_data_pre <> 0)) (PreH13 : (prio_pre <= 63)) (PreH14 : (0 <= request)) (PreH15 : (request <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (prio_pre = request)) (PreH19 : (p_task_data_pre = output)) (PreH20 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH21 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskQuery_safety_wit_11 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH2 : (0 <= key)) (PreH3 : (key <= 63)) (PreH4 : (task_query_priority_resolution sg acquired caller request key )) (PreH5 : (key = resolved)) (PreH6 : (request = 255)) (PreH7 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH8 : (request = 255)) (PreH9 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH10 : (request = 255)) (PreH11 : (retval <= UINT_MAX)) (PreH12 : (retval >= 0)) (PreH13 : (prio_pre = 255)) (PreH14 : (interrupt_saved_value mask retval )) (PreH15 : (critical_region_interval critical sg invocation before acquired )) (PreH16 : (p_task_data_pre <> 0)) (PreH17 : (prio_pre = 255)) (PreH18 : (prio_pre > 63)) (PreH19 : (0 <= request)) (PreH20 : (request <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (prio_pre = request)) (PreH24 : (p_task_data_pre = output)) (PreH25 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH26 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OSTaskQuery_safety_wit_12 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH2 : (0 <= key)) (PreH3 : (key <= 63)) (PreH4 : (task_query_priority_resolution sg acquired caller request key )) (PreH5 : (key = prio_pre)) (PreH6 : (prio_pre <> 255)) (PreH7 : (interrupt_saved_value mask retval )) (PreH8 : (critical_region_interval critical sg invocation before acquired )) (PreH9 : (p_task_data_pre <> 0)) (PreH10 : (prio_pre <= 63)) (PreH11 : (0 <= request)) (PreH12 : (request <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (prio_pre = request)) (PreH16 : (p_task_data_pre = output)) (PreH17 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH18 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OSTaskQuery_safety_wit_13 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (task_query_reserved_entry acquired key )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH5 : (0 <= key)) (PreH6 : (key <= 63)) (PreH7 : (task_query_priority_resolution sg acquired caller request key )) (PreH8 : (key = resolved)) (PreH9 : (request = 255)) (PreH10 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH11 : (request = 255)) (PreH12 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH13 : (request = 255)) (PreH14 : (retval <= UINT_MAX)) (PreH15 : (retval >= 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (interrupt_saved_value mask retval )) (PreH18 : (critical_region_interval critical sg invocation before acquired )) (PreH19 : (p_task_data_pre <> 0)) (PreH20 : (prio_pre = 255)) (PreH21 : (prio_pre > 63)) (PreH22 : (0 <= request)) (PreH23 : (request <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (prio_pre = request)) (PreH27 : (p_task_data_pre = output)) (PreH28 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH29 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskQuery_safety_wit_14 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (task_query_reserved_entry acquired key )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (retval >= 0)) (PreH5 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH6 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH7 : (0 <= key)) (PreH8 : (key <= 63)) (PreH9 : (task_query_priority_resolution sg acquired caller request key )) (PreH10 : (key = prio_pre)) (PreH11 : (prio_pre <> 255)) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (critical_region_interval critical sg invocation before acquired )) (PreH14 : (p_task_data_pre <> 0)) (PreH15 : (prio_pre <= 63)) (PreH16 : (0 <= request)) (PreH17 : (request <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (prio_pre = request)) (PreH21 : (p_task_data_pre = output)) (PreH22 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH23 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskQuery_safety_wit_15 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (0 <= key)) (PreH3 : (key <= 63)) (PreH4 : (task_query_task_entry acquired key tid )) (PreH5 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH6 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH7 : ((Zlength (bytes)) = 64)) (PreH8 : (sizeof( "os_tcb" ) = 64)) (PreH9 : (0 <= (task_slot_addr (sg) (tid)))) (PreH10 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH11 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (0 <= output)) (PreH13 : ((output + 64 ) <= UINT_MAX)) (PreH14 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH16 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH17 : (0 <= key)) (PreH18 : (key <= 63)) (PreH19 : (task_query_priority_resolution sg acquired caller request key )) (PreH20 : (key = resolved)) (PreH21 : (request = 255)) (PreH22 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH23 : (request = 255)) (PreH24 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH25 : (request = 255)) (PreH26 : (retval <= UINT_MAX)) (PreH27 : (retval >= 0)) (PreH28 : (prio_pre = 255)) (PreH29 : (interrupt_saved_value mask retval )) (PreH30 : (critical_region_interval critical sg invocation before acquired )) (PreH31 : (p_task_data_pre <> 0)) (PreH32 : (prio_pre = 255)) (PreH33 : (prio_pre > 63)) (PreH34 : (0 <= request)) (PreH35 : (request <= 255)) (PreH36 : (0 <= UINT_MAX)) (PreH37 : (0 >= 0)) (PreH38 : (prio_pre = request)) (PreH39 : (p_task_data_pre = output)) (PreH40 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH41 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_success_frame sg acquired caller request output bytes )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskQuery_safety_wit_16 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (0 <= key)) (PreH5 : (key <= 63)) (PreH6 : (task_query_task_entry acquired key tid )) (PreH7 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH8 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH9 : ((Zlength (bytes)) = 64)) (PreH10 : (sizeof( "os_tcb" ) = 64)) (PreH11 : (0 <= (task_slot_addr (sg) (tid)))) (PreH12 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH13 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : (0 <= output)) (PreH15 : ((output + 64 ) <= UINT_MAX)) (PreH16 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH17 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH18 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH19 : (0 <= key)) (PreH20 : (key <= 63)) (PreH21 : (task_query_priority_resolution sg acquired caller request key )) (PreH22 : (key = prio_pre)) (PreH23 : (prio_pre <> 255)) (PreH24 : (interrupt_saved_value mask retval )) (PreH25 : (critical_region_interval critical sg invocation before acquired )) (PreH26 : (p_task_data_pre <> 0)) (PreH27 : (prio_pre <= 63)) (PreH28 : (0 <= request)) (PreH29 : (request <= 255)) (PreH30 : (0 <= UINT_MAX)) (PreH31 : (0 >= 0)) (PreH32 : (prio_pre = request)) (PreH33 : (p_task_data_pre = output)) (PreH34 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH35 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_success_frame sg acquired caller request output bytes )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskQuery_entail_wit_1 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre = request)) (PreH2 : (p_task_data_pre = output)) (PreH3 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH4 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
  **  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
  **  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (prio_pre = request)) (PreH4 : (p_task_data_pre = output)) (PreH5 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH6 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  TT && emp 
|--
  “ (prio_pre <= 255) ” 
  &&  “ (0 <= prio_pre) ”
  &&  emp
).

Definition OSTaskQuery_entail_wit_1_split_goal_1 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (prio_pre = request)) (PreH4 : (p_task_data_pre = output)) (PreH5 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH6 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (prio_pre <= 255)
.

Definition OSTaskQuery_entail_wit_1_split_goal_2 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (prio_pre = request)) (PreH4 : (p_task_data_pre = output)) (PreH5 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH6 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (0 <= prio_pre)
.

Definition OSTaskQuery_entail_wit_2 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (critical_region_interval critical sg invocation before acquired )) (PreH4 : (p_task_data_pre <> 0)) (PreH5 : (prio_pre = 255)) (PreH6 : (prio_pre > 63)) (PreH7 : (0 <= request)) (PreH8 : (request <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (prio_pre = request)) (PreH12 : (p_task_data_pre = output)) (PreH13 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH14 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (request = 255) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
.

Definition OSTaskQuery_entail_wit_3_1 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : ((task_query_table_value (sg) (acquired) (key)) = 0)) (PreH2 : (0 <= key)) (PreH3 : (key <= 63)) (PreH4 : (task_query_priority_resolution sg acquired caller request key )) (PreH5 : (key = resolved)) (PreH6 : (request = 255)) (PreH7 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH8 : (request = 255)) (PreH9 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH10 : (request = 255)) (PreH11 : (retval <= UINT_MAX)) (PreH12 : (retval >= 0)) (PreH13 : (prio_pre = 255)) (PreH14 : (interrupt_saved_value mask retval )) (PreH15 : (critical_region_interval critical sg invocation before acquired )) (PreH16 : (p_task_data_pre <> 0)) (PreH17 : (prio_pre = 255)) (PreH18 : (prio_pre > 63)) (PreH19 : (0 <= request)) (PreH20 : (request <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (prio_pre = request)) (PreH24 : (p_task_data_pre = output)) (PreH25 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH26 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = resolved) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request resolved ) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ” 
  &&  “ (request = 255) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : ((task_query_table_value (sg) (acquired) (key)) = 0)) (PreH2 : (0 <= key)) (PreH3 : (key <= 63)) (PreH4 : (task_query_priority_resolution sg acquired caller request key )) (PreH5 : (key = resolved)) (PreH6 : (request = 255)) (PreH7 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH8 : (request = 255)) (PreH9 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH10 : (request = 255)) (PreH11 : (retval <= UINT_MAX)) (PreH12 : (retval >= 0)) (PreH13 : (prio_pre = 255)) (PreH14 : (interrupt_saved_value mask retval )) (PreH15 : (critical_region_interval critical sg invocation before acquired )) (PreH16 : (p_task_data_pre <> 0)) (PreH17 : (prio_pre = 255)) (PreH18 : (prio_pre > 63)) (PreH19 : (0 <= request)) (PreH20 : (request <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (prio_pre = request)) (PreH24 : (p_task_data_pre = output)) (PreH25 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH26 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  TT && emp 
|--
  “ (UCOS2_state_inv sg acquired ) ”
  &&  emp
).

Definition OSTaskQuery_entail_wit_3_1_split_goal_1 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : ((task_query_table_value (sg) (acquired) (key)) = 0)) (PreH2 : (0 <= key)) (PreH3 : (key <= 63)) (PreH4 : (task_query_priority_resolution sg acquired caller request key )) (PreH5 : (key = resolved)) (PreH6 : (request = 255)) (PreH7 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH8 : (request = 255)) (PreH9 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH10 : (request = 255)) (PreH11 : (retval <= UINT_MAX)) (PreH12 : (retval >= 0)) (PreH13 : (prio_pre = 255)) (PreH14 : (interrupt_saved_value mask retval )) (PreH15 : (critical_region_interval critical sg invocation before acquired )) (PreH16 : (p_task_data_pre <> 0)) (PreH17 : (prio_pre = 255)) (PreH18 : (prio_pre > 63)) (PreH19 : (0 <= request)) (PreH20 : (request <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (prio_pre = request)) (PreH24 : (p_task_data_pre = output)) (PreH25 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH26 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (UCOS2_state_inv sg acquired )
.

Definition OSTaskQuery_entail_wit_3_2 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval_2: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : ((task_query_table_value (sg) (acquired) (key)) = 0)) (PreH2 : (0 <= key)) (PreH3 : (key <= 63)) (PreH4 : (task_query_priority_resolution sg acquired caller request key )) (PreH5 : (key = prio_pre)) (PreH6 : (prio_pre <> 255)) (PreH7 : (interrupt_saved_value mask retval_2 )) (PreH8 : (critical_region_interval critical sg invocation before acquired )) (PreH9 : (p_task_data_pre <> 0)) (PreH10 : (prio_pre <= 63)) (PreH11 : (0 <= request)) (PreH12 : (request <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (prio_pre = request)) (PreH16 : (p_task_data_pre = output)) (PreH17 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH18 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (task_query_restore_pre platform critical sg invocation origin retval_2 acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (retval_2 <= UINT_MAX) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = prio_pre) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (interrupt_saved_value mask retval_2 ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (task_query_restore_pre platform critical sg invocation origin retval_2 acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval_2: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (retval_2 <= UINT_MAX)) (PreH2 : (retval_2 >= 0)) (PreH3 : ((task_query_table_value (sg) (acquired) (key)) = 0)) (PreH4 : (0 <= key)) (PreH5 : (key <= 63)) (PreH6 : (task_query_priority_resolution sg acquired caller request key )) (PreH7 : (key = prio_pre)) (PreH8 : (prio_pre <> 255)) (PreH9 : (interrupt_saved_value mask retval_2 )) (PreH10 : (critical_region_interval critical sg invocation before acquired )) (PreH11 : (p_task_data_pre <> 0)) (PreH12 : (prio_pre <= 63)) (PreH13 : (0 <= request)) (PreH14 : (request <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (prio_pre = request)) (PreH18 : (p_task_data_pre = output)) (PreH19 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH20 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  TT && emp 
|--
  “ (UCOS2_state_inv sg acquired ) ”
  &&  emp
).

Definition OSTaskQuery_entail_wit_3_2_split_goal_1 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval_2: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (retval_2 <= UINT_MAX)) (PreH2 : (retval_2 >= 0)) (PreH3 : ((task_query_table_value (sg) (acquired) (key)) = 0)) (PreH4 : (0 <= key)) (PreH5 : (key <= 63)) (PreH6 : (task_query_priority_resolution sg acquired caller request key )) (PreH7 : (key = prio_pre)) (PreH8 : (prio_pre <> 255)) (PreH9 : (interrupt_saved_value mask retval_2 )) (PreH10 : (critical_region_interval critical sg invocation before acquired )) (PreH11 : (p_task_data_pre <> 0)) (PreH12 : (prio_pre <= 63)) (PreH13 : (0 <= request)) (PreH14 : (request <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (prio_pre = request)) (PreH18 : (p_task_data_pre = output)) (PreH19 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH20 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (UCOS2_state_inv sg acquired )
.

Definition OSTaskQuery_entail_wit_4_1 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH2 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH3 : (0 <= key)) (PreH4 : (key <= 63)) (PreH5 : (task_query_priority_resolution sg acquired caller request key )) (PreH6 : (key = resolved)) (PreH7 : (request = 255)) (PreH8 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH9 : (request = 255)) (PreH10 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH11 : (request = 255)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : (retval >= 0)) (PreH14 : (prio_pre = 255)) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (p_task_data_pre <> 0)) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre > 63)) (PreH20 : (0 <= request)) (PreH21 : (request <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (prio_pre = request)) (PreH25 : (p_task_data_pre = output)) (PreH26 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH27 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = resolved) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request resolved ) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ” 
  &&  “ (request = 255) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH2 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH3 : (0 <= key)) (PreH4 : (key <= 63)) (PreH5 : (task_query_priority_resolution sg acquired caller request key )) (PreH6 : (key = resolved)) (PreH7 : (request = 255)) (PreH8 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH9 : (request = 255)) (PreH10 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH11 : (request = 255)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : (retval >= 0)) (PreH14 : (prio_pre = 255)) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (p_task_data_pre <> 0)) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre > 63)) (PreH20 : (0 <= request)) (PreH21 : (request <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (prio_pre = request)) (PreH25 : (p_task_data_pre = output)) (PreH26 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH27 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  TT && emp 
|--
  “ (UCOS2_state_inv sg acquired ) ”
  &&  emp
).

Definition OSTaskQuery_entail_wit_4_1_split_goal_1 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH2 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH3 : (0 <= key)) (PreH4 : (key <= 63)) (PreH5 : (task_query_priority_resolution sg acquired caller request key )) (PreH6 : (key = resolved)) (PreH7 : (request = 255)) (PreH8 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH9 : (request = 255)) (PreH10 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH11 : (request = 255)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : (retval >= 0)) (PreH14 : (prio_pre = 255)) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (p_task_data_pre <> 0)) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre > 63)) (PreH20 : (0 <= request)) (PreH21 : (request <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (prio_pre = request)) (PreH25 : (p_task_data_pre = output)) (PreH26 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH27 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (UCOS2_state_inv sg acquired )
.

Definition OSTaskQuery_entail_wit_4_2 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval_2: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH2 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH3 : (0 <= key)) (PreH4 : (key <= 63)) (PreH5 : (task_query_priority_resolution sg acquired caller request key )) (PreH6 : (key = prio_pre)) (PreH7 : (prio_pre <> 255)) (PreH8 : (interrupt_saved_value mask retval_2 )) (PreH9 : (critical_region_interval critical sg invocation before acquired )) (PreH10 : (p_task_data_pre <> 0)) (PreH11 : (prio_pre <= 63)) (PreH12 : (0 <= request)) (PreH13 : (request <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (prio_pre = request)) (PreH17 : (p_task_data_pre = output)) (PreH18 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH19 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (task_query_restore_pre platform critical sg invocation origin retval_2 acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (retval_2 <= UINT_MAX) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = prio_pre) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (interrupt_saved_value mask retval_2 ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (task_query_restore_pre platform critical sg invocation origin retval_2 acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval_2: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (retval_2 <= UINT_MAX)) (PreH2 : (retval_2 >= 0)) (PreH3 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH5 : (0 <= key)) (PreH6 : (key <= 63)) (PreH7 : (task_query_priority_resolution sg acquired caller request key )) (PreH8 : (key = prio_pre)) (PreH9 : (prio_pre <> 255)) (PreH10 : (interrupt_saved_value mask retval_2 )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (p_task_data_pre <> 0)) (PreH13 : (prio_pre <= 63)) (PreH14 : (0 <= request)) (PreH15 : (request <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (prio_pre = request)) (PreH19 : (p_task_data_pre = output)) (PreH20 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH21 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  TT && emp 
|--
  “ (UCOS2_state_inv sg acquired ) ”
  &&  emp
).

Definition OSTaskQuery_entail_wit_4_2_split_goal_1 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval_2: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (retval_2 <= UINT_MAX)) (PreH2 : (retval_2 >= 0)) (PreH3 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH5 : (0 <= key)) (PreH6 : (key <= 63)) (PreH7 : (task_query_priority_resolution sg acquired caller request key )) (PreH8 : (key = prio_pre)) (PreH9 : (prio_pre <> 255)) (PreH10 : (interrupt_saved_value mask retval_2 )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (p_task_data_pre <> 0)) (PreH13 : (prio_pre <= 63)) (PreH14 : (0 <= request)) (PreH15 : (request <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (prio_pre = request)) (PreH19 : (p_task_data_pre = output)) (PreH20 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH21 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (UCOS2_state_inv sg acquired )
.

Definition OSTaskQuery_entail_wit_5_1 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH3 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH4 : (0 <= key)) (PreH5 : (key <= 63)) (PreH6 : (task_query_priority_resolution sg acquired caller request key )) (PreH7 : (key = resolved)) (PreH8 : (request = 255)) (PreH9 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH10 : (request = 255)) (PreH11 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH12 : (request = 255)) (PreH13 : (retval <= UINT_MAX)) (PreH14 : (retval >= 0)) (PreH15 : (prio_pre = 255)) (PreH16 : (interrupt_saved_value mask retval )) (PreH17 : (critical_region_interval critical sg invocation before acquired )) (PreH18 : (p_task_data_pre <> 0)) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre > 63)) (PreH21 : (0 <= request)) (PreH22 : (request <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (prio_pre = request)) (PreH26 : (p_task_data_pre = output)) (PreH27 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH28 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (task_query_reserved_entry acquired key ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = resolved) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request resolved ) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ” 
  &&  “ (request = 255) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH3 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH4 : (0 <= key)) (PreH5 : (key <= 63)) (PreH6 : (task_query_priority_resolution sg acquired caller request key )) (PreH7 : (key = resolved)) (PreH8 : (request = 255)) (PreH9 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH10 : (request = 255)) (PreH11 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH12 : (request = 255)) (PreH13 : (retval <= UINT_MAX)) (PreH14 : (retval >= 0)) (PreH15 : (prio_pre = 255)) (PreH16 : (interrupt_saved_value mask retval )) (PreH17 : (critical_region_interval critical sg invocation before acquired )) (PreH18 : (p_task_data_pre <> 0)) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre > 63)) (PreH21 : (0 <= request)) (PreH22 : (request <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (prio_pre = request)) (PreH26 : (p_task_data_pre = output)) (PreH27 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH28 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  TT && emp 
|--
  “ (task_query_reserved_entry acquired resolved ) ”
  &&  emp
).

Definition OSTaskQuery_entail_wit_5_1_split_goal_1 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH3 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH4 : (0 <= key)) (PreH5 : (key <= 63)) (PreH6 : (task_query_priority_resolution sg acquired caller request key )) (PreH7 : (key = resolved)) (PreH8 : (request = 255)) (PreH9 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH10 : (request = 255)) (PreH11 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH12 : (request = 255)) (PreH13 : (retval <= UINT_MAX)) (PreH14 : (retval >= 0)) (PreH15 : (prio_pre = 255)) (PreH16 : (interrupt_saved_value mask retval )) (PreH17 : (critical_region_interval critical sg invocation before acquired )) (PreH18 : (p_task_data_pre <> 0)) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre > 63)) (PreH21 : (0 <= request)) (PreH22 : (request <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (prio_pre = request)) (PreH26 : (p_task_data_pre = output)) (PreH27 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH28 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_reserved_entry acquired resolved )
.

Definition OSTaskQuery_entail_wit_5_2 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval_2: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (retval_2 <= UINT_MAX)) (PreH3 : (retval_2 >= 0)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH5 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH6 : (0 <= key)) (PreH7 : (key <= 63)) (PreH8 : (task_query_priority_resolution sg acquired caller request key )) (PreH9 : (key = prio_pre)) (PreH10 : (prio_pre <> 255)) (PreH11 : (interrupt_saved_value mask retval_2 )) (PreH12 : (critical_region_interval critical sg invocation before acquired )) (PreH13 : (p_task_data_pre <> 0)) (PreH14 : (prio_pre <= 63)) (PreH15 : (0 <= request)) (PreH16 : (request <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (prio_pre = request)) (PreH20 : (p_task_data_pre = output)) (PreH21 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH22 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (task_query_restore_pre platform critical sg invocation origin retval_2 acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (task_query_reserved_entry acquired key ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (retval_2 <= UINT_MAX) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = prio_pre) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (interrupt_saved_value mask retval_2 ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (task_query_restore_pre platform critical sg invocation origin retval_2 acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval_2: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (retval_2 <= UINT_MAX)) (PreH3 : (retval_2 >= 0)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH5 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH6 : (0 <= key)) (PreH7 : (key <= 63)) (PreH8 : (task_query_priority_resolution sg acquired caller request key )) (PreH9 : (key = prio_pre)) (PreH10 : (prio_pre <> 255)) (PreH11 : (interrupt_saved_value mask retval_2 )) (PreH12 : (critical_region_interval critical sg invocation before acquired )) (PreH13 : (p_task_data_pre <> 0)) (PreH14 : (prio_pre <= 63)) (PreH15 : (0 <= request)) (PreH16 : (request <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (prio_pre = request)) (PreH20 : (p_task_data_pre = output)) (PreH21 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH22 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  TT && emp 
|--
  “ (task_query_reserved_entry acquired prio_pre ) ”
  &&  emp
).

Definition OSTaskQuery_entail_wit_5_2_split_goal_1 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval_2: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (retval_2 <= UINT_MAX)) (PreH3 : (retval_2 >= 0)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH5 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH6 : (0 <= key)) (PreH7 : (key <= 63)) (PreH8 : (task_query_priority_resolution sg acquired caller request key )) (PreH9 : (key = prio_pre)) (PreH10 : (prio_pre <> 255)) (PreH11 : (interrupt_saved_value mask retval_2 )) (PreH12 : (critical_region_interval critical sg invocation before acquired )) (PreH13 : (p_task_data_pre <> 0)) (PreH14 : (prio_pre <= 63)) (PreH15 : (0 <= request)) (PreH16 : (request <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (prio_pre = request)) (PreH20 : (p_task_data_pre = output)) (PreH21 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH22 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_reserved_entry acquired prio_pre )
.

Definition OSTaskQuery_entail_wit_6_1 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_task_entry acquired key tid )) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH5 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH6 : ((Zlength (bytes)) = 64)) (PreH7 : (sizeof( "os_tcb" ) = 64)) (PreH8 : (0 <= (task_slot_addr (sg) (tid)))) (PreH9 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH10 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= output)) (PreH12 : ((output + 64 ) <= UINT_MAX)) (PreH13 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH16 : (0 <= key)) (PreH17 : (key <= 63)) (PreH18 : (task_query_priority_resolution sg acquired caller request key )) (PreH19 : (key = resolved)) (PreH20 : (request = 255)) (PreH21 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH22 : (request = 255)) (PreH23 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH24 : (request = 255)) (PreH25 : (retval <= UINT_MAX)) (PreH26 : (retval >= 0)) (PreH27 : (prio_pre = 255)) (PreH28 : (interrupt_saved_value mask retval )) (PreH29 : (critical_region_interval critical sg invocation before acquired )) (PreH30 : (p_task_data_pre <> 0)) (PreH31 : (prio_pre = 255)) (PreH32 : (prio_pre > 63)) (PreH33 : (0 <= request)) (PreH34 : (request <= 255)) (PreH35 : (0 <= UINT_MAX)) (PreH36 : (0 >= 0)) (PreH37 : (prio_pre = request)) (PreH38 : (p_task_data_pre = output)) (PreH39 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH40 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_task_entry acquired key tid ) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_query_source_byte_view sg acquired tid t bytes ) ” 
  &&  “ ((Zlength (bytes)) = 64) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ” 
  &&  “ (0 <= (task_slot_addr (sg) (tid))) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= output) ” 
  &&  “ ((output + 64 ) <= UINT_MAX) ” 
  &&  “ ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = resolved) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request resolved ) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ” 
  &&  “ (request = 255) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_task_entry acquired key tid )) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH5 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH6 : ((Zlength (bytes)) = 64)) (PreH7 : (sizeof( "os_tcb" ) = 64)) (PreH8 : (0 <= (task_slot_addr (sg) (tid)))) (PreH9 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH10 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= output)) (PreH12 : ((output + 64 ) <= UINT_MAX)) (PreH13 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH16 : (0 <= key)) (PreH17 : (key <= 63)) (PreH18 : (task_query_priority_resolution sg acquired caller request key )) (PreH19 : (key = resolved)) (PreH20 : (request = 255)) (PreH21 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH22 : (request = 255)) (PreH23 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH24 : (request = 255)) (PreH25 : (retval <= UINT_MAX)) (PreH26 : (retval >= 0)) (PreH27 : (prio_pre = 255)) (PreH28 : (interrupt_saved_value mask retval )) (PreH29 : (critical_region_interval critical sg invocation before acquired )) (PreH30 : (p_task_data_pre <> 0)) (PreH31 : (prio_pre = 255)) (PreH32 : (prio_pre > 63)) (PreH33 : (0 <= request)) (PreH34 : (request <= 255)) (PreH35 : (0 <= UINT_MAX)) (PreH36 : (0 >= 0)) (PreH37 : (prio_pre = request)) (PreH38 : (p_task_data_pre = output)) (PreH39 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH40 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  TT && emp 
|--
  “ (UCOS2_state_inv sg acquired ) ”
  &&  emp
).

Definition OSTaskQuery_entail_wit_6_1_split_goal_1 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_task_entry acquired key tid )) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH5 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH6 : ((Zlength (bytes)) = 64)) (PreH7 : (sizeof( "os_tcb" ) = 64)) (PreH8 : (0 <= (task_slot_addr (sg) (tid)))) (PreH9 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH10 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= output)) (PreH12 : ((output + 64 ) <= UINT_MAX)) (PreH13 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH16 : (0 <= key)) (PreH17 : (key <= 63)) (PreH18 : (task_query_priority_resolution sg acquired caller request key )) (PreH19 : (key = resolved)) (PreH20 : (request = 255)) (PreH21 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH22 : (request = 255)) (PreH23 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH24 : (request = 255)) (PreH25 : (retval <= UINT_MAX)) (PreH26 : (retval >= 0)) (PreH27 : (prio_pre = 255)) (PreH28 : (interrupt_saved_value mask retval )) (PreH29 : (critical_region_interval critical sg invocation before acquired )) (PreH30 : (p_task_data_pre <> 0)) (PreH31 : (prio_pre = 255)) (PreH32 : (prio_pre > 63)) (PreH33 : (0 <= request)) (PreH34 : (request <= 255)) (PreH35 : (0 <= UINT_MAX)) (PreH36 : (0 >= 0)) (PreH37 : (prio_pre = request)) (PreH38 : (p_task_data_pre = output)) (PreH39 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH40 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (UCOS2_state_inv sg acquired )
.

Definition OSTaskQuery_entail_wit_6_2 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval_2: Z) (acquired: UCOS2_Verify_State) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_task_entry acquired key tid )) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH5 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH6 : ((Zlength (bytes)) = 64)) (PreH7 : (sizeof( "os_tcb" ) = 64)) (PreH8 : (0 <= (task_slot_addr (sg) (tid)))) (PreH9 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH10 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= output)) (PreH12 : ((output + 64 ) <= UINT_MAX)) (PreH13 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH16 : (0 <= key)) (PreH17 : (key <= 63)) (PreH18 : (task_query_priority_resolution sg acquired caller request key )) (PreH19 : (key = prio_pre)) (PreH20 : (prio_pre <> 255)) (PreH21 : (interrupt_saved_value mask retval_2 )) (PreH22 : (critical_region_interval critical sg invocation before acquired )) (PreH23 : (p_task_data_pre <> 0)) (PreH24 : (prio_pre <= 63)) (PreH25 : (0 <= request)) (PreH26 : (request <= 255)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (0 >= 0)) (PreH29 : (prio_pre = request)) (PreH30 : (p_task_data_pre = output)) (PreH31 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH32 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (task_query_restore_pre platform critical sg invocation origin retval_2 acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (retval_2 <= UINT_MAX) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_task_entry acquired key tid ) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_query_source_byte_view sg acquired tid t bytes ) ” 
  &&  “ ((Zlength (bytes)) = 64) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ” 
  &&  “ (0 <= (task_slot_addr (sg) (tid))) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= output) ” 
  &&  “ ((output + 64 ) <= UINT_MAX) ” 
  &&  “ ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = prio_pre) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (interrupt_saved_value mask retval_2 ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  (task_query_restore_pre platform critical sg invocation origin retval_2 acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval_2: Z) (acquired: UCOS2_Verify_State) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (retval_2 <= UINT_MAX)) (PreH2 : (retval_2 >= 0)) (PreH3 : (0 <= key)) (PreH4 : (key <= 63)) (PreH5 : (task_query_task_entry acquired key tid )) (PreH6 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH7 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH8 : ((Zlength (bytes)) = 64)) (PreH9 : (sizeof( "os_tcb" ) = 64)) (PreH10 : (0 <= (task_slot_addr (sg) (tid)))) (PreH11 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH12 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH13 : (0 <= output)) (PreH14 : ((output + 64 ) <= UINT_MAX)) (PreH15 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH16 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH17 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH18 : (0 <= key)) (PreH19 : (key <= 63)) (PreH20 : (task_query_priority_resolution sg acquired caller request key )) (PreH21 : (key = prio_pre)) (PreH22 : (prio_pre <> 255)) (PreH23 : (interrupt_saved_value mask retval_2 )) (PreH24 : (critical_region_interval critical sg invocation before acquired )) (PreH25 : (p_task_data_pre <> 0)) (PreH26 : (prio_pre <= 63)) (PreH27 : (0 <= request)) (PreH28 : (request <= 255)) (PreH29 : (0 <= UINT_MAX)) (PreH30 : (0 >= 0)) (PreH31 : (prio_pre = request)) (PreH32 : (p_task_data_pre = output)) (PreH33 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH34 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  TT && emp 
|--
  “ (UCOS2_state_inv sg acquired ) ”
  &&  emp
).

Definition OSTaskQuery_entail_wit_6_2_split_goal_1 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval_2: Z) (acquired: UCOS2_Verify_State) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (retval_2 <= UINT_MAX)) (PreH2 : (retval_2 >= 0)) (PreH3 : (0 <= key)) (PreH4 : (key <= 63)) (PreH5 : (task_query_task_entry acquired key tid )) (PreH6 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH7 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH8 : ((Zlength (bytes)) = 64)) (PreH9 : (sizeof( "os_tcb" ) = 64)) (PreH10 : (0 <= (task_slot_addr (sg) (tid)))) (PreH11 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH12 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH13 : (0 <= output)) (PreH14 : ((output + 64 ) <= UINT_MAX)) (PreH15 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH16 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH17 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH18 : (0 <= key)) (PreH19 : (key <= 63)) (PreH20 : (task_query_priority_resolution sg acquired caller request key )) (PreH21 : (key = prio_pre)) (PreH22 : (prio_pre <> 255)) (PreH23 : (interrupt_saved_value mask retval_2 )) (PreH24 : (critical_region_interval critical sg invocation before acquired )) (PreH25 : (p_task_data_pre <> 0)) (PreH26 : (prio_pre <= 63)) (PreH27 : (0 <= request)) (PreH28 : (request <= 255)) (PreH29 : (0 <= UINT_MAX)) (PreH30 : (0 >= 0)) (PreH31 : (prio_pre = request)) (PreH32 : (p_task_data_pre = output)) (PreH33 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH34 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (UCOS2_state_inv sg acquired )
.

Definition OSTaskQuery_return_wit_1 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (0 <= key)) (PreH3 : (key <= 63)) (PreH4 : (task_query_task_entry acquired key tid )) (PreH5 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH6 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH7 : ((Zlength (bytes)) = 64)) (PreH8 : (sizeof( "os_tcb" ) = 64)) (PreH9 : (0 <= (task_slot_addr (sg) (tid)))) (PreH10 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH11 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (0 <= output)) (PreH13 : ((output + 64 ) <= UINT_MAX)) (PreH14 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH16 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH17 : (0 <= key)) (PreH18 : (key <= 63)) (PreH19 : (task_query_priority_resolution sg acquired caller request key )) (PreH20 : (key = resolved)) (PreH21 : (request = 255)) (PreH22 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH23 : (request = 255)) (PreH24 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH25 : (request = 255)) (PreH26 : (retval <= UINT_MAX)) (PreH27 : (retval >= 0)) (PreH28 : (prio_pre = 255)) (PreH29 : (interrupt_saved_value mask retval )) (PreH30 : (critical_region_interval critical sg invocation before acquired )) (PreH31 : (p_task_data_pre <> 0)) (PreH32 : (prio_pre = 255)) (PreH33 : (prio_pre > 63)) (PreH34 : (0 <= request)) (PreH35 : (request <= 255)) (PreH36 : (0 <= UINT_MAX)) (PreH37 : (0 >= 0)) (PreH38 : (prio_pre = request)) (PreH39 : (p_task_data_pre = output)) (PreH40 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH41 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 0 X )
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (0 <= key)) (PreH3 : (key <= 63)) (PreH4 : (task_query_task_entry acquired key tid )) (PreH5 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH6 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH7 : ((Zlength (bytes)) = 64)) (PreH8 : (sizeof( "os_tcb" ) = 64)) (PreH9 : (0 <= (task_slot_addr (sg) (tid)))) (PreH10 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH11 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (0 <= output)) (PreH13 : ((output + 64 ) <= UINT_MAX)) (PreH14 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH16 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH17 : (0 <= key)) (PreH18 : (key <= 63)) (PreH19 : (task_query_priority_resolution sg acquired caller request key )) (PreH20 : (key = resolved)) (PreH21 : (request = 255)) (PreH22 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH23 : (request = 255)) (PreH24 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH25 : (request = 255)) (PreH26 : (retval <= UINT_MAX)) (PreH27 : (retval >= 0)) (PreH28 : (prio_pre = 255)) (PreH29 : (interrupt_saved_value mask retval )) (PreH30 : (critical_region_interval critical sg invocation before acquired )) (PreH31 : (p_task_data_pre <> 0)) (PreH32 : (prio_pre = 255)) (PreH33 : (prio_pre > 63)) (PreH34 : (0 <= request)) (PreH35 : (request <= 255)) (PreH36 : (0 <= UINT_MAX)) (PreH37 : (0 >= 0)) (PreH38 : (prio_pre = request)) (PreH39 : (p_task_data_pre = output)) (PreH40 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH41 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 0 X )
).

Definition OSTaskQuery_return_wit_1_split_goal_spatial := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (0 <= key)) (PreH3 : (key <= 63)) (PreH4 : (task_query_task_entry acquired key tid )) (PreH5 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH6 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH7 : ((Zlength (bytes)) = 64)) (PreH8 : (sizeof( "os_tcb" ) = 64)) (PreH9 : (0 <= (task_slot_addr (sg) (tid)))) (PreH10 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH11 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (0 <= output)) (PreH13 : ((output + 64 ) <= UINT_MAX)) (PreH14 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH16 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH17 : (0 <= key)) (PreH18 : (key <= 63)) (PreH19 : (task_query_priority_resolution sg acquired caller request key )) (PreH20 : (key = resolved)) (PreH21 : (request = 255)) (PreH22 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH23 : (request = 255)) (PreH24 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH25 : (request = 255)) (PreH26 : (retval <= UINT_MAX)) (PreH27 : (retval >= 0)) (PreH28 : (prio_pre = 255)) (PreH29 : (interrupt_saved_value mask retval )) (PreH30 : (critical_region_interval critical sg invocation before acquired )) (PreH31 : (p_task_data_pre <> 0)) (PreH32 : (prio_pre = 255)) (PreH33 : (prio_pre > 63)) (PreH34 : (0 <= request)) (PreH35 : (request <= 255)) (PreH36 : (0 <= UINT_MAX)) (PreH37 : (0 >= 0)) (PreH38 : (prio_pre = request)) (PreH39 : (p_task_data_pre = output)) (PreH40 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH41 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 0 X )
.

Definition OSTaskQuery_return_wit_2 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (0 <= key)) (PreH5 : (key <= 63)) (PreH6 : (task_query_task_entry acquired key tid )) (PreH7 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH8 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH9 : ((Zlength (bytes)) = 64)) (PreH10 : (sizeof( "os_tcb" ) = 64)) (PreH11 : (0 <= (task_slot_addr (sg) (tid)))) (PreH12 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH13 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : (0 <= output)) (PreH15 : ((output + 64 ) <= UINT_MAX)) (PreH16 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH17 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH18 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH19 : (0 <= key)) (PreH20 : (key <= 63)) (PreH21 : (task_query_priority_resolution sg acquired caller request key )) (PreH22 : (key = prio_pre)) (PreH23 : (prio_pre <> 255)) (PreH24 : (interrupt_saved_value mask retval )) (PreH25 : (critical_region_interval critical sg invocation before acquired )) (PreH26 : (p_task_data_pre <> 0)) (PreH27 : (prio_pre <= 63)) (PreH28 : (0 <= request)) (PreH29 : (request <= 255)) (PreH30 : (0 <= UINT_MAX)) (PreH31 : (0 >= 0)) (PreH32 : (prio_pre = request)) (PreH33 : (p_task_data_pre = output)) (PreH34 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH35 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 0 X )
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (0 <= key)) (PreH5 : (key <= 63)) (PreH6 : (task_query_task_entry acquired key tid )) (PreH7 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH8 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH9 : ((Zlength (bytes)) = 64)) (PreH10 : (sizeof( "os_tcb" ) = 64)) (PreH11 : (0 <= (task_slot_addr (sg) (tid)))) (PreH12 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH13 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : (0 <= output)) (PreH15 : ((output + 64 ) <= UINT_MAX)) (PreH16 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH17 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH18 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH19 : (0 <= key)) (PreH20 : (key <= 63)) (PreH21 : (task_query_priority_resolution sg acquired caller request key )) (PreH22 : (key = prio_pre)) (PreH23 : (prio_pre <> 255)) (PreH24 : (interrupt_saved_value mask retval )) (PreH25 : (critical_region_interval critical sg invocation before acquired )) (PreH26 : (p_task_data_pre <> 0)) (PreH27 : (prio_pre <= 63)) (PreH28 : (0 <= request)) (PreH29 : (request <= 255)) (PreH30 : (0 <= UINT_MAX)) (PreH31 : (0 >= 0)) (PreH32 : (prio_pre = request)) (PreH33 : (p_task_data_pre = output)) (PreH34 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH35 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 0 X )
).

Definition OSTaskQuery_return_wit_2_split_goal_spatial := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (0 <= key)) (PreH5 : (key <= 63)) (PreH6 : (task_query_task_entry acquired key tid )) (PreH7 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH8 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH9 : ((Zlength (bytes)) = 64)) (PreH10 : (sizeof( "os_tcb" ) = 64)) (PreH11 : (0 <= (task_slot_addr (sg) (tid)))) (PreH12 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH13 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : (0 <= output)) (PreH15 : ((output + 64 ) <= UINT_MAX)) (PreH16 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH17 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH18 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH19 : (0 <= key)) (PreH20 : (key <= 63)) (PreH21 : (task_query_priority_resolution sg acquired caller request key )) (PreH22 : (key = prio_pre)) (PreH23 : (prio_pre <> 255)) (PreH24 : (interrupt_saved_value mask retval )) (PreH25 : (critical_region_interval critical sg invocation before acquired )) (PreH26 : (p_task_data_pre <> 0)) (PreH27 : (prio_pre <= 63)) (PreH28 : (0 <= request)) (PreH29 : (request <= 255)) (PreH30 : (0 <= UINT_MAX)) (PreH31 : (0 >= 0)) (PreH32 : (prio_pre = request)) (PreH33 : (p_task_data_pre = output)) (PreH34 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH35 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 0 X )
.

Definition OSTaskQuery_return_wit_3 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (task_query_reserved_entry acquired key )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH5 : (0 <= key)) (PreH6 : (key <= 63)) (PreH7 : (task_query_priority_resolution sg acquired caller request key )) (PreH8 : (key = resolved)) (PreH9 : (request = 255)) (PreH10 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH11 : (request = 255)) (PreH12 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH13 : (request = 255)) (PreH14 : (retval <= UINT_MAX)) (PreH15 : (retval >= 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (interrupt_saved_value mask retval )) (PreH18 : (critical_region_interval critical sg invocation before acquired )) (PreH19 : (p_task_data_pre <> 0)) (PreH20 : (prio_pre = 255)) (PreH21 : (prio_pre > 63)) (PreH22 : (0 <= request)) (PreH23 : (request <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (prio_pre = request)) (PreH27 : (p_task_data_pre = output)) (PreH28 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH29 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 67 X )
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (task_query_reserved_entry acquired key )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH5 : (0 <= key)) (PreH6 : (key <= 63)) (PreH7 : (task_query_priority_resolution sg acquired caller request key )) (PreH8 : (key = resolved)) (PreH9 : (request = 255)) (PreH10 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH11 : (request = 255)) (PreH12 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH13 : (request = 255)) (PreH14 : (retval <= UINT_MAX)) (PreH15 : (retval >= 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (interrupt_saved_value mask retval )) (PreH18 : (critical_region_interval critical sg invocation before acquired )) (PreH19 : (p_task_data_pre <> 0)) (PreH20 : (prio_pre = 255)) (PreH21 : (prio_pre > 63)) (PreH22 : (0 <= request)) (PreH23 : (request <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (prio_pre = request)) (PreH27 : (p_task_data_pre = output)) (PreH28 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH29 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 67 X )
).

Definition OSTaskQuery_return_wit_3_split_goal_spatial := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (task_query_reserved_entry acquired key )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH5 : (0 <= key)) (PreH6 : (key <= 63)) (PreH7 : (task_query_priority_resolution sg acquired caller request key )) (PreH8 : (key = resolved)) (PreH9 : (request = 255)) (PreH10 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH11 : (request = 255)) (PreH12 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH13 : (request = 255)) (PreH14 : (retval <= UINT_MAX)) (PreH15 : (retval >= 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (interrupt_saved_value mask retval )) (PreH18 : (critical_region_interval critical sg invocation before acquired )) (PreH19 : (p_task_data_pre <> 0)) (PreH20 : (prio_pre = 255)) (PreH21 : (prio_pre > 63)) (PreH22 : (0 <= request)) (PreH23 : (request <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (prio_pre = request)) (PreH27 : (p_task_data_pre = output)) (PreH28 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH29 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 67 X )
.

Definition OSTaskQuery_return_wit_4 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (task_query_reserved_entry acquired key )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (retval >= 0)) (PreH5 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH6 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH7 : (0 <= key)) (PreH8 : (key <= 63)) (PreH9 : (task_query_priority_resolution sg acquired caller request key )) (PreH10 : (key = prio_pre)) (PreH11 : (prio_pre <> 255)) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (critical_region_interval critical sg invocation before acquired )) (PreH14 : (p_task_data_pre <> 0)) (PreH15 : (prio_pre <= 63)) (PreH16 : (0 <= request)) (PreH17 : (request <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (prio_pre = request)) (PreH21 : (p_task_data_pre = output)) (PreH22 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH23 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 67 X )
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (task_query_reserved_entry acquired key )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (retval >= 0)) (PreH5 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH6 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH7 : (0 <= key)) (PreH8 : (key <= 63)) (PreH9 : (task_query_priority_resolution sg acquired caller request key )) (PreH10 : (key = prio_pre)) (PreH11 : (prio_pre <> 255)) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (critical_region_interval critical sg invocation before acquired )) (PreH14 : (p_task_data_pre <> 0)) (PreH15 : (prio_pre <= 63)) (PreH16 : (0 <= request)) (PreH17 : (request <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (prio_pre = request)) (PreH21 : (p_task_data_pre = output)) (PreH22 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH23 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 67 X )
).

Definition OSTaskQuery_return_wit_4_split_goal_spatial := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (task_query_reserved_entry acquired key )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (retval >= 0)) (PreH5 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH6 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH7 : (0 <= key)) (PreH8 : (key <= 63)) (PreH9 : (task_query_priority_resolution sg acquired caller request key )) (PreH10 : (key = prio_pre)) (PreH11 : (prio_pre <> 255)) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (critical_region_interval critical sg invocation before acquired )) (PreH14 : (p_task_data_pre <> 0)) (PreH15 : (prio_pre <= 63)) (PreH16 : (0 <= request)) (PreH17 : (request <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (prio_pre = request)) (PreH21 : (p_task_data_pre = output)) (PreH22 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH23 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 67 X )
.

Definition OSTaskQuery_return_wit_5 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : ((task_query_table_value (sg) (acquired) (key)) = 0)) (PreH3 : (0 <= key)) (PreH4 : (key <= 63)) (PreH5 : (task_query_priority_resolution sg acquired caller request key )) (PreH6 : (key = resolved)) (PreH7 : (request = 255)) (PreH8 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH9 : (request = 255)) (PreH10 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH11 : (request = 255)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : (retval >= 0)) (PreH14 : (prio_pre = 255)) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (p_task_data_pre <> 0)) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre > 63)) (PreH20 : (0 <= request)) (PreH21 : (request <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (prio_pre = request)) (PreH25 : (p_task_data_pre = output)) (PreH26 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH27 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 41 X )
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : ((task_query_table_value (sg) (acquired) (key)) = 0)) (PreH3 : (0 <= key)) (PreH4 : (key <= 63)) (PreH5 : (task_query_priority_resolution sg acquired caller request key )) (PreH6 : (key = resolved)) (PreH7 : (request = 255)) (PreH8 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH9 : (request = 255)) (PreH10 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH11 : (request = 255)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : (retval >= 0)) (PreH14 : (prio_pre = 255)) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (p_task_data_pre <> 0)) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre > 63)) (PreH20 : (0 <= request)) (PreH21 : (request <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (prio_pre = request)) (PreH25 : (p_task_data_pre = output)) (PreH26 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH27 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 41 X )
).

Definition OSTaskQuery_return_wit_5_split_goal_spatial := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : ((task_query_table_value (sg) (acquired) (key)) = 0)) (PreH3 : (0 <= key)) (PreH4 : (key <= 63)) (PreH5 : (task_query_priority_resolution sg acquired caller request key )) (PreH6 : (key = resolved)) (PreH7 : (request = 255)) (PreH8 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH9 : (request = 255)) (PreH10 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH11 : (request = 255)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : (retval >= 0)) (PreH14 : (prio_pre = 255)) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (p_task_data_pre <> 0)) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre > 63)) (PreH20 : (0 <= request)) (PreH21 : (request <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (prio_pre = request)) (PreH25 : (p_task_data_pre = output)) (PreH26 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH27 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 41 X )
.

Definition OSTaskQuery_return_wit_6 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = 0)) (PreH5 : (0 <= key)) (PreH6 : (key <= 63)) (PreH7 : (task_query_priority_resolution sg acquired caller request key )) (PreH8 : (key = prio_pre)) (PreH9 : (prio_pre <> 255)) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (p_task_data_pre <> 0)) (PreH13 : (prio_pre <= 63)) (PreH14 : (0 <= request)) (PreH15 : (request <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (prio_pre = request)) (PreH19 : (p_task_data_pre = output)) (PreH20 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH21 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 41 X )
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = 0)) (PreH5 : (0 <= key)) (PreH6 : (key <= 63)) (PreH7 : (task_query_priority_resolution sg acquired caller request key )) (PreH8 : (key = prio_pre)) (PreH9 : (prio_pre <> 255)) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (p_task_data_pre <> 0)) (PreH13 : (prio_pre <= 63)) (PreH14 : (0 <= request)) (PreH15 : (request <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (prio_pre = request)) (PreH19 : (p_task_data_pre = output)) (PreH20 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH21 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 41 X )
).

Definition OSTaskQuery_return_wit_6_split_goal_spatial := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = 0)) (PreH5 : (0 <= key)) (PreH6 : (key <= 63)) (PreH7 : (task_query_priority_resolution sg acquired caller request key )) (PreH8 : (key = prio_pre)) (PreH9 : (prio_pre <> 255)) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (p_task_data_pre <> 0)) (PreH13 : (prio_pre <= 63)) (PreH14 : (0 <= request)) (PreH15 : (request <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (prio_pre = request)) (PreH19 : (p_task_data_pre = output)) (PreH20 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH21 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_post platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 41 X )
.

Definition OSTaskQuery_return_wit_7 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre = 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (0 <= request)) (PreH5 : (request <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (prio_pre = request)) (PreH9 : (p_task_data_pre = output)) (PreH10 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH11 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 9 X )
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre = 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (0 <= request)) (PreH5 : (request <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (prio_pre = request)) (PreH9 : (p_task_data_pre = output)) (PreH10 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH11 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 9 X )
).

Definition OSTaskQuery_return_wit_7_split_goal_spatial := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre = 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (0 <= request)) (PreH5 : (request <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (prio_pre = request)) (PreH9 : (p_task_data_pre = output)) (PreH10 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH11 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 9 X )
.

Definition OSTaskQuery_return_wit_8 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre = 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (prio_pre = request)) (PreH8 : (p_task_data_pre = output)) (PreH9 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH10 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 9 X )
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre = 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (prio_pre = request)) (PreH8 : (p_task_data_pre = output)) (PreH9 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH10 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 9 X )
).

Definition OSTaskQuery_return_wit_8_split_goal_spatial := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre = 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (prio_pre = request)) (PreH8 : (p_task_data_pre = output)) (PreH9 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH10 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 9 X )
.

Definition OSTaskQuery_return_wit_9 := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre > 63)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (prio_pre = request)) (PreH8 : (p_task_data_pre = output)) (PreH9 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH10 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 42 X )
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre > 63)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (prio_pre = request)) (PreH8 : (p_task_data_pre = output)) (PreH9 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH10 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 42 X )
).

Definition OSTaskQuery_return_wit_9_split_goal_spatial := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre > 63)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (prio_pre = request)) (PreH8 : (p_task_data_pre = output)) (PreH9 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH10 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  (task_query_post platform critical sg invocation origin mask before caller request output old_output 42 X )
.

Definition OSTaskQuery_partial_solve_wit_1_pure := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre <> 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (prio_pre = request)) (PreH8 : (p_task_data_pre = output)) (PreH9 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH10 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
  **  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  “ (task_query_valid_arguments request output ) ” 
  &&  “ (task_query_valid_arguments prio_pre p_task_data_pre ) ”
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre <> 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (prio_pre = request)) (PreH8 : (p_task_data_pre = output)) (PreH9 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH10 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
  **  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  “ (task_query_valid_arguments prio_pre p_task_data_pre ) ” 
  &&  “ (task_query_valid_arguments prio_pre p_task_data_pre ) ”
).

Definition OSTaskQuery_partial_solve_wit_1_pure_split_goal_1 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre <> 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (prio_pre = request)) (PreH8 : (p_task_data_pre = output)) (PreH9 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH10 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
  **  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  “ (task_query_valid_arguments prio_pre p_task_data_pre ) ”
.

Definition OSTaskQuery_partial_solve_wit_1_pure_split_goal_2 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre <> 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (prio_pre = request)) (PreH8 : (p_task_data_pre = output)) (PreH9 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH10 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
  **  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  “ (task_query_valid_arguments prio_pre p_task_data_pre ) ”
.

Definition OSTaskQuery_partial_solve_wit_1_aux := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre <> 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (prio_pre = request)) (PreH8 : (p_task_data_pre = output)) (PreH9 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH10 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  “ (task_query_valid_arguments request output ) ” 
  &&  “ (task_query_valid_arguments prio_pre p_task_data_pre ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_1 := OSTaskQuery_partial_solve_wit_1_pure -> OSTaskQuery_partial_solve_wit_1_aux.

Definition OSTaskQuery_partial_solve_wit_2_pure := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre <> 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (0 <= request)) (PreH5 : (request <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (prio_pre = request)) (PreH9 : (p_task_data_pre = output)) (PreH10 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH11 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
  **  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  “ (task_query_valid_arguments request output ) ” 
  &&  “ (task_query_valid_arguments prio_pre p_task_data_pre ) ”
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre <> 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (0 <= request)) (PreH5 : (request <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (prio_pre = request)) (PreH9 : (p_task_data_pre = output)) (PreH10 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH11 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
  **  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  “ (task_query_valid_arguments 255 p_task_data_pre ) ” 
  &&  “ (task_query_valid_arguments prio_pre p_task_data_pre ) ”
).

Definition OSTaskQuery_partial_solve_wit_2_pure_split_goal_1 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre <> 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (0 <= request)) (PreH5 : (request <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (prio_pre = request)) (PreH9 : (p_task_data_pre = output)) (PreH10 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH11 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
  **  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  “ (task_query_valid_arguments 255 p_task_data_pre ) ”
.

Definition OSTaskQuery_partial_solve_wit_2_pure_split_goal_2 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre <> 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (0 <= request)) (PreH5 : (request <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (prio_pre = request)) (PreH9 : (p_task_data_pre = output)) (PreH10 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH11 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
  **  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  “ (task_query_valid_arguments prio_pre p_task_data_pre ) ”
.

Definition OSTaskQuery_partial_solve_wit_2_aux := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre <> 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (0 <= request)) (PreH5 : (request <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (prio_pre = request)) (PreH9 : (p_task_data_pre = output)) (PreH10 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH11 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  “ (task_query_valid_arguments request output ) ” 
  &&  “ (task_query_valid_arguments prio_pre p_task_data_pre ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_2 := OSTaskQuery_partial_solve_wit_2_pure -> OSTaskQuery_partial_solve_wit_2_aux.

Definition OSTaskQuery_partial_solve_wit_3 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre <> 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (0 <= request)) (PreH5 : (request <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (prio_pre = request)) (PreH9 : (p_task_data_pre = output)) (PreH10 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH11 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_closed platform critical sg invocation origin mask before )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_closed platform critical sg invocation origin mask before )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_4 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_task_data_pre <> 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (prio_pre = request)) (PreH8 : (p_task_data_pre = output)) (PreH9 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH10 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_closed platform critical sg invocation origin mask before )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_closed platform critical sg invocation origin mask before )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_5 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (p_task_data_pre <> 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (0 <= request)) (PreH4 : (request <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (prio_pre = request)) (PreH8 : (p_task_data_pre = output)) (PreH9 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH10 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_save_post platform critical sg invocation origin mask before retval )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_save_post platform critical sg invocation origin mask before retval )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_6 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (p_task_data_pre <> 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (0 <= request)) (PreH5 : (request <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (prio_pre = request)) (PreH9 : (p_task_data_pre = output)) (PreH10 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH11 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_save_post platform critical sg invocation origin mask before retval )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_save_post platform critical sg invocation origin mask before retval )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_7_pure := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (PreH1 : (request = 255)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (prio_pre = 255)) (PreH5 : (interrupt_saved_value mask retval )) (PreH6 : (critical_region_interval critical sg invocation before acquired )) (PreH7 : (p_task_data_pre <> 0)) (PreH8 : (prio_pre = 255)) (PreH9 : (prio_pre > 63)) (PreH10 : (0 <= request)) (PreH11 : (request <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (prio_pre = request)) (PreH15 : (p_task_data_pre = output)) (PreH16 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH17 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (request = 255) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
.

Definition OSTaskQuery_partial_solve_wit_7_aux := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (PreH1 : (request = 255)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (prio_pre = 255)) (PreH5 : (interrupt_saved_value mask retval )) (PreH6 : (critical_region_interval critical sg invocation before acquired )) (PreH7 : (p_task_data_pre <> 0)) (PreH8 : (prio_pre = 255)) (PreH9 : (prio_pre > 63)) (PreH10 : (0 <= request)) (PreH11 : (request <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (prio_pre = request)) (PreH15 : (p_task_data_pre = output)) (PreH16 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH17 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (request = 255) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (request = 255) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_7 := OSTaskQuery_partial_solve_wit_7_pure -> OSTaskQuery_partial_solve_wit_7_aux.

Definition OSTaskQuery_partial_solve_wit_8_pure := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (PreH1 : (request = 255)) (PreH2 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH3 : (request = 255)) (PreH4 : (retval <= UINT_MAX)) (PreH5 : (retval >= 0)) (PreH6 : (prio_pre = 255)) (PreH7 : (interrupt_saved_value mask retval )) (PreH8 : (critical_region_interval critical sg invocation before acquired )) (PreH9 : (p_task_data_pre <> 0)) (PreH10 : (prio_pre = 255)) (PreH11 : (prio_pre > 63)) (PreH12 : (0 <= request)) (PreH13 : (request <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (prio_pre = request)) (PreH17 : (p_task_data_pre = output)) (PreH18 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH19 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((&((current)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> resolved)
  **  (residual )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_current_tail platform critical sg invocation origin retval before acquired caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> resolved)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
.

Definition OSTaskQuery_partial_solve_wit_8_aux := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (PreH1 : (request = 255)) (PreH2 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH3 : (request = 255)) (PreH4 : (retval <= UINT_MAX)) (PreH5 : (retval >= 0)) (PreH6 : (prio_pre = 255)) (PreH7 : (interrupt_saved_value mask retval )) (PreH8 : (critical_region_interval critical sg invocation before acquired )) (PreH9 : (p_task_data_pre <> 0)) (PreH10 : (prio_pre = 255)) (PreH11 : (prio_pre > 63)) (PreH12 : (0 <= request)) (PreH13 : (request <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (prio_pre = request)) (PreH17 : (p_task_data_pre = output)) (PreH18 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH19 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((&((current)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> resolved)
  **  (residual )
  **  (task_query_current_tail platform critical sg invocation origin retval before acquired caller request output old_output )
|--
  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ” 
  &&  “ (request = 255) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((&((current)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> resolved)
  **  (residual )
  **  (task_query_current_tail platform critical sg invocation origin retval before acquired caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_8 := OSTaskQuery_partial_solve_wit_8_pure -> OSTaskQuery_partial_solve_wit_8_aux.

Definition OSTaskQuery_partial_solve_wit_9 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (critical_region_interval critical sg invocation before acquired )) (PreH4 : (p_task_data_pre <> 0)) (PreH5 : (prio_pre <= 63)) (PreH6 : (0 <= request)) (PreH7 : (request <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (prio_pre = request)) (PreH11 : (p_task_data_pre = output)) (PreH12 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH13 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (prio_pre <> 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_10 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (PreH1 : (request = 255)) (PreH2 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH3 : (request = 255)) (PreH4 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH5 : (request = 255)) (PreH6 : (retval <= UINT_MAX)) (PreH7 : (retval >= 0)) (PreH8 : (prio_pre = 255)) (PreH9 : (interrupt_saved_value mask retval )) (PreH10 : (critical_region_interval critical sg invocation before acquired )) (PreH11 : (p_task_data_pre <> 0)) (PreH12 : (prio_pre = 255)) (PreH13 : (prio_pre > 63)) (PreH14 : (0 <= request)) (PreH15 : (request <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (prio_pre = request)) (PreH19 : (p_task_data_pre = output)) (PreH20 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH21 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (request = 255) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request resolved ) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ” 
  &&  “ (request = 255) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_11_pure := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (key = prio_pre)) (PreH2 : (prio_pre <> 255)) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (critical_region_interval critical sg invocation before acquired )) (PreH5 : (p_task_data_pre <> 0)) (PreH6 : (prio_pre <= 63)) (PreH7 : (0 <= request)) (PreH8 : (request <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (prio_pre = request)) (PreH12 : (p_task_data_pre = output)) (PreH13 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH14 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_query_priority_resolution sg acquired caller prio_pre prio_pre ) ”
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (key = prio_pre)) (PreH4 : (prio_pre <> 255)) (PreH5 : (interrupt_saved_value mask retval )) (PreH6 : (critical_region_interval critical sg invocation before acquired )) (PreH7 : (p_task_data_pre <> 0)) (PreH8 : (prio_pre <= 63)) (PreH9 : (0 <= request)) (PreH10 : (request <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (prio_pre = request)) (PreH14 : (p_task_data_pre = output)) (PreH15 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH16 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (task_query_priority_resolution sg acquired caller prio_pre prio_pre ) ” 
  &&  “ (task_query_priority_resolution sg acquired caller prio_pre prio_pre ) ”
).

Definition OSTaskQuery_partial_solve_wit_11_pure_split_goal_1 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (key = prio_pre)) (PreH4 : (prio_pre <> 255)) (PreH5 : (interrupt_saved_value mask retval )) (PreH6 : (critical_region_interval critical sg invocation before acquired )) (PreH7 : (p_task_data_pre <> 0)) (PreH8 : (prio_pre <= 63)) (PreH9 : (0 <= request)) (PreH10 : (request <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (prio_pre = request)) (PreH14 : (p_task_data_pre = output)) (PreH15 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH16 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (task_query_priority_resolution sg acquired caller prio_pre prio_pre ) ”
.

Definition OSTaskQuery_partial_solve_wit_11_pure_split_goal_2 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (key = prio_pre)) (PreH4 : (prio_pre <> 255)) (PreH5 : (interrupt_saved_value mask retval )) (PreH6 : (critical_region_interval critical sg invocation before acquired )) (PreH7 : (p_task_data_pre <> 0)) (PreH8 : (prio_pre <= 63)) (PreH9 : (0 <= request)) (PreH10 : (request <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (prio_pre = request)) (PreH14 : (p_task_data_pre = output)) (PreH15 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH16 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (task_query_priority_resolution sg acquired caller prio_pre prio_pre ) ”
.

Definition OSTaskQuery_partial_solve_wit_11_aux := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (key = prio_pre)) (PreH2 : (prio_pre <> 255)) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (critical_region_interval critical sg invocation before acquired )) (PreH5 : (p_task_data_pre <> 0)) (PreH6 : (prio_pre <= 63)) (PreH7 : (0 <= request)) (PreH8 : (request <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (prio_pre = request)) (PreH12 : (p_task_data_pre = output)) (PreH13 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH14 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_query_priority_resolution sg acquired caller prio_pre prio_pre ) ” 
  &&  “ (key = prio_pre) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_11 := OSTaskQuery_partial_solve_wit_11_pure -> OSTaskQuery_partial_solve_wit_11_aux.

Definition OSTaskQuery_partial_solve_wit_12_pure := 
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (key = resolved)) (PreH2 : (request = 255)) (PreH3 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH4 : (request = 255)) (PreH5 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH6 : (request = 255)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (retval >= 0)) (PreH9 : (prio_pre = 255)) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (p_task_data_pre <> 0)) (PreH13 : (prio_pre = 255)) (PreH14 : (prio_pre > 63)) (PreH15 : (0 <= request)) (PreH16 : (request <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (prio_pre = request)) (PreH20 : (p_task_data_pre = output)) (PreH21 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH22 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (resolved <= 63) ” 
  &&  “ (0 <= resolved) ”
) \/
(
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (key = resolved)) (PreH2 : (request = 255)) (PreH3 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH4 : (request = 255)) (PreH5 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH6 : (request = 255)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (retval >= 0)) (PreH9 : (prio_pre = 255)) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (p_task_data_pre <> 0)) (PreH13 : (prio_pre = 255)) (PreH14 : (prio_pre > 63)) (PreH15 : (0 <= request)) (PreH16 : (request <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (prio_pre = request)) (PreH20 : (p_task_data_pre = output)) (PreH21 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH22 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (0 <= resolved) ” 
  &&  “ (resolved <= 63) ” 
  &&  “ (resolved <= 63) ” 
  &&  “ (0 <= resolved) ”
).

Definition OSTaskQuery_partial_solve_wit_12_pure_split_goal_1 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (key = resolved)) (PreH2 : (request = 255)) (PreH3 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH4 : (request = 255)) (PreH5 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH6 : (request = 255)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (retval >= 0)) (PreH9 : (prio_pre = 255)) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (p_task_data_pre <> 0)) (PreH13 : (prio_pre = 255)) (PreH14 : (prio_pre > 63)) (PreH15 : (0 <= request)) (PreH16 : (request <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (prio_pre = request)) (PreH20 : (p_task_data_pre = output)) (PreH21 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH22 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (0 <= resolved) ”
.

Definition OSTaskQuery_partial_solve_wit_12_pure_split_goal_2 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (key = resolved)) (PreH2 : (request = 255)) (PreH3 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH4 : (request = 255)) (PreH5 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH6 : (request = 255)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (retval >= 0)) (PreH9 : (prio_pre = 255)) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (p_task_data_pre <> 0)) (PreH13 : (prio_pre = 255)) (PreH14 : (prio_pre > 63)) (PreH15 : (0 <= request)) (PreH16 : (request <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (prio_pre = request)) (PreH20 : (p_task_data_pre = output)) (PreH21 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH22 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (resolved <= 63) ”
.

Definition OSTaskQuery_partial_solve_wit_12_pure_split_goal_3 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (key = resolved)) (PreH2 : (request = 255)) (PreH3 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH4 : (request = 255)) (PreH5 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH6 : (request = 255)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (retval >= 0)) (PreH9 : (prio_pre = 255)) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (p_task_data_pre <> 0)) (PreH13 : (prio_pre = 255)) (PreH14 : (prio_pre > 63)) (PreH15 : (0 <= request)) (PreH16 : (request <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (prio_pre = request)) (PreH20 : (p_task_data_pre = output)) (PreH21 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH22 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (resolved <= 63) ”
.

Definition OSTaskQuery_partial_solve_wit_12_pure_split_goal_4 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (key = resolved)) (PreH2 : (request = 255)) (PreH3 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH4 : (request = 255)) (PreH5 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH6 : (request = 255)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (retval >= 0)) (PreH9 : (prio_pre = 255)) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (p_task_data_pre <> 0)) (PreH13 : (prio_pre = 255)) (PreH14 : (prio_pre > 63)) (PreH15 : (0 <= request)) (PreH16 : (request <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (prio_pre = request)) (PreH20 : (p_task_data_pre = output)) (PreH21 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH22 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (0 <= resolved) ”
.

Definition OSTaskQuery_partial_solve_wit_12_aux := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (key = resolved)) (PreH2 : (request = 255)) (PreH3 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH4 : (request = 255)) (PreH5 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH6 : (request = 255)) (PreH7 : (retval <= UINT_MAX)) (PreH8 : (retval >= 0)) (PreH9 : (prio_pre = 255)) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (p_task_data_pre <> 0)) (PreH13 : (prio_pre = 255)) (PreH14 : (prio_pre > 63)) (PreH15 : (0 <= request)) (PreH16 : (request <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (prio_pre = request)) (PreH20 : (p_task_data_pre = output)) (PreH21 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH22 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (resolved <= 63) ” 
  &&  “ (0 <= resolved) ” 
  &&  “ (key = resolved) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request resolved ) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ” 
  &&  “ (request = 255) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_12 := OSTaskQuery_partial_solve_wit_12_pure -> OSTaskQuery_partial_solve_wit_12_aux.

Definition OSTaskQuery_partial_solve_wit_13_pure := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_priority_resolution sg acquired caller request key )) (PreH4 : (key = prio_pre)) (PreH5 : (prio_pre <> 255)) (PreH6 : (interrupt_saved_value mask retval )) (PreH7 : (critical_region_interval critical sg invocation before acquired )) (PreH8 : (p_task_data_pre <> 0)) (PreH9 : (prio_pre <= 63)) (PreH10 : (0 <= request)) (PreH11 : (request <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (prio_pre = request)) (PreH15 : (p_task_data_pre = output)) (PreH16 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH17 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (key * sizeof(PTR)))) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_table_tail platform critical sg invocation origin retval acquired key )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
.

Definition OSTaskQuery_partial_solve_wit_13_aux := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_priority_resolution sg acquired caller request key )) (PreH4 : (key = prio_pre)) (PreH5 : (prio_pre <> 255)) (PreH6 : (interrupt_saved_value mask retval )) (PreH7 : (critical_region_interval critical sg invocation before acquired )) (PreH8 : (p_task_data_pre <> 0)) (PreH9 : (prio_pre <= 63)) (PreH10 : (0 <= request)) (PreH11 : (request <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (prio_pre = request)) (PreH15 : (p_task_data_pre = output)) (PreH16 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH17 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (key * sizeof(PTR)))) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  (task_query_table_tail platform critical sg invocation origin retval acquired key )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = prio_pre) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (key * sizeof(PTR)))) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  (task_query_table_tail platform critical sg invocation origin retval acquired key )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_13 := OSTaskQuery_partial_solve_wit_13_pure -> OSTaskQuery_partial_solve_wit_13_aux.

Definition OSTaskQuery_partial_solve_wit_14_pure := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_priority_resolution sg acquired caller request key )) (PreH4 : (key = resolved)) (PreH5 : (request = 255)) (PreH6 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH7 : (request = 255)) (PreH8 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH9 : (request = 255)) (PreH10 : (retval <= UINT_MAX)) (PreH11 : (retval >= 0)) (PreH12 : (prio_pre = 255)) (PreH13 : (interrupt_saved_value mask retval )) (PreH14 : (critical_region_interval critical sg invocation before acquired )) (PreH15 : (p_task_data_pre <> 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (prio_pre > 63)) (PreH18 : (0 <= request)) (PreH19 : (request <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (prio_pre = request)) (PreH23 : (p_task_data_pre = output)) (PreH24 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH25 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (key * sizeof(PTR)))) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_table_tail platform critical sg invocation origin retval acquired key )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
.

Definition OSTaskQuery_partial_solve_wit_14_aux := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_priority_resolution sg acquired caller request key )) (PreH4 : (key = resolved)) (PreH5 : (request = 255)) (PreH6 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH7 : (request = 255)) (PreH8 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH9 : (request = 255)) (PreH10 : (retval <= UINT_MAX)) (PreH11 : (retval >= 0)) (PreH12 : (prio_pre = 255)) (PreH13 : (interrupt_saved_value mask retval )) (PreH14 : (critical_region_interval critical sg invocation before acquired )) (PreH15 : (p_task_data_pre <> 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (prio_pre > 63)) (PreH18 : (0 <= request)) (PreH19 : (request <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (prio_pre = request)) (PreH23 : (p_task_data_pre = output)) (PreH24 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH25 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (key * sizeof(PTR)))) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  (task_query_table_tail platform critical sg invocation origin retval acquired key )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = resolved) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request resolved ) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ” 
  &&  “ (request = 255) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (key * sizeof(PTR)))) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  (task_query_table_tail platform critical sg invocation origin retval acquired key )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_14 := OSTaskQuery_partial_solve_wit_14_pure -> OSTaskQuery_partial_solve_wit_14_aux.

Definition OSTaskQuery_partial_solve_wit_15 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : ((task_query_table_value (sg) (acquired) (key)) = 0)) (PreH3 : (0 <= key)) (PreH4 : (key <= 63)) (PreH5 : (task_query_priority_resolution sg acquired caller request key )) (PreH6 : (key = resolved)) (PreH7 : (request = 255)) (PreH8 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH9 : (request = 255)) (PreH10 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH11 : (request = 255)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : (retval >= 0)) (PreH14 : (prio_pre = 255)) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (p_task_data_pre <> 0)) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre > 63)) (PreH20 : (0 <= request)) (PreH21 : (request <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (prio_pre = request)) (PreH25 : (p_task_data_pre = output)) (PreH26 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH27 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = resolved) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request resolved ) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ” 
  &&  “ (request = 255) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_16 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = 0)) (PreH5 : (0 <= key)) (PreH6 : (key <= 63)) (PreH7 : (task_query_priority_resolution sg acquired caller request key )) (PreH8 : (key = prio_pre)) (PreH9 : (prio_pre <> 255)) (PreH10 : (interrupt_saved_value mask retval )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (p_task_data_pre <> 0)) (PreH13 : (prio_pre <= 63)) (PreH14 : (0 <= request)) (PreH15 : (request <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (prio_pre = request)) (PreH19 : (p_task_data_pre = output)) (PreH20 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH21 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = prio_pre) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_17 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : (task_query_reserved_entry acquired key )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH5 : (0 <= key)) (PreH6 : (key <= 63)) (PreH7 : (task_query_priority_resolution sg acquired caller request key )) (PreH8 : (key = resolved)) (PreH9 : (request = 255)) (PreH10 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH11 : (request = 255)) (PreH12 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH13 : (request = 255)) (PreH14 : (retval <= UINT_MAX)) (PreH15 : (retval >= 0)) (PreH16 : (prio_pre = 255)) (PreH17 : (interrupt_saved_value mask retval )) (PreH18 : (critical_region_interval critical sg invocation before acquired )) (PreH19 : (p_task_data_pre <> 0)) (PreH20 : (prio_pre = 255)) (PreH21 : (prio_pre > 63)) (PreH22 : (0 <= request)) (PreH23 : (request <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (prio_pre = request)) (PreH27 : (p_task_data_pre = output)) (PreH28 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH29 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (task_query_reserved_entry acquired key ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = resolved) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request resolved ) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ” 
  &&  “ (request = 255) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_18 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : (task_query_reserved_entry acquired key )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (retval >= 0)) (PreH5 : ((task_query_table_value (sg) (acquired) (key)) = 1)) (PreH6 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH7 : (0 <= key)) (PreH8 : (key <= 63)) (PreH9 : (task_query_priority_resolution sg acquired caller request key )) (PreH10 : (key = prio_pre)) (PreH11 : (prio_pre <> 255)) (PreH12 : (interrupt_saved_value mask retval )) (PreH13 : (critical_region_interval critical sg invocation before acquired )) (PreH14 : (p_task_data_pre <> 0)) (PreH15 : (prio_pre <= 63)) (PreH16 : (0 <= request)) (PreH17 : (request <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (prio_pre = request)) (PreH21 : (p_task_data_pre = output)) (PreH22 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH23 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (task_query_reserved_entry acquired key ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = prio_pre) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_19_pure := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH2 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH3 : (0 <= key)) (PreH4 : (key <= 63)) (PreH5 : (task_query_priority_resolution sg acquired caller request key )) (PreH6 : (key = prio_pre)) (PreH7 : (prio_pre <> 255)) (PreH8 : (interrupt_saved_value mask retval )) (PreH9 : (critical_region_interval critical sg invocation before acquired )) (PreH10 : (p_task_data_pre <> 0)) (PreH11 : (prio_pre <= 63)) (PreH12 : (0 <= request)) (PreH13 : (request <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (prio_pre = request)) (PreH17 : (p_task_data_pre = output)) (PreH18 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH19 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 1) ”
.

Definition OSTaskQuery_partial_solve_wit_19_aux := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (PreH1 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH2 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH3 : (0 <= key)) (PreH4 : (key <= 63)) (PreH5 : (task_query_priority_resolution sg acquired caller request key )) (PreH6 : (key = prio_pre)) (PreH7 : (prio_pre <> 255)) (PreH8 : (interrupt_saved_value mask retval )) (PreH9 : (critical_region_interval critical sg invocation before acquired )) (PreH10 : (p_task_data_pre <> 0)) (PreH11 : (prio_pre <= 63)) (PreH12 : (0 <= request)) (PreH13 : (request <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (prio_pre = request)) (PreH17 : (p_task_data_pre = output)) (PreH18 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH19 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = prio_pre) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_19 := OSTaskQuery_partial_solve_wit_19_pure -> OSTaskQuery_partial_solve_wit_19_aux.

Definition OSTaskQuery_partial_solve_wit_20_pure := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH2 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH3 : (0 <= key)) (PreH4 : (key <= 63)) (PreH5 : (task_query_priority_resolution sg acquired caller request key )) (PreH6 : (key = resolved)) (PreH7 : (request = 255)) (PreH8 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH9 : (request = 255)) (PreH10 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH11 : (request = 255)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : (retval >= 0)) (PreH14 : (prio_pre = 255)) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (p_task_data_pre <> 0)) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre > 63)) (PreH20 : (0 <= request)) (PreH21 : (request <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (prio_pre = request)) (PreH25 : (p_task_data_pre = output)) (PreH26 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH27 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 1) ”
.

Definition OSTaskQuery_partial_solve_wit_20_aux := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (PreH1 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH2 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH3 : (0 <= key)) (PreH4 : (key <= 63)) (PreH5 : (task_query_priority_resolution sg acquired caller request key )) (PreH6 : (key = resolved)) (PreH7 : (request = 255)) (PreH8 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH9 : (request = 255)) (PreH10 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH11 : (request = 255)) (PreH12 : (retval <= UINT_MAX)) (PreH13 : (retval >= 0)) (PreH14 : (prio_pre = 255)) (PreH15 : (interrupt_saved_value mask retval )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (p_task_data_pre <> 0)) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre > 63)) (PreH20 : (0 <= request)) (PreH21 : (request <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (prio_pre = request)) (PreH25 : (p_task_data_pre = output)) (PreH26 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH27 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = resolved) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request resolved ) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ” 
  &&  “ (request = 255) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_partial_solve_wit_20 := OSTaskQuery_partial_solve_wit_20_pure -> OSTaskQuery_partial_solve_wit_20_aux.

Definition OSTaskQuery_partial_solve_wit_21_pure := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_task_entry acquired key tid )) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH5 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH6 : ((Zlength (bytes)) = 64)) (PreH7 : (sizeof( "os_tcb" ) = 64)) (PreH8 : (0 <= (task_slot_addr (sg) (tid)))) (PreH9 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH10 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= output)) (PreH12 : ((output + 64 ) <= UINT_MAX)) (PreH13 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH16 : (0 <= key)) (PreH17 : (key <= 63)) (PreH18 : (task_query_priority_resolution sg acquired caller request key )) (PreH19 : (key = resolved)) (PreH20 : (request = 255)) (PreH21 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH22 : (request = 255)) (PreH23 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH24 : (request = 255)) (PreH25 : (retval <= UINT_MAX)) (PreH26 : (retval >= 0)) (PreH27 : (prio_pre = 255)) (PreH28 : (interrupt_saved_value mask retval )) (PreH29 : (critical_region_interval critical sg invocation before acquired )) (PreH30 : (p_task_data_pre <> 0)) (PreH31 : (prio_pre = 255)) (PreH32 : (prio_pre > 63)) (PreH33 : (0 <= request)) (PreH34 : (request <= 255)) (PreH35 : (0 <= UINT_MAX)) (PreH36 : (0 >= 0)) (PreH37 : (prio_pre = request)) (PreH38 : (p_task_data_pre = output)) (PreH39 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH40 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mem_copy_pre output (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_copy_frame platform critical sg invocation origin retval acquired caller tid )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (0 <= sizeof( "os_tcb" )) ” 
  &&  “ (sizeof( "os_tcb" ) <= 65535) ” 
  &&  “ ((Zlength (bytes)) = sizeof( "os_tcb" )) ” 
  &&  “ (0 <= p_task_data_pre) ” 
  &&  “ ((p_task_data_pre + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (task_slot_addr (sg) (tid))) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ”
.

Definition OSTaskQuery_partial_solve_wit_21_aux := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_task_entry acquired key tid )) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH5 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH6 : ((Zlength (bytes)) = 64)) (PreH7 : (sizeof( "os_tcb" ) = 64)) (PreH8 : (0 <= (task_slot_addr (sg) (tid)))) (PreH9 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH10 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= output)) (PreH12 : ((output + 64 ) <= UINT_MAX)) (PreH13 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH16 : (0 <= key)) (PreH17 : (key <= 63)) (PreH18 : (task_query_priority_resolution sg acquired caller request key )) (PreH19 : (key = resolved)) (PreH20 : (request = 255)) (PreH21 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH22 : (request = 255)) (PreH23 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH24 : (request = 255)) (PreH25 : (retval <= UINT_MAX)) (PreH26 : (retval >= 0)) (PreH27 : (prio_pre = 255)) (PreH28 : (interrupt_saved_value mask retval )) (PreH29 : (critical_region_interval critical sg invocation before acquired )) (PreH30 : (p_task_data_pre <> 0)) (PreH31 : (prio_pre = 255)) (PreH32 : (prio_pre > 63)) (PreH33 : (0 <= request)) (PreH34 : (request <= 255)) (PreH35 : (0 <= UINT_MAX)) (PreH36 : (0 >= 0)) (PreH37 : (prio_pre = request)) (PreH38 : (p_task_data_pre = output)) (PreH39 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH40 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (mem_copy_pre output (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  (task_query_copy_frame platform critical sg invocation origin retval acquired caller tid )
|--
  “ (0 <= sizeof( "os_tcb" )) ” 
  &&  “ (sizeof( "os_tcb" ) <= 65535) ” 
  &&  “ ((Zlength (bytes)) = sizeof( "os_tcb" )) ” 
  &&  “ (0 <= p_task_data_pre) ” 
  &&  “ ((p_task_data_pre + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (task_slot_addr (sg) (tid))) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_task_entry acquired key tid ) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_query_source_byte_view sg acquired tid t bytes ) ” 
  &&  “ ((Zlength (bytes)) = 64) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ” 
  &&  “ (0 <= (task_slot_addr (sg) (tid))) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= output) ” 
  &&  “ ((output + 64 ) <= UINT_MAX) ” 
  &&  “ ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = resolved) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request resolved ) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ” 
  &&  “ (request = 255) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (mem_copy_pre p_task_data_pre (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  (task_query_copy_frame platform critical sg invocation origin retval acquired caller tid )
.

Definition OSTaskQuery_partial_solve_wit_21 := OSTaskQuery_partial_solve_wit_21_pure -> OSTaskQuery_partial_solve_wit_21_aux.

Definition OSTaskQuery_partial_solve_wit_22_pure := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_task_entry acquired key tid )) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH5 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH6 : ((Zlength (bytes)) = 64)) (PreH7 : (sizeof( "os_tcb" ) = 64)) (PreH8 : (0 <= (task_slot_addr (sg) (tid)))) (PreH9 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH10 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= output)) (PreH12 : ((output + 64 ) <= UINT_MAX)) (PreH13 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH16 : (0 <= key)) (PreH17 : (key <= 63)) (PreH18 : (task_query_priority_resolution sg acquired caller request key )) (PreH19 : (key = prio_pre)) (PreH20 : (prio_pre <> 255)) (PreH21 : (interrupt_saved_value mask retval )) (PreH22 : (critical_region_interval critical sg invocation before acquired )) (PreH23 : (p_task_data_pre <> 0)) (PreH24 : (prio_pre <= 63)) (PreH25 : (0 <= request)) (PreH26 : (request <= 255)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (0 >= 0)) (PreH29 : (prio_pre = request)) (PreH30 : (p_task_data_pre = output)) (PreH31 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH32 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mem_copy_pre output (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_copy_frame platform critical sg invocation origin retval acquired caller tid )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (0 <= sizeof( "os_tcb" )) ” 
  &&  “ (sizeof( "os_tcb" ) <= 65535) ” 
  &&  “ ((Zlength (bytes)) = sizeof( "os_tcb" )) ” 
  &&  “ (0 <= p_task_data_pre) ” 
  &&  “ ((p_task_data_pre + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (task_slot_addr (sg) (tid))) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ”
.

Definition OSTaskQuery_partial_solve_wit_22_aux := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_task_entry acquired key tid )) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH5 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH6 : ((Zlength (bytes)) = 64)) (PreH7 : (sizeof( "os_tcb" ) = 64)) (PreH8 : (0 <= (task_slot_addr (sg) (tid)))) (PreH9 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH10 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= output)) (PreH12 : ((output + 64 ) <= UINT_MAX)) (PreH13 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH16 : (0 <= key)) (PreH17 : (key <= 63)) (PreH18 : (task_query_priority_resolution sg acquired caller request key )) (PreH19 : (key = prio_pre)) (PreH20 : (prio_pre <> 255)) (PreH21 : (interrupt_saved_value mask retval )) (PreH22 : (critical_region_interval critical sg invocation before acquired )) (PreH23 : (p_task_data_pre <> 0)) (PreH24 : (prio_pre <= 63)) (PreH25 : (0 <= request)) (PreH26 : (request <= 255)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (0 >= 0)) (PreH29 : (prio_pre = request)) (PreH30 : (p_task_data_pre = output)) (PreH31 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH32 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (mem_copy_pre output (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  (task_query_copy_frame platform critical sg invocation origin retval acquired caller tid )
|--
  “ (0 <= sizeof( "os_tcb" )) ” 
  &&  “ (sizeof( "os_tcb" ) <= 65535) ” 
  &&  “ ((Zlength (bytes)) = sizeof( "os_tcb" )) ” 
  &&  “ (0 <= p_task_data_pre) ” 
  &&  “ ((p_task_data_pre + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (task_slot_addr (sg) (tid))) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_task_entry acquired key tid ) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_query_source_byte_view sg acquired tid t bytes ) ” 
  &&  “ ((Zlength (bytes)) = 64) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ” 
  &&  “ (0 <= (task_slot_addr (sg) (tid))) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= output) ” 
  &&  “ ((output + 64 ) <= UINT_MAX) ” 
  &&  “ ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = prio_pre) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (mem_copy_pre p_task_data_pre (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  (task_query_copy_frame platform critical sg invocation origin retval acquired caller tid )
.

Definition OSTaskQuery_partial_solve_wit_22 := OSTaskQuery_partial_solve_wit_22_pure -> OSTaskQuery_partial_solve_wit_22_aux.

Definition OSTaskQuery_partial_solve_wit_23_pure := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_task_entry acquired key tid )) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH5 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH6 : ((Zlength (bytes)) = 64)) (PreH7 : (sizeof( "os_tcb" ) = 64)) (PreH8 : (0 <= (task_slot_addr (sg) (tid)))) (PreH9 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH10 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= output)) (PreH12 : ((output + 64 ) <= UINT_MAX)) (PreH13 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH16 : (0 <= key)) (PreH17 : (key <= 63)) (PreH18 : (task_query_priority_resolution sg acquired caller request key )) (PreH19 : (key = prio_pre)) (PreH20 : (prio_pre <> 255)) (PreH21 : (interrupt_saved_value mask retval )) (PreH22 : (critical_region_interval critical sg invocation before acquired )) (PreH23 : (p_task_data_pre <> 0)) (PreH24 : (prio_pre <= 63)) (PreH25 : (0 <= request)) (PreH26 : (request <= 255)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (0 >= 0)) (PreH29 : (prio_pre = request)) (PreH30 : (p_task_data_pre = output)) (PreH31 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH32 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (mem_copy_post p_task_data_pre (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_copy_frame platform critical sg invocation origin retval acquired caller tid )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (task_query_task_entry acquired key tid ) ” 
  &&  “ (task_query_source_byte_view sg acquired tid t bytes ) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ”
.

Definition OSTaskQuery_partial_solve_wit_23_aux := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_task_entry acquired key tid )) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH5 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH6 : ((Zlength (bytes)) = 64)) (PreH7 : (sizeof( "os_tcb" ) = 64)) (PreH8 : (0 <= (task_slot_addr (sg) (tid)))) (PreH9 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH10 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= output)) (PreH12 : ((output + 64 ) <= UINT_MAX)) (PreH13 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH16 : (0 <= key)) (PreH17 : (key <= 63)) (PreH18 : (task_query_priority_resolution sg acquired caller request key )) (PreH19 : (key = prio_pre)) (PreH20 : (prio_pre <> 255)) (PreH21 : (interrupt_saved_value mask retval )) (PreH22 : (critical_region_interval critical sg invocation before acquired )) (PreH23 : (p_task_data_pre <> 0)) (PreH24 : (prio_pre <= 63)) (PreH25 : (0 <= request)) (PreH26 : (request <= 255)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (0 >= 0)) (PreH29 : (prio_pre = request)) (PreH30 : (p_task_data_pre = output)) (PreH31 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH32 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (mem_copy_post p_task_data_pre (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  (task_query_copy_frame platform critical sg invocation origin retval acquired caller tid )
|--
  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (task_query_task_entry acquired key tid ) ” 
  &&  “ (task_query_source_byte_view sg acquired tid t bytes ) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_task_entry acquired key tid ) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_query_source_byte_view sg acquired tid t bytes ) ” 
  &&  “ ((Zlength (bytes)) = 64) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ” 
  &&  “ (0 <= (task_slot_addr (sg) (tid))) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= output) ” 
  &&  “ ((output + 64 ) <= UINT_MAX) ” 
  &&  “ ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = prio_pre) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (mem_copy_post p_task_data_pre (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  (task_query_copy_frame platform critical sg invocation origin retval acquired caller tid )
.

Definition OSTaskQuery_partial_solve_wit_23 := OSTaskQuery_partial_solve_wit_23_pure -> OSTaskQuery_partial_solve_wit_23_aux.

Definition OSTaskQuery_partial_solve_wit_24_pure := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_task_entry acquired key tid )) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH5 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH6 : ((Zlength (bytes)) = 64)) (PreH7 : (sizeof( "os_tcb" ) = 64)) (PreH8 : (0 <= (task_slot_addr (sg) (tid)))) (PreH9 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH10 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= output)) (PreH12 : ((output + 64 ) <= UINT_MAX)) (PreH13 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH16 : (0 <= key)) (PreH17 : (key <= 63)) (PreH18 : (task_query_priority_resolution sg acquired caller request key )) (PreH19 : (key = resolved)) (PreH20 : (request = 255)) (PreH21 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH22 : (request = 255)) (PreH23 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH24 : (request = 255)) (PreH25 : (retval <= UINT_MAX)) (PreH26 : (retval >= 0)) (PreH27 : (prio_pre = 255)) (PreH28 : (interrupt_saved_value mask retval )) (PreH29 : (critical_region_interval critical sg invocation before acquired )) (PreH30 : (p_task_data_pre <> 0)) (PreH31 : (prio_pre = 255)) (PreH32 : (prio_pre > 63)) (PreH33 : (0 <= request)) (PreH34 : (request <= 255)) (PreH35 : (0 <= UINT_MAX)) (PreH36 : (0 >= 0)) (PreH37 : (prio_pre = request)) (PreH38 : (p_task_data_pre = output)) (PreH39 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH40 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (mem_copy_post p_task_data_pre (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (task_query_copy_frame platform critical sg invocation origin retval acquired caller tid )
  **  ((( &( "prio" ) )) # UChar  |-> key)
  **  ((( &( "p_task_data" ) )) # Ptr  |-> p_task_data_pre)
|--
  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (task_query_task_entry acquired key tid ) ” 
  &&  “ (task_query_source_byte_view sg acquired tid t bytes ) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ”
.

Definition OSTaskQuery_partial_solve_wit_24_aux := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (0 <= key)) (PreH2 : (key <= 63)) (PreH3 : (task_query_task_entry acquired key tid )) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH5 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH6 : ((Zlength (bytes)) = 64)) (PreH7 : (sizeof( "os_tcb" ) = 64)) (PreH8 : (0 <= (task_slot_addr (sg) (tid)))) (PreH9 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH10 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= output)) (PreH12 : ((output + 64 ) <= UINT_MAX)) (PreH13 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH16 : (0 <= key)) (PreH17 : (key <= 63)) (PreH18 : (task_query_priority_resolution sg acquired caller request key )) (PreH19 : (key = resolved)) (PreH20 : (request = 255)) (PreH21 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH22 : (request = 255)) (PreH23 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH24 : (request = 255)) (PreH25 : (retval <= UINT_MAX)) (PreH26 : (retval >= 0)) (PreH27 : (prio_pre = 255)) (PreH28 : (interrupt_saved_value mask retval )) (PreH29 : (critical_region_interval critical sg invocation before acquired )) (PreH30 : (p_task_data_pre <> 0)) (PreH31 : (prio_pre = 255)) (PreH32 : (prio_pre > 63)) (PreH33 : (0 <= request)) (PreH34 : (request <= 255)) (PreH35 : (0 <= UINT_MAX)) (PreH36 : (0 >= 0)) (PreH37 : (prio_pre = request)) (PreH38 : (p_task_data_pre = output)) (PreH39 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH40 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (mem_copy_post p_task_data_pre (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  (task_query_copy_frame platform critical sg invocation origin retval acquired caller tid )
|--
  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (task_query_task_entry acquired key tid ) ” 
  &&  “ (task_query_source_byte_view sg acquired tid t bytes ) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_task_entry acquired key tid ) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_query_source_byte_view sg acquired tid t bytes ) ” 
  &&  “ ((Zlength (bytes)) = 64) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ” 
  &&  “ (0 <= (task_slot_addr (sg) (tid))) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= output) ” 
  &&  “ ((output + 64 ) <= UINT_MAX) ” 
  &&  “ ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = resolved) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request resolved ) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ” 
  &&  “ (request = 255) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (mem_copy_post p_task_data_pre (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  (task_query_copy_frame platform critical sg invocation origin retval acquired caller tid )
.

Definition OSTaskQuery_partial_solve_wit_24 := OSTaskQuery_partial_solve_wit_24_pure -> OSTaskQuery_partial_solve_wit_24_aux.

Definition OSTaskQuery_partial_solve_wit_25 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (0 <= key)) (PreH3 : (key <= 63)) (PreH4 : (task_query_task_entry acquired key tid )) (PreH5 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH6 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH7 : ((Zlength (bytes)) = 64)) (PreH8 : (sizeof( "os_tcb" ) = 64)) (PreH9 : (0 <= (task_slot_addr (sg) (tid)))) (PreH10 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH11 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (0 <= output)) (PreH13 : ((output + 64 ) <= UINT_MAX)) (PreH14 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH15 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH16 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH17 : (0 <= key)) (PreH18 : (key <= 63)) (PreH19 : (task_query_priority_resolution sg acquired caller request key )) (PreH20 : (key = resolved)) (PreH21 : (request = 255)) (PreH22 : (task_query_priority_resolution sg acquired caller request resolved )) (PreH23 : (request = 255)) (PreH24 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH25 : (request = 255)) (PreH26 : (retval <= UINT_MAX)) (PreH27 : (retval >= 0)) (PreH28 : (prio_pre = 255)) (PreH29 : (interrupt_saved_value mask retval )) (PreH30 : (critical_region_interval critical sg invocation before acquired )) (PreH31 : (p_task_data_pre <> 0)) (PreH32 : (prio_pre = 255)) (PreH33 : (prio_pre > 63)) (PreH34 : (0 <= request)) (PreH35 : (request <= 255)) (PreH36 : (0 <= UINT_MAX)) (PreH37 : (0 >= 0)) (PreH38 : (prio_pre = request)) (PreH39 : (p_task_data_pre = output)) (PreH40 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH41 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_task_entry acquired key tid ) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_query_source_byte_view sg acquired tid t bytes ) ” 
  &&  “ ((Zlength (bytes)) = 64) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ” 
  &&  “ (0 <= (task_slot_addr (sg) (tid))) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= output) ” 
  &&  “ ((output + 64 ) <= UINT_MAX) ” 
  &&  “ ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = resolved) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request resolved ) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ” 
  &&  “ (request = 255) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
.

Definition OSTaskQuery_partial_solve_wit_26 := 
forall (p_task_data_pre: Z) (prio_pre: Z) (X: (Z -> ((@list (@option Z)) -> (UCOS2_Verify_State -> Prop)))) (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (acquired: UCOS2_Verify_State) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (0 <= key)) (PreH5 : (key <= 63)) (PreH6 : (task_query_task_entry acquired key tid )) (PreH7 : ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid)))) (PreH8 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH9 : ((Zlength (bytes)) = 64)) (PreH10 : (sizeof( "os_tcb" ) = 64)) (PreH11 : (0 <= (task_slot_addr (sg) (tid)))) (PreH12 : (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX)) (PreH13 : (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : (0 <= output)) (PreH15 : ((output + 64 ) <= UINT_MAX)) (PreH16 : ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX)) (PreH17 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) (PreH18 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH19 : (0 <= key)) (PreH20 : (key <= 63)) (PreH21 : (task_query_priority_resolution sg acquired caller request key )) (PreH22 : (key = prio_pre)) (PreH23 : (prio_pre <> 255)) (PreH24 : (interrupt_saved_value mask retval )) (PreH25 : (critical_region_interval critical sg invocation before acquired )) (PreH26 : (p_task_data_pre <> 0)) (PreH27 : (prio_pre <= 63)) (PreH28 : (0 <= request)) (PreH29 : (request <= 255)) (PreH30 : (0 <= UINT_MAX)) (PreH31 : (0 >= 0)) (PreH32 : (prio_pre = request)) (PreH33 : (p_task_data_pre = output)) (PreH34 : (task_query_safe critical sg invocation before caller request output old_output X )) (PreH35 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_task_entry acquired key tid ) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_query_source_byte_view sg acquired tid t bytes ) ” 
  &&  “ ((Zlength (bytes)) = 64) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ” 
  &&  “ (0 <= (task_slot_addr (sg) (tid))) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= output) ” 
  &&  “ ((output + 64 ) <= UINT_MAX) ” 
  &&  “ ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 1) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) <> 0) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ” 
  &&  “ (key = prio_pre) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (p_task_data_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (p_task_data_pre = output) ” 
  &&  “ (task_query_safe critical sg invocation before caller request output old_output X ) ” 
  &&  “ (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin retval acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
.

Definition OSTaskQuery_which_implies_wit_1 := 
(
forall (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_query_valid_arguments request output )) ,
  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  (task_query_closed platform critical sg invocation origin mask before )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
) \/
(
forall (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_query_valid_arguments request output )) ,
  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  (task_query_closed platform critical sg invocation origin mask before )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
).

Definition OSTaskQuery_which_implies_wit_1_split_goal_spatial := 
forall (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_query_valid_arguments request output )) ,
  (task_query_pre platform critical sg invocation origin mask before caller request output old_output )
|--
  (task_query_closed platform critical sg invocation origin mask before )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_which_implies_wit_2 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) ,
  (task_query_save_post platform critical sg invocation origin mask before cpu_sr )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) ,
  (task_query_save_post platform critical sg invocation origin mask before cpu_sr )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
).

Definition OSTaskQuery_which_implies_wit_3 := 
(
forall (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (request = 255)) (PreH2 : (critical_region_interval critical sg invocation before acquired )) (PreH3 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  EX (current: Z)  (resolved: Z)  (residual: Assertion) ,
  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((&((current)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> resolved)
  **  (residual )
  **  (task_query_current_tail platform critical sg invocation origin cpu_sr before acquired caller request output old_output )
) \/
(
forall (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (request = 255)) (PreH2 : (critical_region_interval critical sg invocation before acquired )) (PreH3 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  EX (current: Z)  (resolved: Z)  (residual: Assertion) ,
  “ (request = 255) ” 
  &&  “ (task_query_current_cut sg acquired caller current resolved residual ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((&((current)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> resolved)
  **  (residual )
  **  (task_query_current_tail platform critical sg invocation origin cpu_sr before acquired caller request output old_output )
).

Definition OSTaskQuery_which_implies_wit_4 := 
(
forall (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (cpu_sr: Z) (PreH1 : (request = 255)) (PreH2 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH3 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((&((current)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> resolved)
  **  (residual )
  **  (task_query_current_tail platform critical sg invocation origin cpu_sr before acquired caller request output old_output )
|--
  “ (request = 255) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request resolved ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
) \/
(
forall (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (cpu_sr: Z) (PreH1 : (request = 255)) (PreH2 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH3 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((&((current)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> resolved)
  **  (residual )
  **  (task_query_current_tail platform critical sg invocation origin cpu_sr before acquired caller request output old_output )
|--
  “ (task_query_priority_resolution sg acquired caller 255 resolved ) ”
  &&  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
).

Definition OSTaskQuery_which_implies_wit_4_split_goal_1 := 
forall (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (cpu_sr: Z) (PreH1 : (request = 255)) (PreH2 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH3 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((&((current)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> resolved)
  **  (residual )
  **  (task_query_current_tail platform critical sg invocation origin cpu_sr before acquired caller request output old_output )
|--
  “ (task_query_priority_resolution sg acquired caller 255 resolved ) ”
.

Definition OSTaskQuery_which_implies_wit_4_split_goal_spatial := 
forall (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (current: Z) (resolved: Z) (residual: Assertion) (cpu_sr: Z) (PreH1 : (request = 255)) (PreH2 : (task_query_current_cut sg acquired caller current resolved residual )) (PreH3 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((&((current)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> resolved)
  **  (residual )
  **  (task_query_current_tail platform critical sg invocation origin cpu_sr before acquired caller request output old_output )
|--
  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
.

Definition OSTaskQuery_which_implies_wit_5 := 
forall (local_priority: Z) ,
  TT && emp 
|--
  “ (local_priority = local_priority) ”
  &&  emp
.

Definition OSTaskQuery_which_implies_wit_6 := 
(
forall (request: Z) (caller: Assertion) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (key: Z) (cpu_sr: Z) (PreH1 : (task_query_priority_resolution sg acquired caller request key )) (PreH2 : (0 <= key)) (PreH3 : (key <= 63)) (PreH4 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
|--
  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_priority_resolution sg acquired caller request key ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (key * sizeof(PTR)))) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  (task_query_table_tail platform critical sg invocation origin cpu_sr acquired key )
) \/
(
forall (request: Z) (caller: Assertion) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (key: Z) (cpu_sr: Z) (PreH1 : (task_query_priority_resolution sg acquired caller request key )) (PreH2 : (0 <= key)) (PreH3 : (key <= 63)) (PreH4 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
|--
  (((( &( "OSTCBPrioTbl" ) ) + (key * sizeof(PTR)))) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  (task_query_table_tail platform critical sg invocation origin cpu_sr acquired key )
).

Definition OSTaskQuery_which_implies_wit_6_split_goal_spatial := 
forall (request: Z) (caller: Assertion) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (key: Z) (cpu_sr: Z) (PreH1 : (task_query_priority_resolution sg acquired caller request key )) (PreH2 : (0 <= key)) (PreH3 : (key <= 63)) (PreH4 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
|--
  (((( &( "OSTCBPrioTbl" ) ) + (key * sizeof(PTR)))) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  (task_query_table_tail platform critical sg invocation origin cpu_sr acquired key )
.

Definition OSTaskQuery_which_implies_wit_7 := 
(
forall (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (key: Z) (cpu_sr: Z) (PreH1 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (key * sizeof(PTR)))) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  (task_query_table_tail platform critical sg invocation origin cpu_sr acquired key )
|--
  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
) \/
(
forall (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (key: Z) (cpu_sr: Z) (PreH1 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (key * sizeof(PTR)))) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  (task_query_table_tail platform critical sg invocation origin cpu_sr acquired key )
|--
  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
).

Definition OSTaskQuery_which_implies_wit_7_split_goal_spatial := 
forall (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (key: Z) (cpu_sr: Z) (PreH1 : (task_query_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (key * sizeof(PTR)))) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
  **  (task_query_table_tail platform critical sg invocation origin cpu_sr acquired key )
|--
  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
.

Definition OSTaskQuery_which_implies_wit_8 := 
(
forall (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (key: Z) (cpu_sr: Z) (PreH1 : (task_query_priority_resolution sg acquired caller request key )) (PreH2 : (0 <= key)) (PreH3 : (key <= 63)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH5 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) ,
  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_query_table_value (sg) (acquired) (key)))
|--
  EX (t: TaskAbstractState)  (bytes: (@list Z))  (tid: Z) ,
  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_task_entry acquired key tid ) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_query_source_byte_view sg acquired tid t bytes ) ” 
  &&  “ ((Zlength (bytes)) = 64) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ” 
  &&  “ (0 <= (task_slot_addr (sg) (tid))) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= output) ” 
  &&  “ ((output + 64 ) <= UINT_MAX) ” 
  &&  “ ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ”
  &&  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mem_copy_pre output (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  (task_query_copy_frame platform critical sg invocation origin cpu_sr acquired caller tid )
) \/
(
forall (output: Z) (request: Z) (old_output: (@list (@option Z))) (caller: Assertion) (before: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (key: Z) (cpu_sr: Z) (PreH1 : (task_query_priority_resolution sg acquired caller request key )) (PreH2 : (0 <= key)) (PreH3 : (key <= 63)) (PreH4 : ((task_query_table_value (sg) (acquired) (key)) <> 0)) (PreH5 : ((task_query_table_value (sg) (acquired) (key)) <> 1)) ,
  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
  **  (task_query_entry_frame critical sg invocation before caller request output old_output )
|--
  EX (t: TaskAbstractState)  (bytes: (@list Z))  (tid: Z) ,
  “ ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= key) ” 
  &&  “ (key <= 63) ” 
  &&  “ (task_query_task_entry acquired key tid ) ” 
  &&  “ ((task_query_table_value (sg) (acquired) (key)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_query_source_byte_view sg acquired tid t bytes ) ” 
  &&  “ ((Zlength (bytes)) = 64) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ” 
  &&  “ (0 <= (task_slot_addr (sg) (tid))) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + 64 ) <= UINT_MAX) ” 
  &&  “ (((task_slot_addr (sg) (tid)) + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= output) ” 
  &&  “ ((output + 64 ) <= UINT_MAX) ” 
  &&  “ ((output + (sizeof( "os_tcb" ) * sizeof(UCHAR))) <= UINT_MAX) ”
  &&  (mem_copy_pre output (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  (task_query_copy_frame platform critical sg invocation origin cpu_sr acquired caller tid )
).

Definition OSTaskQuery_which_implies_wit_9 := 
(
forall (p_task_data_pre: Z) (output: Z) (request: Z) (caller: Assertion) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (cpu_sr: Z) (PreH1 : (task_query_priority_resolution sg acquired caller request key )) (PreH2 : (task_query_task_entry acquired key tid )) (PreH3 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH4 : (p_task_data_pre = output)) (PreH5 : (sizeof( "os_tcb" ) = 64)) ,
  (mem_copy_post p_task_data_pre (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  (task_query_copy_frame platform critical sg invocation origin cpu_sr acquired caller tid )
|--
  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
) \/
(
forall (p_task_data_pre: Z) (output: Z) (request: Z) (caller: Assertion) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (cpu_sr: Z) (PreH1 : (task_query_priority_resolution sg acquired caller request key )) (PreH2 : (task_query_task_entry acquired key tid )) (PreH3 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH4 : (p_task_data_pre = output)) (PreH5 : (sizeof( "os_tcb" ) = 64)) ,
  (mem_copy_post p_task_data_pre (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  (task_query_copy_frame platform critical sg invocation origin cpu_sr acquired caller tid )
|--
  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
).

Definition OSTaskQuery_which_implies_wit_9_split_goal_spatial := 
forall (p_task_data_pre: Z) (output: Z) (request: Z) (caller: Assertion) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (key: Z) (tid: Z) (t: TaskAbstractState) (bytes: (@list Z)) (cpu_sr: Z) (PreH1 : (task_query_priority_resolution sg acquired caller request key )) (PreH2 : (task_query_task_entry acquired key tid )) (PreH3 : (task_query_source_byte_view sg acquired tid t bytes )) (PreH4 : (p_task_data_pre = output)) (PreH5 : (sizeof( "os_tcb" ) = 64)) ,
  (mem_copy_post p_task_data_pre (task_slot_addr (sg) (tid)) sizeof( "os_tcb" ) bytes )
  **  (task_query_copy_frame platform critical sg invocation origin cpu_sr acquired caller tid )
|--
  (task_query_restore_pre platform critical sg invocation origin cpu_sr acquired )
  **  (task_query_success_frame sg acquired caller request output bytes )
.

Module Type VC_Correct.


Axiom proof_of_OSTaskQuery_safety_wit_1 : OSTaskQuery_safety_wit_1.
Axiom proof_of_OSTaskQuery_safety_wit_2 : OSTaskQuery_safety_wit_2.
Axiom proof_of_OSTaskQuery_safety_wit_3 : OSTaskQuery_safety_wit_3.
Axiom proof_of_OSTaskQuery_safety_wit_4 : OSTaskQuery_safety_wit_4.
Axiom proof_of_OSTaskQuery_safety_wit_5 : OSTaskQuery_safety_wit_5.
Axiom proof_of_OSTaskQuery_safety_wit_6 : OSTaskQuery_safety_wit_6.
Axiom proof_of_OSTaskQuery_safety_wit_7 : OSTaskQuery_safety_wit_7.
Axiom proof_of_OSTaskQuery_safety_wit_8 : OSTaskQuery_safety_wit_8.
Axiom proof_of_OSTaskQuery_safety_wit_9 : OSTaskQuery_safety_wit_9.
Axiom proof_of_OSTaskQuery_safety_wit_10 : OSTaskQuery_safety_wit_10.
Axiom proof_of_OSTaskQuery_safety_wit_11 : OSTaskQuery_safety_wit_11.
Axiom proof_of_OSTaskQuery_safety_wit_12 : OSTaskQuery_safety_wit_12.
Axiom proof_of_OSTaskQuery_safety_wit_13 : OSTaskQuery_safety_wit_13.
Axiom proof_of_OSTaskQuery_safety_wit_14 : OSTaskQuery_safety_wit_14.
Axiom proof_of_OSTaskQuery_safety_wit_15 : OSTaskQuery_safety_wit_15.
Axiom proof_of_OSTaskQuery_safety_wit_16 : OSTaskQuery_safety_wit_16.
Axiom proof_of_OSTaskQuery_entail_wit_1 : OSTaskQuery_entail_wit_1.
Axiom proof_of_OSTaskQuery_entail_wit_2 : OSTaskQuery_entail_wit_2.
Axiom proof_of_OSTaskQuery_entail_wit_3_1 : OSTaskQuery_entail_wit_3_1.
Axiom proof_of_OSTaskQuery_entail_wit_3_2 : OSTaskQuery_entail_wit_3_2.
Axiom proof_of_OSTaskQuery_entail_wit_4_1 : OSTaskQuery_entail_wit_4_1.
Axiom proof_of_OSTaskQuery_entail_wit_4_2 : OSTaskQuery_entail_wit_4_2.
Axiom proof_of_OSTaskQuery_entail_wit_5_1 : OSTaskQuery_entail_wit_5_1.
Axiom proof_of_OSTaskQuery_entail_wit_5_2 : OSTaskQuery_entail_wit_5_2.
Axiom proof_of_OSTaskQuery_entail_wit_6_1 : OSTaskQuery_entail_wit_6_1.
Axiom proof_of_OSTaskQuery_entail_wit_6_2 : OSTaskQuery_entail_wit_6_2.
Axiom proof_of_OSTaskQuery_return_wit_1 : OSTaskQuery_return_wit_1.
Axiom proof_of_OSTaskQuery_return_wit_2 : OSTaskQuery_return_wit_2.
Axiom proof_of_OSTaskQuery_return_wit_3 : OSTaskQuery_return_wit_3.
Axiom proof_of_OSTaskQuery_return_wit_4 : OSTaskQuery_return_wit_4.
Axiom proof_of_OSTaskQuery_return_wit_5 : OSTaskQuery_return_wit_5.
Axiom proof_of_OSTaskQuery_return_wit_6 : OSTaskQuery_return_wit_6.
Axiom proof_of_OSTaskQuery_return_wit_7 : OSTaskQuery_return_wit_7.
Axiom proof_of_OSTaskQuery_return_wit_8 : OSTaskQuery_return_wit_8.
Axiom proof_of_OSTaskQuery_return_wit_9 : OSTaskQuery_return_wit_9.
Axiom proof_of_OSTaskQuery_partial_solve_wit_1_pure : OSTaskQuery_partial_solve_wit_1_pure.
Axiom proof_of_OSTaskQuery_partial_solve_wit_1 : OSTaskQuery_partial_solve_wit_1.
Axiom proof_of_OSTaskQuery_partial_solve_wit_2_pure : OSTaskQuery_partial_solve_wit_2_pure.
Axiom proof_of_OSTaskQuery_partial_solve_wit_2 : OSTaskQuery_partial_solve_wit_2.
Axiom proof_of_OSTaskQuery_partial_solve_wit_3 : OSTaskQuery_partial_solve_wit_3.
Axiom proof_of_OSTaskQuery_partial_solve_wit_4 : OSTaskQuery_partial_solve_wit_4.
Axiom proof_of_OSTaskQuery_partial_solve_wit_5 : OSTaskQuery_partial_solve_wit_5.
Axiom proof_of_OSTaskQuery_partial_solve_wit_6 : OSTaskQuery_partial_solve_wit_6.
Axiom proof_of_OSTaskQuery_partial_solve_wit_7_pure : OSTaskQuery_partial_solve_wit_7_pure.
Axiom proof_of_OSTaskQuery_partial_solve_wit_7 : OSTaskQuery_partial_solve_wit_7.
Axiom proof_of_OSTaskQuery_partial_solve_wit_8_pure : OSTaskQuery_partial_solve_wit_8_pure.
Axiom proof_of_OSTaskQuery_partial_solve_wit_8 : OSTaskQuery_partial_solve_wit_8.
Axiom proof_of_OSTaskQuery_partial_solve_wit_9 : OSTaskQuery_partial_solve_wit_9.
Axiom proof_of_OSTaskQuery_partial_solve_wit_10 : OSTaskQuery_partial_solve_wit_10.
Axiom proof_of_OSTaskQuery_partial_solve_wit_11_pure : OSTaskQuery_partial_solve_wit_11_pure.
Axiom proof_of_OSTaskQuery_partial_solve_wit_11 : OSTaskQuery_partial_solve_wit_11.
Axiom proof_of_OSTaskQuery_partial_solve_wit_12_pure : OSTaskQuery_partial_solve_wit_12_pure.
Axiom proof_of_OSTaskQuery_partial_solve_wit_12 : OSTaskQuery_partial_solve_wit_12.
Axiom proof_of_OSTaskQuery_partial_solve_wit_13_pure : OSTaskQuery_partial_solve_wit_13_pure.
Axiom proof_of_OSTaskQuery_partial_solve_wit_13 : OSTaskQuery_partial_solve_wit_13.
Axiom proof_of_OSTaskQuery_partial_solve_wit_14_pure : OSTaskQuery_partial_solve_wit_14_pure.
Axiom proof_of_OSTaskQuery_partial_solve_wit_14 : OSTaskQuery_partial_solve_wit_14.
Axiom proof_of_OSTaskQuery_partial_solve_wit_15 : OSTaskQuery_partial_solve_wit_15.
Axiom proof_of_OSTaskQuery_partial_solve_wit_16 : OSTaskQuery_partial_solve_wit_16.
Axiom proof_of_OSTaskQuery_partial_solve_wit_17 : OSTaskQuery_partial_solve_wit_17.
Axiom proof_of_OSTaskQuery_partial_solve_wit_18 : OSTaskQuery_partial_solve_wit_18.
Axiom proof_of_OSTaskQuery_partial_solve_wit_19_pure : OSTaskQuery_partial_solve_wit_19_pure.
Axiom proof_of_OSTaskQuery_partial_solve_wit_19 : OSTaskQuery_partial_solve_wit_19.
Axiom proof_of_OSTaskQuery_partial_solve_wit_20_pure : OSTaskQuery_partial_solve_wit_20_pure.
Axiom proof_of_OSTaskQuery_partial_solve_wit_20 : OSTaskQuery_partial_solve_wit_20.
Axiom proof_of_OSTaskQuery_partial_solve_wit_21_pure : OSTaskQuery_partial_solve_wit_21_pure.
Axiom proof_of_OSTaskQuery_partial_solve_wit_21 : OSTaskQuery_partial_solve_wit_21.
Axiom proof_of_OSTaskQuery_partial_solve_wit_22_pure : OSTaskQuery_partial_solve_wit_22_pure.
Axiom proof_of_OSTaskQuery_partial_solve_wit_22 : OSTaskQuery_partial_solve_wit_22.
Axiom proof_of_OSTaskQuery_partial_solve_wit_23_pure : OSTaskQuery_partial_solve_wit_23_pure.
Axiom proof_of_OSTaskQuery_partial_solve_wit_23 : OSTaskQuery_partial_solve_wit_23.
Axiom proof_of_OSTaskQuery_partial_solve_wit_24_pure : OSTaskQuery_partial_solve_wit_24_pure.
Axiom proof_of_OSTaskQuery_partial_solve_wit_24 : OSTaskQuery_partial_solve_wit_24.
Axiom proof_of_OSTaskQuery_partial_solve_wit_25 : OSTaskQuery_partial_solve_wit_25.
Axiom proof_of_OSTaskQuery_partial_solve_wit_26 : OSTaskQuery_partial_solve_wit_26.
Axiom proof_of_OSTaskQuery_which_implies_wit_1 : OSTaskQuery_which_implies_wit_1.
Axiom proof_of_OSTaskQuery_which_implies_wit_2 : OSTaskQuery_which_implies_wit_2.
Axiom proof_of_OSTaskQuery_which_implies_wit_3 : OSTaskQuery_which_implies_wit_3.
Axiom proof_of_OSTaskQuery_which_implies_wit_4 : OSTaskQuery_which_implies_wit_4.
Axiom proof_of_OSTaskQuery_which_implies_wit_5 : OSTaskQuery_which_implies_wit_5.
Axiom proof_of_OSTaskQuery_which_implies_wit_6 : OSTaskQuery_which_implies_wit_6.
Axiom proof_of_OSTaskQuery_which_implies_wit_7 : OSTaskQuery_which_implies_wit_7.
Axiom proof_of_OSTaskQuery_which_implies_wit_8 : OSTaskQuery_which_implies_wit_8.
Axiom proof_of_OSTaskQuery_which_implies_wit_9 : OSTaskQuery_which_implies_wit_9.

End VC_Correct.
