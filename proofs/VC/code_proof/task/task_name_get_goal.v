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
Require Import Ucos2Verify.VC.code.task.spec.task_name_get_spec.
Require Import Ucos2Verify.VC.code.core.OS_StrLen_goal_check.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTaskNameGet -----*)

Definition OSTaskNameGet_safety_wit_1 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre = 255)) (PreH2 : (prio_pre > 63)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= request)) (PreH5 : (request < 256)) (PreH6 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH7 : (prio_pre = request)) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskNameGet_safety_wit_2 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <= 63)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (0 <= request)) (PreH4 : (request < 256)) (PreH5 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH6 : (prio_pre = request)) (PreH7 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskNameGet_safety_wit_3 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (0 <= (task_name_get_nesting (before)))) (PreH5 : ((task_name_get_nesting (before)) < 256)) (PreH6 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH7 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (pname_pre <> 0)) (PreH9 : (prio_pre = 255)) (PreH10 : (prio_pre > 63)) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (0 <= request)) (PreH13 : (request < 256)) (PreH14 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH15 : (prio_pre = request)) (PreH16 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_raw_rep sg acquired )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskNameGet_safety_wit_4 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (0 <= (task_name_get_nesting (before)))) (PreH5 : ((task_name_get_nesting (before)) < 256)) (PreH6 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH7 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (pname_pre <> 0)) (PreH9 : (prio_pre <= 63)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (0 <= request)) (PreH12 : (request < 256)) (PreH13 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH14 : (prio_pre = request)) (PreH15 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_raw_rep sg acquired )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskNameGet_safety_wit_5 := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (critical_region_interval critical sg invocation before acquired )) (PreH3 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_name_get_resolved sg invocation acquired request prio )) (PreH8 : (UCOS2_state_inv sg acquired )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (UCOS2_state_inv sg acquired )) (PreH11 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH13 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH14 : (critical_region_interval critical sg invocation before acquired )) (PreH15 : (interrupt_saved_value mask cpu_sr )) (PreH16 : (task_name_get_resolved sg invocation acquired request prio )) (PreH17 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_private sg invocation request before )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskNameGet_safety_wit_6 := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_name_get_table_value (sg) (acquired) (prio)) = 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (critical_region_interval critical sg invocation before acquired )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_name_get_resolved sg invocation acquired request prio )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (UCOS2_state_inv sg acquired )) (PreH12 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH14 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH15 : (critical_region_interval critical sg invocation before acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) (PreH17 : (task_name_get_resolved sg invocation acquired request prio )) (PreH18 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request before )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskNameGet_safety_wit_7 := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (critical_region_interval critical sg invocation before acquired )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_name_get_resolved sg invocation acquired request prio )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (UCOS2_state_inv sg acquired )) (PreH12 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH14 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH15 : (critical_region_interval critical sg invocation before acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) (PreH17 : (task_name_get_resolved sg invocation acquired request prio )) (PreH18 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_private sg invocation request before )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OSTaskNameGet_safety_wit_8 := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_name_get_table_value (sg) (acquired) (prio)) = 1)) (PreH2 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (critical_region_interval critical sg invocation before acquired )) (PreH5 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_resolved sg invocation acquired request prio )) (PreH10 : (UCOS2_state_inv sg acquired )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (UCOS2_state_inv sg acquired )) (PreH13 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH15 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (interrupt_saved_value mask cpu_sr )) (PreH18 : (task_name_get_resolved sg invocation acquired request prio )) (PreH19 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request before )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskNameGet_safety_wit_9 := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (previous: Z) (retval: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH3 : (retval = (task_name_get_length ((task_name_get_name (node))) (chars)))) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH6 : (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH11 : (task_name_get_target acquired prio tid node )) (PreH12 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH13 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH14 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH15 : (old = (Some (previous)))) (PreH16 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (critical_region_interval critical sg invocation before acquired )) (PreH20 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH22 : (UCOS2_state_inv sg acquired )) (PreH23 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH24 : (task_name_get_resolved sg invocation acquired request prio )) (PreH25 : (UCOS2_state_inv sg acquired )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (UCOS2_state_inv sg acquired )) (PreH28 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH29 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH30 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH31 : (critical_region_interval critical sg invocation before acquired )) (PreH32 : (interrupt_saved_value mask cpu_sr )) (PreH33 : (task_name_get_resolved sg invocation acquired request prio )) (PreH34 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (task_name_get_private sg invocation request before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
  **  ((( &( "len" ) )) # UChar  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTaskNameGet_entail_wit_1_1 := 
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (0 <= (task_name_get_nesting (before)))) (PreH5 : ((task_name_get_nesting (before)) < 256)) (PreH6 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH7 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (pname_pre <> 0)) (PreH9 : (prio_pre = 255)) (PreH10 : (prio_pre > 63)) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (0 <= request)) (PreH13 : (request < 256)) (PreH14 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH15 : (prio_pre = request)) (PreH16 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (critical_region_masked platform critical sg invocation origin retval acquired_2 )
  **  (UCOS2_raw_rep sg acquired_2 )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  ((( &( "prio" ) )) # UChar  |-> request)
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (0 <= (task_name_get_nesting (before)))) (PreH5 : ((task_name_get_nesting (before)) < 256)) (PreH6 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH7 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (pname_pre <> 0)) (PreH9 : (prio_pre = 255)) (PreH10 : (prio_pre > 63)) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (0 <= request)) (PreH13 : (request < 256)) (PreH14 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH15 : (prio_pre = request)) (PreH16 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (critical_region_masked platform critical sg invocation origin retval acquired_2 )
  **  (UCOS2_raw_rep sg acquired_2 )
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (prio_pre = request) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
).

Definition OSTaskNameGet_entail_wit_1_2 := 
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (0 <= (task_name_get_nesting (before)))) (PreH5 : ((task_name_get_nesting (before)) < 256)) (PreH6 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH7 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (pname_pre <> 0)) (PreH9 : (prio_pre <= 63)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (0 <= request)) (PreH12 : (request < 256)) (PreH13 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH14 : (prio_pre = request)) (PreH15 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (critical_region_masked platform critical sg invocation origin retval acquired_2 )
  **  (UCOS2_raw_rep sg acquired_2 )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  ((( &( "prio" ) )) # UChar  |-> request)
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before acquired_2 )) (PreH2 : (interrupt_saved_value mask retval )) (PreH3 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (0 <= (task_name_get_nesting (before)))) (PreH5 : ((task_name_get_nesting (before)) < 256)) (PreH6 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH7 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (pname_pre <> 0)) (PreH9 : (prio_pre <= 63)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (0 <= request)) (PreH12 : (request < 256)) (PreH13 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH14 : (prio_pre = request)) (PreH15 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (critical_region_masked platform critical sg invocation origin retval acquired_2 )
  **  (UCOS2_raw_rep sg acquired_2 )
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (prio_pre = request) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
).

Definition OSTaskNameGet_entail_wit_2_1 := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (view: TaskNameGetCurrentView) (priority: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_resolved sg invocation acquired request priority )) (PreH3 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (critical_region_interval critical sg invocation before acquired )) (PreH6 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH7 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH8 : (request = 255)) (PreH9 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_name_get_current_view sg invocation acquired view priority )) (PreH11 : ((unsigned_last_nbits (request) (32)) = 255)) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (UCOS2_state_inv sg acquired )) (PreH14 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH16 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH17 : (critical_region_interval critical sg invocation before acquired )) (PreH18 : (interrupt_saved_value mask cpu_sr )) (PreH19 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request priority ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameGet_entail_wit_2_2 := 
(
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH6 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH7 : (critical_region_interval critical sg invocation before acquired )) (PreH8 : (interrupt_saved_value mask cpu_sr )) (PreH9 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request request ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH6 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH7 : (critical_region_interval critical sg invocation before acquired )) (PreH8 : (interrupt_saved_value mask cpu_sr )) (PreH9 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  TT && emp 
|--
  “ (task_name_get_resolved sg invocation acquired request request ) ”
  &&  emp
).

Definition OSTaskNameGet_entail_wit_2_2_split_goal_1 := 
forall (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (request) (32)) <> 255)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH6 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH7 : (critical_region_interval critical sg invocation before acquired )) (PreH8 : (interrupt_saved_value mask cpu_sr )) (PreH9 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_resolved sg invocation acquired request request )
.

Definition OSTaskNameGet_return_wit_1 := 
(
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (previous: Z) (retval: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH3 : (retval = (task_name_get_length ((task_name_get_name (node))) (chars)))) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH6 : (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH11 : (task_name_get_target acquired prio tid node )) (PreH12 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH13 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH14 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH15 : (old = (Some (previous)))) (PreH16 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (critical_region_interval critical sg invocation before acquired )) (PreH20 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH22 : (UCOS2_state_inv sg acquired )) (PreH23 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH24 : (task_name_get_resolved sg invocation acquired request prio )) (PreH25 : (UCOS2_state_inv sg acquired )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (UCOS2_state_inv sg acquired )) (PreH28 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH29 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH30 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH31 : (critical_region_interval critical sg invocation before acquired )) (PreH32 : (interrupt_saved_value mask cpu_sr )) (PreH33 : (task_name_get_resolved sg invocation acquired request prio )) (PreH34 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request before )
  **  ((perr_pre) # UChar  |-> 0)
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old retval X )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (previous: Z) (retval: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH3 : (retval = (task_name_get_length ((task_name_get_name (node))) (chars)))) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH6 : (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH11 : (task_name_get_target acquired prio tid node )) (PreH12 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH13 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH14 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH15 : (old = (Some (previous)))) (PreH16 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (critical_region_interval critical sg invocation before acquired )) (PreH20 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH22 : (UCOS2_state_inv sg acquired )) (PreH23 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH24 : (task_name_get_resolved sg invocation acquired request prio )) (PreH25 : (UCOS2_state_inv sg acquired )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (UCOS2_state_inv sg acquired )) (PreH28 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH29 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH30 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH31 : (critical_region_interval critical sg invocation before acquired )) (PreH32 : (interrupt_saved_value mask cpu_sr )) (PreH33 : (task_name_get_resolved sg invocation acquired request prio )) (PreH34 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request before )
  **  ((perr_pre) # UChar  |-> 0)
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old retval X )
).

Definition OSTaskNameGet_return_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (previous: Z) (retval: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH3 : (retval = (task_name_get_length ((task_name_get_name (node))) (chars)))) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH6 : (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH11 : (task_name_get_target acquired prio tid node )) (PreH12 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH13 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH14 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH15 : (old = (Some (previous)))) (PreH16 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (critical_region_interval critical sg invocation before acquired )) (PreH20 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH22 : (UCOS2_state_inv sg acquired )) (PreH23 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH24 : (task_name_get_resolved sg invocation acquired request prio )) (PreH25 : (UCOS2_state_inv sg acquired )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (UCOS2_state_inv sg acquired )) (PreH28 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH29 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH30 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH31 : (critical_region_interval critical sg invocation before acquired )) (PreH32 : (interrupt_saved_value mask cpu_sr )) (PreH33 : (task_name_get_resolved sg invocation acquired request prio )) (PreH34 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request before )
  **  ((perr_pre) # UChar  |-> 0)
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old retval X )
.

Definition OSTaskNameGet_return_wit_2 := 
(
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_name_get_table_value (sg) (acquired) (prio)) = 1)) (PreH2 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (critical_region_interval critical sg invocation before acquired )) (PreH5 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_resolved sg invocation acquired request prio )) (PreH10 : (UCOS2_state_inv sg acquired )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (UCOS2_state_inv sg acquired )) (PreH13 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH15 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (interrupt_saved_value mask cpu_sr )) (PreH18 : (task_name_get_resolved sg invocation acquired request prio )) (PreH19 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request before )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |-> 67)
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_name_get_table_value (sg) (acquired) (prio)) = 1)) (PreH2 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (critical_region_interval critical sg invocation before acquired )) (PreH5 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_resolved sg invocation acquired request prio )) (PreH10 : (UCOS2_state_inv sg acquired )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (UCOS2_state_inv sg acquired )) (PreH13 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH15 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (interrupt_saved_value mask cpu_sr )) (PreH18 : (task_name_get_resolved sg invocation acquired request prio )) (PreH19 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request before )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |-> 67)
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
).

Definition OSTaskNameGet_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_name_get_table_value (sg) (acquired) (prio)) = 1)) (PreH2 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (critical_region_interval critical sg invocation before acquired )) (PreH5 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_resolved sg invocation acquired request prio )) (PreH10 : (UCOS2_state_inv sg acquired )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (UCOS2_state_inv sg acquired )) (PreH13 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH15 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (interrupt_saved_value mask cpu_sr )) (PreH18 : (task_name_get_resolved sg invocation acquired request prio )) (PreH19 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request before )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |-> 67)
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
.

Definition OSTaskNameGet_return_wit_3 := 
(
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_name_get_table_value (sg) (acquired) (prio)) = 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (critical_region_interval critical sg invocation before acquired )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_name_get_resolved sg invocation acquired request prio )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (UCOS2_state_inv sg acquired )) (PreH12 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH14 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH15 : (critical_region_interval critical sg invocation before acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) (PreH17 : (task_name_get_resolved sg invocation acquired request prio )) (PreH18 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request before )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |-> 67)
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_name_get_table_value (sg) (acquired) (prio)) = 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (critical_region_interval critical sg invocation before acquired )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_name_get_resolved sg invocation acquired request prio )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (UCOS2_state_inv sg acquired )) (PreH12 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH14 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH15 : (critical_region_interval critical sg invocation before acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) (PreH17 : (task_name_get_resolved sg invocation acquired request prio )) (PreH18 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request before )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |-> 67)
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
).

Definition OSTaskNameGet_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_name_get_table_value (sg) (acquired) (prio)) = 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (critical_region_interval critical sg invocation before acquired )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_name_get_resolved sg invocation acquired request prio )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (UCOS2_state_inv sg acquired )) (PreH12 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH14 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH15 : (critical_region_interval critical sg invocation before acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) (PreH17 : (task_name_get_resolved sg invocation acquired request prio )) (PreH18 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request before )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |-> 67)
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
.

Definition OSTaskNameGet_return_wit_4 := 
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH3 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (pname_pre <> 0)) (PreH5 : (prio_pre = 255)) (PreH6 : (prio_pre > 63)) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (0 <= request)) (PreH9 : (request < 256)) (PreH10 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH11 : (prio_pre = request)) (PreH12 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 17)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH3 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (pname_pre <> 0)) (PreH5 : (prio_pre = 255)) (PreH6 : (prio_pre > 63)) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (0 <= request)) (PreH9 : (request < 256)) (PreH10 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH11 : (prio_pre = request)) (PreH12 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 17)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
).

Definition OSTaskNameGet_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH3 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (pname_pre <> 0)) (PreH5 : (prio_pre = 255)) (PreH6 : (prio_pre > 63)) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (0 <= request)) (PreH9 : (request < 256)) (PreH10 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH11 : (prio_pre = request)) (PreH12 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 17)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
.

Definition OSTaskNameGet_return_wit_5 := 
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH3 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (pname_pre <> 0)) (PreH5 : (prio_pre <= 63)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (0 <= request)) (PreH8 : (request < 256)) (PreH9 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH10 : (prio_pre = request)) (PreH11 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 17)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH3 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (pname_pre <> 0)) (PreH5 : (prio_pre <= 63)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (0 <= request)) (PreH8 : (request < 256)) (PreH9 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH10 : (prio_pre = request)) (PreH11 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 17)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
).

Definition OSTaskNameGet_return_wit_5_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH3 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (pname_pre <> 0)) (PreH5 : (prio_pre <= 63)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (0 <= request)) (PreH8 : (request < 256)) (PreH9 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH10 : (prio_pre = request)) (PreH11 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 17)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
.

Definition OSTaskNameGet_return_wit_6 := 
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= request)) (PreH6 : (request < 256)) (PreH7 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH8 : (prio_pre = request)) (PreH9 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 12)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= request)) (PreH6 : (request < 256)) (PreH7 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH8 : (prio_pre = request)) (PreH9 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 12)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
).

Definition OSTaskNameGet_return_wit_6_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= request)) (PreH6 : (request < 256)) (PreH7 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH8 : (prio_pre = request)) (PreH9 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 12)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
.

Definition OSTaskNameGet_return_wit_7 := 
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= request)) (PreH5 : (request < 256)) (PreH6 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH7 : (prio_pre = request)) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 12)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= request)) (PreH5 : (request < 256)) (PreH6 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH7 : (prio_pre = request)) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 12)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
).

Definition OSTaskNameGet_return_wit_7_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= request)) (PreH5 : (request < 256)) (PreH6 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH7 : (prio_pre = request)) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 12)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
.

Definition OSTaskNameGet_return_wit_8 := 
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre > 63)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= request)) (PreH5 : (request < 256)) (PreH6 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH7 : (prio_pre = request)) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 42)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre > 63)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= request)) (PreH5 : (request < 256)) (PreH6 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH7 : (prio_pre = request)) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 42)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
).

Definition OSTaskNameGet_return_wit_8_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre <> 255)) (PreH2 : (prio_pre > 63)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= request)) (PreH5 : (request < 256)) (PreH6 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH7 : (prio_pre = request)) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 42)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  (task_name_get_post platform critical sg invocation origin mask before request pname_pre perr_pre old 0 X )
.

Definition OSTaskNameGet_partial_solve_wit_1 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (prio_pre = request)) (PreH2 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_pre platform critical sg invocation origin mask before request pname_pre perr_pre old )
|--
  “ (prio_pre = request) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (task_name_get_pre platform critical sg invocation origin mask before request pname_pre perr_pre old )
.

Definition OSTaskNameGet_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= request)) (PreH5 : (request < 256)) (PreH6 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH7 : (prio_pre = request)) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
.

Definition OSTaskNameGet_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (prio_pre <= 63)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= request)) (PreH5 : (request < 256)) (PreH6 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH7 : (prio_pre = request)) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request < 256) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
.

Definition OSTaskNameGet_partial_solve_wit_2 := OSTaskNameGet_partial_solve_wit_2_pure -> OSTaskNameGet_partial_solve_wit_2_aux.

Definition OSTaskNameGet_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= request)) (PreH6 : (request < 256)) (PreH7 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH8 : (prio_pre = request)) (PreH9 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
.

Definition OSTaskNameGet_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (prio_pre = 255)) (PreH3 : (prio_pre > 63)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= request)) (PreH6 : (request < 256)) (PreH7 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH8 : (prio_pre = request)) (PreH9 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request < 256) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
.

Definition OSTaskNameGet_partial_solve_wit_3 := OSTaskNameGet_partial_solve_wit_3_pure -> OSTaskNameGet_partial_solve_wit_3_aux.

Definition OSTaskNameGet_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH2 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (pname_pre <> 0)) (PreH4 : (prio_pre <= 63)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (0 <= request)) (PreH7 : (request < 256)) (PreH8 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH9 : (prio_pre = request)) (PreH10 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
.

Definition OSTaskNameGet_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH2 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (pname_pre <> 0)) (PreH4 : (prio_pre <= 63)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (0 <= request)) (PreH7 : (request < 256)) (PreH8 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH9 : (prio_pre = request)) (PreH10 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request < 256) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
.

Definition OSTaskNameGet_partial_solve_wit_4 := OSTaskNameGet_partial_solve_wit_4_pure -> OSTaskNameGet_partial_solve_wit_4_aux.

Definition OSTaskNameGet_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH2 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (pname_pre <> 0)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre > 63)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (0 <= request)) (PreH8 : (request < 256)) (PreH9 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH10 : (prio_pre = request)) (PreH11 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
.

Definition OSTaskNameGet_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH2 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (pname_pre <> 0)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre > 63)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (0 <= request)) (PreH8 : (request < 256)) (PreH9 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH10 : (prio_pre = request)) (PreH11 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request < 256) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
.

Definition OSTaskNameGet_partial_solve_wit_5 := OSTaskNameGet_partial_solve_wit_5_pure -> OSTaskNameGet_partial_solve_wit_5_aux.

Definition OSTaskNameGet_partial_solve_wit_6_pure := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH2 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (pname_pre <> 0)) (PreH4 : (prio_pre <= 63)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (0 <= request)) (PreH7 : (request < 256)) (PreH8 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH9 : (prio_pre = request)) (PreH10 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
.

Definition OSTaskNameGet_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH2 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (pname_pre <> 0)) (PreH4 : (prio_pre <= 63)) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (0 <= request)) (PreH7 : (request < 256)) (PreH8 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH9 : (prio_pre = request)) (PreH10 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH11 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request < 256) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
.

Definition OSTaskNameGet_partial_solve_wit_6 := OSTaskNameGet_partial_solve_wit_6_pure -> OSTaskNameGet_partial_solve_wit_6_aux.

Definition OSTaskNameGet_partial_solve_wit_7_pure := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH2 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (pname_pre <> 0)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre > 63)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (0 <= request)) (PreH8 : (request < 256)) (PreH9 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH10 : (prio_pre = request)) (PreH11 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
.

Definition OSTaskNameGet_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH2 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (pname_pre <> 0)) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre > 63)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (0 <= request)) (PreH8 : (request < 256)) (PreH9 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH10 : (prio_pre = request)) (PreH11 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request < 256) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
.

Definition OSTaskNameGet_partial_solve_wit_7 := OSTaskNameGet_partial_solve_wit_7_pure -> OSTaskNameGet_partial_solve_wit_7_aux.

Definition OSTaskNameGet_partial_solve_wit_8 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (0 <= (task_name_get_nesting (before)))) (PreH3 : ((task_name_get_nesting (before)) < 256)) (PreH4 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH5 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (pname_pre <> 0)) (PreH7 : (prio_pre <= 63)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (0 <= request)) (PreH10 : (request < 256)) (PreH11 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH12 : (prio_pre = request)) (PreH13 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= (task_name_get_nesting (before))) ” 
  &&  “ ((task_name_get_nesting (before)) < 256) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request < 256) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
.

Definition OSTaskNameGet_partial_solve_wit_9 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (0 <= (task_name_get_nesting (before)))) (PreH3 : ((task_name_get_nesting (before)) < 256)) (PreH4 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH5 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (pname_pre <> 0)) (PreH7 : (prio_pre = 255)) (PreH8 : (prio_pre > 63)) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (0 <= request)) (PreH11 : (request < 256)) (PreH12 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH13 : (prio_pre = request)) (PreH14 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= (task_name_get_nesting (before))) ” 
  &&  “ ((task_name_get_nesting (before)) < 256) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request < 256) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
.

Definition OSTaskNameGet_partial_solve_wit_10 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (0 <= (task_name_get_nesting (before)))) (PreH3 : ((task_name_get_nesting (before)) < 256)) (PreH4 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH5 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (pname_pre <> 0)) (PreH7 : (prio_pre = 255)) (PreH8 : (prio_pre > 63)) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (0 <= request)) (PreH11 : (request < 256)) (PreH12 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH13 : (prio_pre = request)) (PreH14 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= (task_name_get_nesting (before))) ” 
  &&  “ ((task_name_get_nesting (before)) < 256) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre > 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request < 256) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
.

Definition OSTaskNameGet_partial_solve_wit_11 := 
forall (perr_pre: Z) (pname_pre: Z) (prio_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (0 <= (task_name_get_nesting (before)))) (PreH3 : ((task_name_get_nesting (before)) < 256)) (PreH4 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH5 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (pname_pre <> 0)) (PreH7 : (prio_pre <= 63)) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (0 <= request)) (PreH10 : (request < 256)) (PreH11 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH12 : (prio_pre = request)) (PreH13 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= (task_name_get_nesting (before))) ” 
  &&  “ ((task_name_get_nesting (before)) < 256) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (prio_pre <= 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request < 256) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (prio_pre = request) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_guarded_private sg invocation request pname_pre before )
.

Definition OSTaskNameGet_partial_solve_wit_12_pure := 
(
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (request) (32)) = 255)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH6 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH7 : (critical_region_interval critical sg invocation before acquired )) (PreH8 : (interrupt_saved_value mask cpu_sr )) (PreH9 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((( &( "prio" ) )) # UChar  |-> request)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (request = 255) ”
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits (request) (32)) = 255)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH8 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH9 : (critical_region_interval critical sg invocation before acquired )) (PreH10 : (interrupt_saved_value mask cpu_sr )) (PreH11 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((( &( "prio" ) )) # UChar  |-> request)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (request = 255) ”
).

Definition OSTaskNameGet_partial_solve_wit_12_pure_split_goal_1 := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits (request) (32)) = 255)) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH8 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH9 : (critical_region_interval critical sg invocation before acquired )) (PreH10 : (interrupt_saved_value mask cpu_sr )) (PreH11 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((( &( "prio" ) )) # UChar  |-> request)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (request = 255) ”
.

Definition OSTaskNameGet_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (request) (32)) = 255)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH6 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH7 : (critical_region_interval critical sg invocation before acquired )) (PreH8 : (interrupt_saved_value mask cpu_sr )) (PreH9 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (request = 255) ” 
  &&  “ ((unsigned_last_nbits (request) (32)) = 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameGet_partial_solve_wit_12 := OSTaskNameGet_partial_solve_wit_12_pure -> OSTaskNameGet_partial_solve_wit_12_aux.

Definition OSTaskNameGet_partial_solve_wit_13_pure := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (view: TaskNameGetCurrentView) (priority: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (critical_region_interval critical sg invocation before acquired )) (PreH3 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH4 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH5 : (request = 255)) (PreH6 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_name_get_current_view sg invocation acquired view priority )) (PreH8 : ((unsigned_last_nbits (request) (32)) = 255)) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (UCOS2_state_inv sg acquired )) (PreH11 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH13 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH14 : (critical_region_interval critical sg invocation before acquired )) (PreH15 : (interrupt_saved_value mask cpu_sr )) (PreH16 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_name_get_current_pointer (sg) (view)))
  **  ((&(((task_name_get_current_pointer (sg) (view)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (task_name_get_current_residual sg invocation acquired view )
  **  ((( &( "prio" ) )) # UChar  |-> priority)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_name_get_current_view sg invocation acquired view priority ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
.

Definition OSTaskNameGet_partial_solve_wit_13_aux := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (view: TaskNameGetCurrentView) (priority: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (critical_region_interval critical sg invocation before acquired )) (PreH3 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH4 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH5 : (request = 255)) (PreH6 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : (task_name_get_current_view sg invocation acquired view priority )) (PreH8 : ((unsigned_last_nbits (request) (32)) = 255)) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (UCOS2_state_inv sg acquired )) (PreH11 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH12 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH13 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH14 : (critical_region_interval critical sg invocation before acquired )) (PreH15 : (interrupt_saved_value mask cpu_sr )) (PreH16 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_name_get_current_pointer (sg) (view)))
  **  ((&(((task_name_get_current_pointer (sg) (view)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (task_name_get_current_residual sg invocation acquired view )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_name_get_current_view sg invocation acquired view priority ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_current_view sg invocation acquired view priority ) ” 
  &&  “ ((unsigned_last_nbits (request) (32)) = 255) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_name_get_current_pointer (sg) (view)))
  **  ((&(((task_name_get_current_pointer (sg) (view)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (task_name_get_current_residual sg invocation acquired view )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameGet_partial_solve_wit_13 := OSTaskNameGet_partial_solve_wit_13_pure -> OSTaskNameGet_partial_solve_wit_13_aux.

Definition OSTaskNameGet_partial_solve_wit_14_pure := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH5 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH6 : (critical_region_interval critical sg invocation before acquired )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (task_name_get_resolved sg invocation acquired request prio )) (PreH9 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ”
.

Definition OSTaskNameGet_partial_solve_wit_14_aux := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH5 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH6 : (critical_region_interval critical sg invocation before acquired )) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (task_name_get_resolved sg invocation acquired request prio )) (PreH9 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (UCOS2_inv sg acquired )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameGet_partial_solve_wit_14 := OSTaskNameGet_partial_solve_wit_14_pure -> OSTaskNameGet_partial_solve_wit_14_aux.

Definition OSTaskNameGet_partial_solve_wit_15_pure := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (task_name_get_resolved sg invocation acquired request prio )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH8 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH9 : (critical_region_interval critical sg invocation before acquired )) (PreH10 : (interrupt_saved_value mask cpu_sr )) (PreH11 : (task_name_get_resolved sg invocation acquired request prio )) (PreH12 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  (task_name_get_table_residual sg acquired prio )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) = (task_name_get_table_value (sg) (acquired) (prio))) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ”
.

Definition OSTaskNameGet_partial_solve_wit_15_aux := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (task_name_get_resolved sg invocation acquired request prio )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH7 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH8 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH9 : (critical_region_interval critical sg invocation before acquired )) (PreH10 : (interrupt_saved_value mask cpu_sr )) (PreH11 : (task_name_get_resolved sg invocation acquired request prio )) (PreH12 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  (task_name_get_table_residual sg acquired prio )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) = (task_name_get_table_value (sg) (acquired) (prio))) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  (task_name_get_table_residual sg acquired prio )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameGet_partial_solve_wit_15 := OSTaskNameGet_partial_solve_wit_15_pure -> OSTaskNameGet_partial_solve_wit_15_aux.

Definition OSTaskNameGet_partial_solve_wit_16_pure := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_name_get_resolved sg invocation acquired request prio )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (UCOS2_state_inv sg acquired )) (PreH9 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH11 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH12 : (critical_region_interval critical sg invocation before acquired )) (PreH13 : (interrupt_saved_value mask cpu_sr )) (PreH14 : (task_name_get_resolved sg invocation acquired request prio )) (PreH15 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ”
.

Definition OSTaskNameGet_partial_solve_wit_16_aux := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_name_get_resolved sg invocation acquired request prio )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (UCOS2_state_inv sg acquired )) (PreH9 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH11 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH12 : (critical_region_interval critical sg invocation before acquired )) (PreH13 : (interrupt_saved_value mask cpu_sr )) (PreH14 : (task_name_get_resolved sg invocation acquired request prio )) (PreH15 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (UCOS2_inv sg acquired )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_private sg invocation request acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (task_name_get_private sg invocation request acquired )
  **  (UCOS2_inv sg acquired )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameGet_partial_solve_wit_16 := OSTaskNameGet_partial_solve_wit_16_pure -> OSTaskNameGet_partial_solve_wit_16_aux.

Definition OSTaskNameGet_partial_solve_wit_17_pure := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_name_get_table_value (sg) (acquired) (prio)) = 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (critical_region_interval critical sg invocation before acquired )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_name_get_resolved sg invocation acquired request prio )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (UCOS2_state_inv sg acquired )) (PreH12 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH14 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH15 : (critical_region_interval critical sg invocation before acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) (PreH17 : (task_name_get_resolved sg invocation acquired request prio )) (PreH18 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_private sg invocation request before )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskNameGet_partial_solve_wit_17_aux := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_name_get_table_value (sg) (acquired) (prio)) = 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (critical_region_interval critical sg invocation before acquired )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (task_name_get_resolved sg invocation acquired request prio )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (UCOS2_state_inv sg acquired )) (PreH12 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH14 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH15 : (critical_region_interval critical sg invocation before acquired )) (PreH16 : (interrupt_saved_value mask cpu_sr )) (PreH17 : (task_name_get_resolved sg invocation acquired request prio )) (PreH18 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_private sg invocation request before )
  **  (UCOS2_inv sg acquired )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) = 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request before )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameGet_partial_solve_wit_17 := OSTaskNameGet_partial_solve_wit_17_pure -> OSTaskNameGet_partial_solve_wit_17_aux.

Definition OSTaskNameGet_partial_solve_wit_18_pure := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_name_get_table_value (sg) (acquired) (prio)) = 1)) (PreH2 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (critical_region_interval critical sg invocation before acquired )) (PreH5 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_resolved sg invocation acquired request prio )) (PreH10 : (UCOS2_state_inv sg acquired )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (UCOS2_state_inv sg acquired )) (PreH13 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH15 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (interrupt_saved_value mask cpu_sr )) (PreH18 : (task_name_get_resolved sg invocation acquired request prio )) (PreH19 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_private sg invocation request before )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskNameGet_partial_solve_wit_18_aux := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_name_get_table_value (sg) (acquired) (prio)) = 1)) (PreH2 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (critical_region_interval critical sg invocation before acquired )) (PreH5 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_resolved sg invocation acquired request prio )) (PreH10 : (UCOS2_state_inv sg acquired )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (UCOS2_state_inv sg acquired )) (PreH13 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH15 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (interrupt_saved_value mask cpu_sr )) (PreH18 : (task_name_get_resolved sg invocation acquired request prio )) (PreH19 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_private sg invocation request before )
  **  (UCOS2_inv sg acquired )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) = 1) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request before )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameGet_partial_solve_wit_18 := OSTaskNameGet_partial_solve_wit_18_pure -> OSTaskNameGet_partial_solve_wit_18_aux.

Definition OSTaskNameGet_partial_solve_wit_19_pure := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH2 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (critical_region_interval critical sg invocation before acquired )) (PreH5 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_resolved sg invocation acquired request prio )) (PreH10 : (UCOS2_state_inv sg acquired )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (UCOS2_state_inv sg acquired )) (PreH13 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH15 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (interrupt_saved_value mask cpu_sr )) (PreH18 : (task_name_get_resolved sg invocation acquired request prio )) (PreH19 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_private sg invocation request before )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ”
.

Definition OSTaskNameGet_partial_solve_wit_19_aux := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (PreH1 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH2 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (critical_region_interval critical sg invocation before acquired )) (PreH5 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH6 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_name_get_resolved sg invocation acquired request prio )) (PreH10 : (UCOS2_state_inv sg acquired )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (UCOS2_state_inv sg acquired )) (PreH13 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH15 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (interrupt_saved_value mask cpu_sr )) (PreH18 : (task_name_get_resolved sg invocation acquired request prio )) (PreH19 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_private sg invocation request before )
  **  (UCOS2_inv sg acquired )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (UCOS2_inv sg acquired )
  **  (task_name_get_output_cell pname_pre old )
  **  (task_name_get_private sg invocation request before )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameGet_partial_solve_wit_19 := OSTaskNameGet_partial_solve_wit_19_pure -> OSTaskNameGet_partial_solve_wit_19_aux.

Definition OSTaskNameGet_partial_solve_wit_20_pure := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (previous: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH3 : (task_name_get_target acquired prio tid node )) (PreH4 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH5 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH6 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH7 : (old = (Some (previous)))) (PreH8 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH9 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_name_get_resolved sg invocation acquired request prio )) (PreH17 : (UCOS2_state_inv sg acquired )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (UCOS2_state_inv sg acquired )) (PreH20 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH22 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH23 : (critical_region_interval critical sg invocation before acquired )) (PreH24 : (interrupt_saved_value mask cpu_sr )) (PreH25 : (task_name_get_resolved sg invocation acquired request prio )) (PreH26 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((&(((task_name_get_table_value (sg) (acquired) (prio)))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (task_name_get_name (node)))
  **  (task_name_get_name_field_residual sg acquired tid node )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
  **  (task_name_get_private sg invocation request before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_target acquired prio tid node ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ”
.

Definition OSTaskNameGet_partial_solve_wit_20_aux := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (previous: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH3 : (task_name_get_target acquired prio tid node )) (PreH4 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH5 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH6 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH7 : (old = (Some (previous)))) (PreH8 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH9 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (critical_region_interval critical sg invocation before acquired )) (PreH12 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH14 : (UCOS2_state_inv sg acquired )) (PreH15 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_name_get_resolved sg invocation acquired request prio )) (PreH17 : (UCOS2_state_inv sg acquired )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (UCOS2_state_inv sg acquired )) (PreH20 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH22 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH23 : (critical_region_interval critical sg invocation before acquired )) (PreH24 : (interrupt_saved_value mask cpu_sr )) (PreH25 : (task_name_get_resolved sg invocation acquired request prio )) (PreH26 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((&(((task_name_get_table_value (sg) (acquired) (prio)))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (task_name_get_name (node)))
  **  (task_name_get_name_field_residual sg acquired tid node )
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
  **  (task_name_get_private sg invocation request before )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_target acquired prio tid node ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (task_name_get_target acquired prio tid node ) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  ((&(((task_name_get_table_value (sg) (acquired) (prio)))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (task_name_get_name (node)))
  **  (task_name_get_name_field_residual sg acquired tid node )
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
  **  (task_name_get_private sg invocation request before )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameGet_partial_solve_wit_20 := OSTaskNameGet_partial_solve_wit_20_pure -> OSTaskNameGet_partial_solve_wit_20_aux.

Definition OSTaskNameGet_partial_solve_wit_21_pure := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (previous: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH5 : (task_name_get_target acquired prio tid node )) (PreH6 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH7 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH8 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH9 : (old = (Some (previous)))) (PreH10 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH11 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (critical_region_interval critical sg invocation before acquired )) (PreH14 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH16 : (UCOS2_state_inv sg acquired )) (PreH17 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH18 : (task_name_get_resolved sg invocation acquired request prio )) (PreH19 : (UCOS2_state_inv sg acquired )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (UCOS2_state_inv sg acquired )) (PreH22 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH23 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH24 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH25 : (critical_region_interval critical sg invocation before acquired )) (PreH26 : (interrupt_saved_value mask cpu_sr )) (PreH27 : (task_name_get_resolved sg invocation acquired request prio )) (PreH28 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
  **  (task_name_get_private sg invocation request before )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ”
.

Definition OSTaskNameGet_partial_solve_wit_21_aux := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (previous: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH3 : (UCOS2_state_inv sg acquired )) (PreH4 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH5 : (task_name_get_target acquired prio tid node )) (PreH6 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH7 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH8 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH9 : (old = (Some (previous)))) (PreH10 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH11 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (critical_region_interval critical sg invocation before acquired )) (PreH14 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH16 : (UCOS2_state_inv sg acquired )) (PreH17 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH18 : (task_name_get_resolved sg invocation acquired request prio )) (PreH19 : (UCOS2_state_inv sg acquired )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (UCOS2_state_inv sg acquired )) (PreH22 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH23 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH24 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH25 : (critical_region_interval critical sg invocation before acquired )) (PreH26 : (interrupt_saved_value mask cpu_sr )) (PreH27 : (task_name_get_resolved sg invocation acquired request prio )) (PreH28 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (UCOS2_inv sg acquired )
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
  **  (task_name_get_private sg invocation request before )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (task_name_get_target acquired prio tid node ) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (UCOS2_inv sg acquired )
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
  **  (task_name_get_private sg invocation request before )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTaskNameGet_partial_solve_wit_21 := OSTaskNameGet_partial_solve_wit_21_pure -> OSTaskNameGet_partial_solve_wit_21_aux.

Definition OSTaskNameGet_partial_solve_wit_22 := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (previous: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH3 : (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars )) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH8 : (task_name_get_target acquired prio tid node )) (PreH9 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH10 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH11 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH12 : (old = (Some (previous)))) (PreH13 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH14 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH18 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH19 : (UCOS2_state_inv sg acquired )) (PreH20 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : (task_name_get_resolved sg invocation acquired request prio )) (PreH22 : (UCOS2_state_inv sg acquired )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH26 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH27 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH28 : (critical_region_interval critical sg invocation before acquired )) (PreH29 : (interrupt_saved_value mask cpu_sr )) (PreH30 : (task_name_get_resolved sg invocation acquired request prio )) (PreH31 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_name_bytes (task_name_get_name (node)) chars )
  **  (task_name_get_name_frame sg acquired (task_name_get_name (node)) chars )
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
  **  (task_name_get_private sg invocation request before )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (task_name_get_target acquired prio tid node ) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (task_name_get_name_frame sg acquired (task_name_get_name (node)) chars )
  **  (task_name_get_private sg invocation request before )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_name_bytes (task_name_get_name (node)) chars )
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
.

Definition OSTaskNameGet_partial_solve_wit_23_pure := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (previous: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH3 : (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars )) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH8 : (task_name_get_target acquired prio tid node )) (PreH9 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH10 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH11 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH12 : (old = (Some (previous)))) (PreH13 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH14 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH18 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH19 : (UCOS2_state_inv sg acquired )) (PreH20 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : (task_name_get_resolved sg invocation acquired request prio )) (PreH22 : (UCOS2_state_inv sg acquired )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH26 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH27 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH28 : (critical_region_interval critical sg invocation before acquired )) (PreH29 : (interrupt_saved_value mask cpu_sr )) (PreH30 : (task_name_get_resolved sg invocation acquired request prio )) (PreH31 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_name_get_call_frame platform critical sg invocation origin cpu_sr before acquired request perr_pre (task_name_get_name (node)) chars )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (task_name_get_name_bytes (task_name_get_name (node)) chars )
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ ((task_name_get_name (node)) = (task_name_get_name (node))) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars ) ”
.

Definition OSTaskNameGet_partial_solve_wit_23_aux := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (previous: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH3 : (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars )) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH6 : (UCOS2_state_inv sg acquired )) (PreH7 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH8 : (task_name_get_target acquired prio tid node )) (PreH9 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH10 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH11 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH12 : (old = (Some (previous)))) (PreH13 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH14 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (critical_region_interval critical sg invocation before acquired )) (PreH17 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH18 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH19 : (UCOS2_state_inv sg acquired )) (PreH20 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : (task_name_get_resolved sg invocation acquired request prio )) (PreH22 : (UCOS2_state_inv sg acquired )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (UCOS2_state_inv sg acquired )) (PreH25 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH26 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH27 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH28 : (critical_region_interval critical sg invocation before acquired )) (PreH29 : (interrupt_saved_value mask cpu_sr )) (PreH30 : (task_name_get_resolved sg invocation acquired request prio )) (PreH31 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_call_frame platform critical sg invocation origin cpu_sr before acquired request perr_pre (task_name_get_name (node)) chars )
  **  (task_name_get_name_bytes (task_name_get_name (node)) chars )
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
|--
  “ ((task_name_get_name (node)) = (task_name_get_name (node))) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (task_name_get_target acquired prio tid node ) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (task_name_get_name_bytes (task_name_get_name (node)) chars )
  **  (task_name_get_call_frame platform critical sg invocation origin cpu_sr before acquired request perr_pre (task_name_get_name (node)) chars )
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
.

Definition OSTaskNameGet_partial_solve_wit_23 := OSTaskNameGet_partial_solve_wit_23_pure -> OSTaskNameGet_partial_solve_wit_23_aux.

Definition OSTaskNameGet_partial_solve_wit_24 := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (previous: Z) (retval: Z) (PreH1 : (retval = (task_name_get_length ((task_name_get_name (node))) (chars)))) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH4 : (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH9 : (task_name_get_target acquired prio tid node )) (PreH10 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH11 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH12 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH13 : (old = (Some (previous)))) (PreH14 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH15 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (critical_region_interval critical sg invocation before acquired )) (PreH18 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH19 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH22 : (task_name_get_resolved sg invocation acquired request prio )) (PreH23 : (UCOS2_state_inv sg acquired )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (UCOS2_state_inv sg acquired )) (PreH26 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH27 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH28 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH29 : (critical_region_interval critical sg invocation before acquired )) (PreH30 : (interrupt_saved_value mask cpu_sr )) (PreH31 : (task_name_get_resolved sg invocation acquired request prio )) (PreH32 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_name_bytes (task_name_get_name (node)) chars )
  **  (task_name_get_call_frame platform critical sg invocation origin cpu_sr before acquired request perr_pre (task_name_get_name (node)) chars )
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
|--
  “ (retval = (task_name_get_length ((task_name_get_name (node))) (chars))) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (task_name_get_target acquired prio tid node ) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (task_name_get_call_frame platform critical sg invocation origin cpu_sr before acquired request perr_pre (task_name_get_name (node)) chars )
  **  (task_name_get_name_bytes (task_name_get_name (node)) chars )
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
.

Definition OSTaskNameGet_partial_solve_wit_25_pure := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (previous: Z) (retval: Z) (PreH1 : (retval = (task_name_get_length ((task_name_get_name (node))) (chars)))) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH4 : (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH9 : (task_name_get_target acquired prio tid node )) (PreH10 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH11 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH12 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH13 : (old = (Some (previous)))) (PreH14 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH15 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (critical_region_interval critical sg invocation before acquired )) (PreH18 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH19 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH22 : (task_name_get_resolved sg invocation acquired request prio )) (PreH23 : (UCOS2_state_inv sg acquired )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (UCOS2_state_inv sg acquired )) (PreH26 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH27 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH28 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH29 : (critical_region_interval critical sg invocation before acquired )) (PreH30 : (interrupt_saved_value mask cpu_sr )) (PreH31 : (task_name_get_resolved sg invocation acquired request prio )) (PreH32 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_name_frame sg acquired (task_name_get_name (node)) chars )
  **  (task_name_get_private sg invocation request before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_name_bytes (task_name_get_name (node)) chars )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
  **  ((( &( "len" ) )) # UChar  |-> retval)
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ”
.

Definition OSTaskNameGet_partial_solve_wit_25_aux := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (previous: Z) (retval: Z) (PreH1 : (retval = (task_name_get_length ((task_name_get_name (node))) (chars)))) (PreH2 : (UCOS2_state_inv sg acquired )) (PreH3 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH4 : (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars )) (PreH5 : (UCOS2_state_inv sg acquired )) (PreH6 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH9 : (task_name_get_target acquired prio tid node )) (PreH10 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH11 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH12 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH13 : (old = (Some (previous)))) (PreH14 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH15 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (critical_region_interval critical sg invocation before acquired )) (PreH18 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH19 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH20 : (UCOS2_state_inv sg acquired )) (PreH21 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH22 : (task_name_get_resolved sg invocation acquired request prio )) (PreH23 : (UCOS2_state_inv sg acquired )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (UCOS2_state_inv sg acquired )) (PreH26 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH27 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH28 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH29 : (critical_region_interval critical sg invocation before acquired )) (PreH30 : (interrupt_saved_value mask cpu_sr )) (PreH31 : (task_name_get_resolved sg invocation acquired request prio )) (PreH32 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (task_name_get_name_frame sg acquired (task_name_get_name (node)) chars )
  **  (task_name_get_private sg invocation request before )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
  **  (task_name_get_name_bytes (task_name_get_name (node)) chars )
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (retval = (task_name_get_length ((task_name_get_name (node))) (chars))) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (task_name_get_target acquired prio tid node ) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (task_name_get_name_bytes (task_name_get_name (node)) chars )
  **  (task_name_get_name_frame sg acquired (task_name_get_name (node)) chars )
  **  (task_name_get_private sg invocation request before )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
.

Definition OSTaskNameGet_partial_solve_wit_25 := OSTaskNameGet_partial_solve_wit_25_pure -> OSTaskNameGet_partial_solve_wit_25_aux.

Definition OSTaskNameGet_partial_solve_wit_26_pure := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (previous: Z) (retval: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH3 : (retval = (task_name_get_length ((task_name_get_name (node))) (chars)))) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH6 : (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH11 : (task_name_get_target acquired prio tid node )) (PreH12 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH13 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH14 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH15 : (old = (Some (previous)))) (PreH16 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (critical_region_interval critical sg invocation before acquired )) (PreH20 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH22 : (UCOS2_state_inv sg acquired )) (PreH23 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH24 : (task_name_get_resolved sg invocation acquired request prio )) (PreH25 : (UCOS2_state_inv sg acquired )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (UCOS2_state_inv sg acquired )) (PreH28 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH29 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH30 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH31 : (critical_region_interval critical sg invocation before acquired )) (PreH32 : (interrupt_saved_value mask cpu_sr )) (PreH33 : (task_name_get_resolved sg invocation acquired request prio )) (PreH34 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
  **  ((( &( "len" ) )) # UChar  |-> retval)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTaskNameGet_partial_solve_wit_26_aux := 
forall (perr_pre: Z) (pname_pre: Z) (X: (TaskNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (prio: Z) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (previous: Z) (retval: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH3 : (retval = (task_name_get_length ((task_name_get_name (node))) (chars)))) (PreH4 : (UCOS2_state_inv sg acquired )) (PreH5 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH6 : (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars )) (PreH7 : (UCOS2_state_inv sg acquired )) (PreH8 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH9 : (UCOS2_state_inv sg acquired )) (PreH10 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH11 : (task_name_get_target acquired prio tid node )) (PreH12 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH13 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH14 : (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars )) (PreH15 : (old = (Some (previous)))) (PreH16 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 1)) (PreH17 : ((task_name_get_table_value (sg) (acquired) (prio)) <> 0)) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (critical_region_interval critical sg invocation before acquired )) (PreH20 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH21 : (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) )) (PreH22 : (UCOS2_state_inv sg acquired )) (PreH23 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH24 : (task_name_get_resolved sg invocation acquired request prio )) (PreH25 : (UCOS2_state_inv sg acquired )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (UCOS2_state_inv sg acquired )) (PreH28 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH29 : ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None)) (PreH30 : (task_name_get_access critical sg invocation before request pname_pre old )) (PreH31 : (critical_region_interval critical sg invocation before acquired )) (PreH32 : (interrupt_saved_value mask cpu_sr )) (PreH33 : (task_name_get_resolved sg invocation acquired request prio )) (PreH34 : (task_name_get_safe critical sg invocation request pname_pre before X )) ,
  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request before )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr_pre) # UChar  |->_)
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (retval = (task_name_get_length ((task_name_get_name (node))) (chars))) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (task_name_get_target acquired prio tid node ) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) (task_name_get_name (node)) chars ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 1) ” 
  &&  “ ((task_name_get_table_value (sg) (acquired) (prio)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio (task_name_get_table_value (sg) (acquired) (prio)) ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ ((task_name_get_early_error (request) (pname_pre) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname_pre old ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (task_name_get_safe critical sg invocation request pname_pre before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request before )
  **  ((perr_pre) # UChar  |->_)
  **  ((pname_pre) # Ptr  |-> (task_name_get_name (node)))
.

Definition OSTaskNameGet_partial_solve_wit_26 := OSTaskNameGet_partial_solve_wit_26_pure -> OSTaskNameGet_partial_solve_wit_26_aux.

Definition OSTaskNameGet_which_implies_wit_1 := 
(
forall (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (perr: Z) (pname: Z) ,
  (task_name_get_pre platform critical sg invocation origin mask before request pname perr old )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request < 256) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname old ) ”
  &&  (task_name_get_closed platform critical sg invocation origin mask before )
  **  ((perr) # UChar  |->_)
  **  (task_name_get_output_cell pname old )
  **  (task_name_get_guarded_private sg invocation request pname before )
) \/
(
forall (old: (@option Z)) (request: Z) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (perr: Z) (pname: Z) ,
  (task_name_get_pre platform critical sg invocation origin mask before request pname perr old )
|--
  EX (x: Z) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= request) ” 
  &&  “ (request < 256) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname old ) ”
  &&  ((perr) # UChar  |-> x)
  **  (task_name_get_closed platform critical sg invocation origin mask before )
  **  (task_name_get_output_cell pname old )
  **  (task_name_get_guarded_private sg invocation request pname before )
).

Definition OSTaskNameGet_which_implies_wit_2 := 
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
) \/
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
).

Definition OSTaskNameGet_which_implies_wit_2_split_goal_spatial := 
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
.

Definition OSTaskNameGet_which_implies_wit_3 := 
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (task_name_get_closed platform critical sg invocation origin mask before )
) \/
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  (task_name_get_closed platform critical sg invocation origin mask before )
).

Definition OSTaskNameGet_which_implies_wit_3_split_goal_spatial := 
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  (task_name_get_closed platform critical sg invocation origin mask before )
.

Definition OSTaskNameGet_which_implies_wit_4 := 
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= (task_name_get_nesting (before))) ” 
  &&  “ ((task_name_get_nesting (before)) < 256) ”
  &&  (task_name_get_closed platform critical sg invocation origin mask before )
) \/
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ ((task_name_get_nesting (before)) < 256) ” 
  &&  “ (0 <= (task_name_get_nesting (before))) ”
  &&  (task_name_get_closed platform critical sg invocation origin mask before )
).

Definition OSTaskNameGet_which_implies_wit_4_split_goal_1 := 
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ ((task_name_get_nesting (before)) < 256) ”
.

Definition OSTaskNameGet_which_implies_wit_4_split_goal_2 := 
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ (0 <= (task_name_get_nesting (before))) ”
.

Definition OSTaskNameGet_which_implies_wit_4_split_goal_spatial := 
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  (task_name_get_closed platform critical sg invocation origin mask before )
.

Definition OSTaskNameGet_which_implies_wit_5 := 
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
) \/
(
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
).

Definition OSTaskNameGet_which_implies_wit_5_split_goal_spatial := 
forall (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (task_name_get_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
.

Definition OSTaskNameGet_which_implies_wit_6 := 
(
forall (old: (@option Z)) (request: Z) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (pname: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (critical_region_interval critical sg invocation before acquired )) (PreH3 : (task_name_get_access critical sg invocation before request pname old )) (PreH4 : ((task_name_get_early_error (request) (pname) ((task_name_get_nesting (before)))) = None)) (PreH5 : (request = 255)) (PreH6 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
|--
  EX (view: TaskNameGetCurrentView)  (priority: Z) ,
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname old ) ” 
  &&  “ ((task_name_get_early_error (request) (pname) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_current_view sg invocation acquired view priority ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_name_get_current_pointer (sg) (view)))
  **  ((&(((task_name_get_current_pointer (sg) (view)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (task_name_get_current_residual sg invocation acquired view )
) \/
(
forall (old: (@option Z)) (request: Z) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (pname: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (critical_region_interval critical sg invocation before acquired )) (PreH3 : (task_name_get_access critical sg invocation before request pname old )) (PreH4 : ((task_name_get_early_error (request) (pname) ((task_name_get_nesting (before)))) = None)) (PreH5 : (request = 255)) (PreH6 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
|--
  EX (view: TaskNameGetCurrentView)  (priority: Z) ,
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ” 
  &&  “ (task_name_get_access critical sg invocation before request pname old ) ” 
  &&  “ ((task_name_get_early_error (request) (pname) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (request = 255) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_current_view sg invocation acquired view priority ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_name_get_current_pointer (sg) (view)))
  **  ((&(((task_name_get_current_pointer (sg) (view)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> priority)
  **  (task_name_get_current_residual sg invocation acquired view )
).

Definition OSTaskNameGet_which_implies_wit_7 := 
(
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (view: TaskNameGetCurrentView) (prio: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (request = 255)) (PreH3 : (task_name_get_current_view sg invocation acquired view prio )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_name_get_current_pointer (sg) (view)))
  **  ((&(((task_name_get_current_pointer (sg) (view)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio)
  **  (task_name_get_current_residual sg invocation acquired view )
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ”
  &&  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
) \/
(
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (view: TaskNameGetCurrentView) (prio: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (request = 255)) (PreH3 : (task_name_get_current_view sg invocation acquired view prio )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_name_get_current_pointer (sg) (view)))
  **  ((&(((task_name_get_current_pointer (sg) (view)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio)
  **  (task_name_get_current_residual sg invocation acquired view )
|--
  “ (task_name_get_resolved sg invocation acquired 255 prio ) ”
  &&  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
).

Definition OSTaskNameGet_which_implies_wit_7_split_goal_1 := 
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (view: TaskNameGetCurrentView) (prio: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (request = 255)) (PreH3 : (task_name_get_current_view sg invocation acquired view prio )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_name_get_current_pointer (sg) (view)))
  **  ((&(((task_name_get_current_pointer (sg) (view)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio)
  **  (task_name_get_current_residual sg invocation acquired view )
|--
  “ (task_name_get_resolved sg invocation acquired 255 prio ) ”
.

Definition OSTaskNameGet_which_implies_wit_7_split_goal_spatial := 
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (view: TaskNameGetCurrentView) (prio: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (request = 255)) (PreH3 : (task_name_get_current_view sg invocation acquired view prio )) (PreH4 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_name_get_current_pointer (sg) (view)))
  **  ((&(((task_name_get_current_pointer (sg) (view)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio)
  **  (task_name_get_current_residual sg invocation acquired view )
|--
  (UCOS2_inv sg acquired )
  **  (task_name_get_private sg invocation request acquired )
.

Definition OSTaskNameGet_which_implies_wit_8 := 
(
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (prio: Z) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (task_name_get_resolved sg invocation acquired request prio )) ,
  (UCOS2_inv sg acquired )
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_resolved sg invocation acquired request prio ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  (task_name_get_table_residual sg acquired prio )
) \/
(
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (prio: Z) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (task_name_get_resolved sg invocation acquired request prio )) ,
  (UCOS2_inv sg acquired )
|--
  “ (UCOS2_state_inv sg acquired ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  (task_name_get_table_residual sg acquired prio )
).

Definition OSTaskNameGet_which_implies_wit_8_split_goal_1 := 
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (prio: Z) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (task_name_get_resolved sg invocation acquired request prio )) ,
  (UCOS2_inv sg acquired )
|--
  “ (UCOS2_state_inv sg acquired ) ”
.

Definition OSTaskNameGet_which_implies_wit_8_split_goal_spatial := 
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (prio: Z) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (task_name_get_resolved sg invocation acquired request prio )) ,
  (UCOS2_inv sg acquired )
|--
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  (task_name_get_table_residual sg acquired prio )
.

Definition OSTaskNameGet_which_implies_wit_9 := 
(
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (task_name_get_resolved sg invocation acquired request prio )) (PreH3 : (ptcb = (task_name_get_table_value (sg) (acquired) (prio)))) (PreH4 : (UCOS2_state_inv sg acquired )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  (task_name_get_table_residual sg acquired prio )
|--
  “ (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio ptcb ) ” 
  &&  “ (UCOS2_state_inv sg acquired ) ”
  &&  (UCOS2_inv sg acquired )
) \/
(
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (task_name_get_resolved sg invocation acquired request prio )) (PreH3 : (ptcb = (task_name_get_table_value (sg) (acquired) (prio)))) (PreH4 : (UCOS2_state_inv sg acquired )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  (task_name_get_table_residual sg acquired prio )
|--
  “ (task_name_get_lookup sg invocation acquired request prio ptcb ) ”
  &&  (UCOS2_inv sg acquired )
).

Definition OSTaskNameGet_which_implies_wit_9_split_goal_1 := 
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (task_name_get_resolved sg invocation acquired request prio )) (PreH3 : (ptcb = (task_name_get_table_value (sg) (acquired) (prio)))) (PreH4 : (UCOS2_state_inv sg acquired )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  (task_name_get_table_residual sg acquired prio )
|--
  “ (task_name_get_lookup sg invocation acquired request prio ptcb ) ”
.

Definition OSTaskNameGet_which_implies_wit_9_split_goal_spatial := 
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (PreH1 : (task_name_get_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH2 : (task_name_get_resolved sg invocation acquired request prio )) (PreH3 : (ptcb = (task_name_get_table_value (sg) (acquired) (prio)))) (PreH4 : (UCOS2_state_inv sg acquired )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_name_get_table_value (sg) (acquired) (prio)))
  **  (task_name_get_table_residual sg acquired prio )
|--
  (UCOS2_inv sg acquired )
.

Definition OSTaskNameGet_which_implies_wit_10 := 
(
forall (request: Z) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (critical_region_interval critical sg invocation before acquired )) ,
  (task_name_get_private sg invocation request acquired )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (critical_region_interval critical sg invocation before acquired ) ”
  &&  (task_name_get_private sg invocation request before )
) \/
(
forall (request: Z) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (critical_region_interval critical sg invocation before acquired )) ,
  (task_name_get_private sg invocation request acquired )
|--
  (task_name_get_private sg invocation request before )
).

Definition OSTaskNameGet_which_implies_wit_10_split_goal_spatial := 
forall (request: Z) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (critical_region_interval critical sg invocation before acquired )) ,
  (task_name_get_private sg invocation request acquired )
|--
  (task_name_get_private sg invocation request before )
.

Definition OSTaskNameGet_which_implies_wit_11 := 
(
forall (old: (@option Z)) (request: Z) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (ptcb: Z) (prio: Z) (pname: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_lookup sg invocation acquired request prio ptcb )) (PreH3 : (ptcb <> 0)) (PreH4 : (ptcb <> 1)) (PreH5 : (task_name_get_access critical sg invocation before request pname old )) (PreH6 : ((task_name_get_early_error (request) (pname) ((task_name_get_nesting (before)))) = None)) (PreH7 : (critical_region_interval critical sg invocation before acquired )) ,
  (UCOS2_inv sg acquired )
  **  (task_name_get_output_cell pname old )
|--
  EX (previous: Z)  (chars: (@list Z))  (tid: Z)  (node: TaskAbstractState) ,
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio ptcb ) ” 
  &&  “ (task_name_get_target acquired prio tid node ) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio ptcb (task_name_get_name (node)) chars ) ” 
  &&  “ (old = (Some (previous))) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (task_name_get_name (node)))
  **  (task_name_get_name_field_residual sg acquired tid node )
  **  ((pname) # Ptr  |-> previous)
) \/
(
forall (old: (@option Z)) (request: Z) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (ptcb: Z) (prio: Z) (pname: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_lookup sg invocation acquired request prio ptcb )) (PreH3 : (ptcb <> 0)) (PreH4 : (ptcb <> 1)) (PreH5 : (task_name_get_access critical sg invocation before request pname old )) (PreH6 : ((task_name_get_early_error (request) (pname) ((task_name_get_nesting (before)))) = None)) (PreH7 : (critical_region_interval critical sg invocation before acquired )) ,
  (UCOS2_inv sg acquired )
  **  (task_name_get_output_cell pname old )
|--
  EX (previous: Z)  (chars: (@list Z))  (tid: Z)  (node: TaskAbstractState) ,
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_lookup sg invocation acquired request prio ptcb ) ” 
  &&  “ (task_name_get_target acquired prio tid node ) ” 
  &&  “ (ptcb <> 0) ” 
  &&  “ (ptcb <> 1) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio ptcb (task_name_get_name (node)) chars ) ” 
  &&  “ (old = (Some (previous))) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (task_name_get_name (node)))
  **  (task_name_get_name_field_residual sg acquired tid node )
  **  ((pname) # Ptr  |-> previous)
).

Definition OSTaskNameGet_which_implies_wit_12 := 
(
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (prio: Z) (ptcb: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_target acquired prio tid node )) (PreH3 : (task_name_get_success sg invocation acquired request prio ptcb (task_name_get_name (node)) chars )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (task_name_get_name (node)))
  **  (task_name_get_name_field_residual sg acquired tid node )
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio ptcb (task_name_get_name (node)) chars ) ”
  &&  (UCOS2_inv sg acquired )
) \/
(
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (prio: Z) (ptcb: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_target acquired prio tid node )) (PreH3 : (task_name_get_success sg invocation acquired request prio ptcb (task_name_get_name (node)) chars )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (task_name_get_name (node)))
  **  (task_name_get_name_field_residual sg acquired tid node )
|--
  (UCOS2_inv sg acquired )
).

Definition OSTaskNameGet_which_implies_wit_12_split_goal_spatial := 
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (chars: (@list Z)) (prio: Z) (ptcb: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_target acquired prio tid node )) (PreH3 : (task_name_get_success sg invocation acquired request prio ptcb (task_name_get_name (node)) chars )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (task_name_get_name (node)))
  **  (task_name_get_name_field_residual sg acquired tid node )
|--
  (UCOS2_inv sg acquired )
.

Definition OSTaskNameGet_which_implies_wit_13 := 
(
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (node: TaskAbstractState) (chars: (@list Z)) (ptcb: Z) (prio: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio ptcb (task_name_get_name (node)) chars )) ,
  (UCOS2_inv sg acquired )
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio ptcb (task_name_get_name (node)) chars ) ” 
  &&  “ (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars ) ”
  &&  (task_name_get_name_bytes (task_name_get_name (node)) chars )
  **  (task_name_get_name_frame sg acquired (task_name_get_name (node)) chars )
) \/
(
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (node: TaskAbstractState) (chars: (@list Z)) (ptcb: Z) (prio: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio ptcb (task_name_get_name (node)) chars )) ,
  (UCOS2_inv sg acquired )
|--
  “ (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars ) ”
  &&  (task_name_get_name_bytes (task_name_get_name (node)) chars )
  **  (task_name_get_name_frame sg acquired (task_name_get_name (node)) chars )
).

Definition OSTaskNameGet_which_implies_wit_13_split_goal_1 := 
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (node: TaskAbstractState) (chars: (@list Z)) (ptcb: Z) (prio: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio ptcb (task_name_get_name (node)) chars )) ,
  (UCOS2_inv sg acquired )
|--
  “ (task_name_get_readable (task_name_get_names (acquired)) (task_name_get_name (node)) chars ) ”
.

Definition OSTaskNameGet_which_implies_wit_13_split_goal_spatial := 
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (node: TaskAbstractState) (chars: (@list Z)) (ptcb: Z) (prio: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio ptcb (task_name_get_name (node)) chars )) ,
  (UCOS2_inv sg acquired )
|--
  (task_name_get_name_bytes (task_name_get_name (node)) chars )
  **  (task_name_get_name_frame sg acquired (task_name_get_name (node)) chars )
.

Definition OSTaskNameGet_which_implies_wit_14 := 
(
forall (request: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (node: TaskAbstractState) (chars: (@list Z)) (cpu_sr: Z) (perr: Z) ,
  (task_name_get_name_frame sg acquired (task_name_get_name (node)) chars )
  **  (task_name_get_private sg invocation request before )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr) # UChar  |->_)
|--
  (task_name_get_call_frame platform critical sg invocation origin cpu_sr before acquired request perr (task_name_get_name (node)) chars )
) \/
(
forall (request: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (node: TaskAbstractState) (chars: (@list Z)) (cpu_sr: Z) (perr: Z) ,
  (task_name_get_name_frame sg acquired (task_name_get_name (node)) chars )
  **  (task_name_get_private sg invocation request before )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr) # UChar  |->_)
|--
  (task_name_get_call_frame platform critical sg invocation origin cpu_sr before acquired request perr (task_name_get_name (node)) chars )
).

Definition OSTaskNameGet_which_implies_wit_14_split_goal_spatial := 
forall (request: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (node: TaskAbstractState) (chars: (@list Z)) (cpu_sr: Z) (perr: Z) ,
  (task_name_get_name_frame sg acquired (task_name_get_name (node)) chars )
  **  (task_name_get_private sg invocation request before )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr) # UChar  |->_)
|--
  (task_name_get_call_frame platform critical sg invocation origin cpu_sr before acquired request perr (task_name_get_name (node)) chars )
.

Definition OSTaskNameGet_which_implies_wit_15 := 
(
forall (request: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (node: TaskAbstractState) (chars: (@list Z)) (perr: Z) (cpu_sr: Z) ,
  (task_name_get_call_frame platform critical sg invocation origin cpu_sr before acquired request perr (task_name_get_name (node)) chars )
|--
  (task_name_get_name_frame sg acquired (task_name_get_name (node)) chars )
  **  (task_name_get_private sg invocation request before )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((perr) # UChar  |->_)
) \/
(
forall (request: Z) (origin: TaskInvocationOrigin) (invocation: nat) (before: UCOS2_Verify_State) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (node: TaskAbstractState) (chars: (@list Z)) (perr: Z) (cpu_sr: Z) ,
  (task_name_get_call_frame platform critical sg invocation origin cpu_sr before acquired request perr (task_name_get_name (node)) chars )
|--
  EX (x: Z) ,
  ((perr) # UChar  |-> x)
  **  (task_name_get_name_frame sg acquired (task_name_get_name (node)) chars )
  **  (task_name_get_private sg invocation request before )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
).

Definition OSTaskNameGet_which_implies_wit_16 := 
(
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (node: TaskAbstractState) (chars: (@list Z)) (ptcb: Z) (prio: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio ptcb (task_name_get_name (node)) chars )) ,
  (task_name_get_name_bytes (task_name_get_name (node)) chars )
  **  (task_name_get_name_frame sg acquired (task_name_get_name (node)) chars )
|--
  “ (UCOS2_state_inv sg acquired ) ” 
  &&  “ (task_name_get_success sg invocation acquired request prio ptcb (task_name_get_name (node)) chars ) ”
  &&  (UCOS2_inv sg acquired )
) \/
(
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (node: TaskAbstractState) (chars: (@list Z)) (ptcb: Z) (prio: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio ptcb (task_name_get_name (node)) chars )) ,
  (task_name_get_name_bytes (task_name_get_name (node)) chars )
  **  (task_name_get_name_frame sg acquired (task_name_get_name (node)) chars )
|--
  (UCOS2_inv sg acquired )
).

Definition OSTaskNameGet_which_implies_wit_16_split_goal_spatial := 
forall (request: Z) (invocation: nat) (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (node: TaskAbstractState) (chars: (@list Z)) (ptcb: Z) (prio: Z) (PreH1 : (UCOS2_state_inv sg acquired )) (PreH2 : (task_name_get_success sg invocation acquired request prio ptcb (task_name_get_name (node)) chars )) ,
  (task_name_get_name_bytes (task_name_get_name (node)) chars )
  **  (task_name_get_name_frame sg acquired (task_name_get_name (node)) chars )
|--
  (UCOS2_inv sg acquired )
.

Definition OS_StrLen_derive_task_name_get_spec_by_exact_frame_spec := 
forall (psrc_pre: Z) (frame_task_name_get_spec: Assertion) (chars_task_name_get_spec: (@list Z)) (names_task_name_get_spec: NameResourceState) (entry_task_name_get_spec: Z) ,
  “ (psrc_pre = entry_task_name_get_spec) ” 
  &&  “ (task_name_get_readable names_task_name_get_spec entry_task_name_get_spec chars_task_name_get_spec ) ”
  &&  (task_name_get_name_bytes entry_task_name_get_spec chars_task_name_get_spec )
  **  (frame_task_name_get_spec )
|--
EX (entry_exact_frame_spec: Z) (base_exact_frame_spec: Z) (names_exact_frame_spec: NameResourceState) (chars_exact_frame_spec: (@list Z)) (frame_exact_frame_spec: Assertion) ,
  ((“ (psrc_pre = entry_exact_frame_spec) ” 
  &&  “ (psrc_pre <> 0) ” 
  &&  “ (psrc_pre = base_exact_frame_spec) ” 
  &&  “ (readable_name names_exact_frame_spec psrc_pre chars_exact_frame_spec ) ”
  &&  (os_strlen_bytes psrc_pre chars_exact_frame_spec )
  **  (frame_exact_frame_spec ))
  ||
  (“ (psrc_pre = entry_exact_frame_spec) ” 
  &&  “ (psrc_pre = 0) ”
  &&  (frame_exact_frame_spec )))
  **
  (((EX retval_2,
  “ (entry_exact_frame_spec = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (frame_exact_frame_spec ))
  ||
  (EX retval_2,
  “ (entry_exact_frame_spec <> 0) ” 
  &&  “ (entry_exact_frame_spec = base_exact_frame_spec) ” 
  &&  “ (os_strlen_result chars_exact_frame_spec retval_2 ) ”
  &&  (os_strlen_bytes entry_exact_frame_spec chars_exact_frame_spec )
  **  (frame_exact_frame_spec )))
  -*
  (EX retval,
  “ (retval = (task_name_get_length (entry_task_name_get_spec) (chars_task_name_get_spec))) ”
  &&  (task_name_get_name_bytes entry_task_name_get_spec chars_task_name_get_spec )
  **  (frame_task_name_get_spec )))
.

Module Type VC_Correct.


Axiom proof_of_OSTaskNameGet_safety_wit_1 : OSTaskNameGet_safety_wit_1.
Axiom proof_of_OSTaskNameGet_safety_wit_2 : OSTaskNameGet_safety_wit_2.
Axiom proof_of_OSTaskNameGet_safety_wit_3 : OSTaskNameGet_safety_wit_3.
Axiom proof_of_OSTaskNameGet_safety_wit_4 : OSTaskNameGet_safety_wit_4.
Axiom proof_of_OSTaskNameGet_safety_wit_5 : OSTaskNameGet_safety_wit_5.
Axiom proof_of_OSTaskNameGet_safety_wit_6 : OSTaskNameGet_safety_wit_6.
Axiom proof_of_OSTaskNameGet_safety_wit_7 : OSTaskNameGet_safety_wit_7.
Axiom proof_of_OSTaskNameGet_safety_wit_8 : OSTaskNameGet_safety_wit_8.
Axiom proof_of_OSTaskNameGet_safety_wit_9 : OSTaskNameGet_safety_wit_9.
Axiom proof_of_OSTaskNameGet_entail_wit_1_1 : OSTaskNameGet_entail_wit_1_1.
Axiom proof_of_OSTaskNameGet_entail_wit_1_2 : OSTaskNameGet_entail_wit_1_2.
Axiom proof_of_OSTaskNameGet_entail_wit_2_1 : OSTaskNameGet_entail_wit_2_1.
Axiom proof_of_OSTaskNameGet_entail_wit_2_2 : OSTaskNameGet_entail_wit_2_2.
Axiom proof_of_OSTaskNameGet_return_wit_1 : OSTaskNameGet_return_wit_1.
Axiom proof_of_OSTaskNameGet_return_wit_2 : OSTaskNameGet_return_wit_2.
Axiom proof_of_OSTaskNameGet_return_wit_3 : OSTaskNameGet_return_wit_3.
Axiom proof_of_OSTaskNameGet_return_wit_4 : OSTaskNameGet_return_wit_4.
Axiom proof_of_OSTaskNameGet_return_wit_5 : OSTaskNameGet_return_wit_5.
Axiom proof_of_OSTaskNameGet_return_wit_6 : OSTaskNameGet_return_wit_6.
Axiom proof_of_OSTaskNameGet_return_wit_7 : OSTaskNameGet_return_wit_7.
Axiom proof_of_OSTaskNameGet_return_wit_8 : OSTaskNameGet_return_wit_8.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_1 : OSTaskNameGet_partial_solve_wit_1.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_2_pure : OSTaskNameGet_partial_solve_wit_2_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_2 : OSTaskNameGet_partial_solve_wit_2.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_3_pure : OSTaskNameGet_partial_solve_wit_3_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_3 : OSTaskNameGet_partial_solve_wit_3.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_4_pure : OSTaskNameGet_partial_solve_wit_4_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_4 : OSTaskNameGet_partial_solve_wit_4.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_5_pure : OSTaskNameGet_partial_solve_wit_5_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_5 : OSTaskNameGet_partial_solve_wit_5.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_6_pure : OSTaskNameGet_partial_solve_wit_6_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_6 : OSTaskNameGet_partial_solve_wit_6.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_7_pure : OSTaskNameGet_partial_solve_wit_7_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_7 : OSTaskNameGet_partial_solve_wit_7.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_8 : OSTaskNameGet_partial_solve_wit_8.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_9 : OSTaskNameGet_partial_solve_wit_9.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_10 : OSTaskNameGet_partial_solve_wit_10.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_11 : OSTaskNameGet_partial_solve_wit_11.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_12_pure : OSTaskNameGet_partial_solve_wit_12_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_12 : OSTaskNameGet_partial_solve_wit_12.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_13_pure : OSTaskNameGet_partial_solve_wit_13_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_13 : OSTaskNameGet_partial_solve_wit_13.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_14_pure : OSTaskNameGet_partial_solve_wit_14_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_14 : OSTaskNameGet_partial_solve_wit_14.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_15_pure : OSTaskNameGet_partial_solve_wit_15_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_15 : OSTaskNameGet_partial_solve_wit_15.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_16_pure : OSTaskNameGet_partial_solve_wit_16_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_16 : OSTaskNameGet_partial_solve_wit_16.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_17_pure : OSTaskNameGet_partial_solve_wit_17_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_17 : OSTaskNameGet_partial_solve_wit_17.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_18_pure : OSTaskNameGet_partial_solve_wit_18_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_18 : OSTaskNameGet_partial_solve_wit_18.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_19_pure : OSTaskNameGet_partial_solve_wit_19_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_19 : OSTaskNameGet_partial_solve_wit_19.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_20_pure : OSTaskNameGet_partial_solve_wit_20_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_20 : OSTaskNameGet_partial_solve_wit_20.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_21_pure : OSTaskNameGet_partial_solve_wit_21_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_21 : OSTaskNameGet_partial_solve_wit_21.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_22 : OSTaskNameGet_partial_solve_wit_22.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_23_pure : OSTaskNameGet_partial_solve_wit_23_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_23 : OSTaskNameGet_partial_solve_wit_23.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_24 : OSTaskNameGet_partial_solve_wit_24.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_25_pure : OSTaskNameGet_partial_solve_wit_25_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_25 : OSTaskNameGet_partial_solve_wit_25.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_26_pure : OSTaskNameGet_partial_solve_wit_26_pure.
Axiom proof_of_OSTaskNameGet_partial_solve_wit_26 : OSTaskNameGet_partial_solve_wit_26.
Axiom proof_of_OSTaskNameGet_which_implies_wit_1 : OSTaskNameGet_which_implies_wit_1.
Axiom proof_of_OSTaskNameGet_which_implies_wit_2 : OSTaskNameGet_which_implies_wit_2.
Axiom proof_of_OSTaskNameGet_which_implies_wit_3 : OSTaskNameGet_which_implies_wit_3.
Axiom proof_of_OSTaskNameGet_which_implies_wit_4 : OSTaskNameGet_which_implies_wit_4.
Axiom proof_of_OSTaskNameGet_which_implies_wit_5 : OSTaskNameGet_which_implies_wit_5.
Axiom proof_of_OSTaskNameGet_which_implies_wit_6 : OSTaskNameGet_which_implies_wit_6.
Axiom proof_of_OSTaskNameGet_which_implies_wit_7 : OSTaskNameGet_which_implies_wit_7.
Axiom proof_of_OSTaskNameGet_which_implies_wit_8 : OSTaskNameGet_which_implies_wit_8.
Axiom proof_of_OSTaskNameGet_which_implies_wit_9 : OSTaskNameGet_which_implies_wit_9.
Axiom proof_of_OSTaskNameGet_which_implies_wit_10 : OSTaskNameGet_which_implies_wit_10.
Axiom proof_of_OSTaskNameGet_which_implies_wit_11 : OSTaskNameGet_which_implies_wit_11.
Axiom proof_of_OSTaskNameGet_which_implies_wit_12 : OSTaskNameGet_which_implies_wit_12.
Axiom proof_of_OSTaskNameGet_which_implies_wit_13 : OSTaskNameGet_which_implies_wit_13.
Axiom proof_of_OSTaskNameGet_which_implies_wit_14 : OSTaskNameGet_which_implies_wit_14.
Axiom proof_of_OSTaskNameGet_which_implies_wit_15 : OSTaskNameGet_which_implies_wit_15.
Axiom proof_of_OSTaskNameGet_which_implies_wit_16 : OSTaskNameGet_which_implies_wit_16.
Axiom proof_of_OS_StrLen_derive_task_name_get_spec_by_exact_frame_spec : OS_StrLen_derive_task_name_get_spec_by_exact_frame_spec.

End VC_Correct.
