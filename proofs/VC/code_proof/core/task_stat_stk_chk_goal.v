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
Require Import Ucos2Verify.VC.code.core.spec.task_stat_stk_chk_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_TaskStatStkChk -----*)

Definition OS_TaskStatStkChk_safety_wit_1 := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH5 : (( &( "stk_data" ) ) <> 0)) (PreH6 : (0 <= prio)) (PreH7 : (prio <= 64)) (PreH8 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH9 : (UCOS2_state_inv sg current )) (PreH10 : (( &( "stk_data" ) ) <> 0)) (PreH11 : (task_stat_stk_chk_configuration sg )) (PreH12 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH13 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH14 : (UCOS2_state_inv sg before )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation current )
  **  (caller )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
  **  ((( &( "err" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition OS_TaskStatStkChk_safety_wit_2 := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (err: Z) (after: UCOS2_Verify_State) (data: (@option TaskStackCheckData)) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = (task_stk_chk_table_pointer (sg) (after) (prio)))) (PreH6 : (UCOS2_state_inv sg after )) (PreH7 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (0 <= prio)) (PreH9 : (prio < 64)) (PreH10 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (task_stat_stk_chk_configuration sg )) (PreH13 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH15 : (( &( "stk_data" ) ) <> 0)) (PreH16 : (0 <= prio)) (PreH17 : (prio < 64)) (PreH18 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH19 : (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) err data after )) (PreH20 : (UCOS2_state_inv sg after )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (critical_region_outside critical sg invocation after )
  **  ((( &( "err" ) )) # UChar  |-> err)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TaskStatStkChk_safety_wit_3 := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (err: Z) (after: UCOS2_Verify_State) (data: (@option TaskStackCheckData)) (PreH1 : ((task_stk_chk_table_pointer (sg) (after) (prio)) <> 0)) (PreH2 : (UCOS2_state_inv sg after )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (0 <= prio)) (PreH5 : (prio < 64)) (PreH6 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = (task_stk_chk_table_pointer (sg) (after) (prio)))) (PreH7 : (UCOS2_state_inv sg after )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (0 <= prio)) (PreH10 : (prio < 64)) (PreH11 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (task_stat_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH16 : (( &( "stk_data" ) ) <> 0)) (PreH17 : (0 <= prio)) (PreH18 : (prio < 64)) (PreH19 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH20 : (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) err data after )) (PreH21 : (UCOS2_state_inv sg after )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (critical_region_outside critical sg invocation after )
  **  ((( &( "err" ) )) # UChar  |-> err)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OS_TaskStatStkChk_entail_wit_1 := 
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (( &( "stk_data" ) ) <> 0)) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH5 : (UCOS2_state_inv sg before )) ,
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
|--
  EX (current: UCOS2_Verify_State)  (history: TaskStatStkChkHistory) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before 0 current history ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation current )
  **  (caller )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
) \/
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (( &( "stk_data" ) ) <> 0)) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH5 : (UCOS2_state_inv sg before )) ,
  TT && emp 
|--
  EX (history: TaskStatStkChkHistory) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before 0 before history ) ”
  &&  emp
).

Definition OS_TaskStatStkChk_entail_wit_2 := 
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (prio: Z) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (error: Z) (data_2: (@option TaskStackCheckData)) (after_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stk_chk_post critical sg invocation mask current caller prio ( &( "stk_data" ) ) error data_2 after_2 (task_stat_stk_chk_observe_call (critical) (sg) (invocation) (current) (caller) (prio) (( &( "stk_data" ) ))) )) (PreH2 : (retval = error)) (PreH3 : (UCOS2_state_inv sg after_2 )) (PreH4 : (task_stat_stk_chk_configuration sg )) (PreH5 : (task_stk_chk_configuration sg )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio < 64)) (PreH9 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH10 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH11 : (task_stk_chk_admission critical sg invocation current caller prio ( &( "stk_data" ) ) )) (PreH12 : (task_stk_chk_safe critical sg invocation current caller prio ( &( "stk_data" ) ) (task_stat_stk_chk_observe_call (critical) (sg) (invocation) (current) (caller) (prio) (( &( "stk_data" ) ))) )) (PreH13 : (prio <= 63)) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (task_stat_stk_chk_configuration sg )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH18 : (( &( "stk_data" ) ) <> 0)) (PreH19 : (0 <= prio)) (PreH20 : (prio <= 64)) (PreH21 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH22 : (UCOS2_state_inv sg current )) (PreH23 : (( &( "stk_data" ) ) <> 0)) (PreH24 : (task_stat_stk_chk_configuration sg )) (PreH25 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH26 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH27 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after_2 )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data_2 )
|--
  EX (data: (@option TaskStackCheckData))  (after: UCOS2_Verify_State) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history ) ” 
  &&  “ (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) retval data after ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
) \/
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (prio: Z) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (error: Z) (data_2: (@option TaskStackCheckData)) (after_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stk_chk_post critical sg invocation mask current caller prio ( &( "stk_data" ) ) error data_2 after_2 (task_stat_stk_chk_observe_call (critical) (sg) (invocation) (current) (caller) (prio) (( &( "stk_data" ) ))) )) (PreH2 : (retval = error)) (PreH3 : (UCOS2_state_inv sg after_2 )) (PreH4 : (task_stat_stk_chk_configuration sg )) (PreH5 : (task_stk_chk_configuration sg )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio < 64)) (PreH9 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH10 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH11 : (task_stk_chk_admission critical sg invocation current caller prio ( &( "stk_data" ) ) )) (PreH12 : (task_stk_chk_safe critical sg invocation current caller prio ( &( "stk_data" ) ) (task_stat_stk_chk_observe_call (critical) (sg) (invocation) (current) (caller) (prio) (( &( "stk_data" ) ))) )) (PreH13 : (prio <= 63)) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (task_stat_stk_chk_configuration sg )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH18 : (( &( "stk_data" ) ) <> 0)) (PreH19 : (0 <= prio)) (PreH20 : (prio <= 64)) (PreH21 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH22 : (UCOS2_state_inv sg current )) (PreH23 : (( &( "stk_data" ) ) <> 0)) (PreH24 : (task_stat_stk_chk_configuration sg )) (PreH25 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH26 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH27 : (UCOS2_state_inv sg before )) ,
  TT && emp 
|--
  “ (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) error data_2 after_2 ) ”
  &&  emp
).

Definition OS_TaskStatStkChk_entail_wit_2_split_goal_1 := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (prio: Z) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (error: Z) (data_2: (@option TaskStackCheckData)) (after_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (task_stk_chk_post critical sg invocation mask current caller prio ( &( "stk_data" ) ) error data_2 after_2 (task_stat_stk_chk_observe_call (critical) (sg) (invocation) (current) (caller) (prio) (( &( "stk_data" ) ))) )) (PreH2 : (retval = error)) (PreH3 : (UCOS2_state_inv sg after_2 )) (PreH4 : (task_stat_stk_chk_configuration sg )) (PreH5 : (task_stk_chk_configuration sg )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio < 64)) (PreH9 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH10 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH11 : (task_stk_chk_admission critical sg invocation current caller prio ( &( "stk_data" ) ) )) (PreH12 : (task_stk_chk_safe critical sg invocation current caller prio ( &( "stk_data" ) ) (task_stat_stk_chk_observe_call (critical) (sg) (invocation) (current) (caller) (prio) (( &( "stk_data" ) ))) )) (PreH13 : (prio <= 63)) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (task_stat_stk_chk_configuration sg )) (PreH16 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH17 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH18 : (( &( "stk_data" ) ) <> 0)) (PreH19 : (0 <= prio)) (PreH20 : (prio <= 64)) (PreH21 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH22 : (UCOS2_state_inv sg current )) (PreH23 : (( &( "stk_data" ) ) <> 0)) (PreH24 : (task_stat_stk_chk_configuration sg )) (PreH25 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH26 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH27 : (UCOS2_state_inv sg before )) ,
  (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) error data_2 after_2 )
.

Definition OS_TaskStatStkChk_entail_wit_3_1 := 
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (err: Z) (after: UCOS2_Verify_State) (data: (@option TaskStackCheckData)) (PreH1 : ((task_stk_chk_table_pointer (sg) (after) (prio)) <> 1)) (PreH2 : ((task_stk_chk_table_pointer (sg) (after) (prio)) <> 0)) (PreH3 : (UCOS2_state_inv sg after )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (0 <= prio)) (PreH6 : (prio < 64)) (PreH7 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = (task_stk_chk_table_pointer (sg) (after) (prio)))) (PreH8 : (UCOS2_state_inv sg after )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (0 <= prio)) (PreH11 : (prio < 64)) (PreH12 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (task_stat_stk_chk_configuration sg )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH17 : (( &( "stk_data" ) ) <> 0)) (PreH18 : (0 <= prio)) (PreH19 : (prio < 64)) (PreH20 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH21 : (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) err data after )) (PreH22 : (UCOS2_state_inv sg after )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (critical_region_outside critical sg invocation after )
  **  ((( &( "err" ) )) # UChar  |-> err)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  EX (next_history: TaskStatStkChkHistory) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before (prio + 1 ) after next_history ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "err" ) )) # UChar  |->_)
) \/
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (err: Z) (after: UCOS2_Verify_State) (data: (@option TaskStackCheckData)) (PreH1 : ((task_stk_chk_table_pointer (sg) (after) (prio)) <> 1)) (PreH2 : ((task_stk_chk_table_pointer (sg) (after) (prio)) <> 0)) (PreH3 : (UCOS2_state_inv sg after )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (0 <= prio)) (PreH6 : (prio < 64)) (PreH7 : (UCOS2_state_inv sg after )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (0 <= prio)) (PreH10 : (prio < 64)) (PreH11 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (task_stat_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH16 : (( &( "stk_data" ) ) <> 0)) (PreH17 : (0 <= prio)) (PreH18 : (prio < 64)) (PreH19 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH20 : (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) err data after )) (PreH21 : (UCOS2_state_inv sg after )) ,
  (critical_region_outside critical sg invocation after )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  EX (next_history: TaskStatStkChkHistory) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before (prio + 1 ) after next_history ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
).

Definition OS_TaskStatStkChk_entail_wit_3_2 := 
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (err: Z) (after: UCOS2_Verify_State) (data: (@option TaskStackCheckData)) (PreH1 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = 1)) (PreH2 : ((task_stk_chk_table_pointer (sg) (after) (prio)) <> 0)) (PreH3 : (UCOS2_state_inv sg after )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (0 <= prio)) (PreH6 : (prio < 64)) (PreH7 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = (task_stk_chk_table_pointer (sg) (after) (prio)))) (PreH8 : (UCOS2_state_inv sg after )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (0 <= prio)) (PreH11 : (prio < 64)) (PreH12 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (task_stat_stk_chk_configuration sg )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH17 : (( &( "stk_data" ) ) <> 0)) (PreH18 : (0 <= prio)) (PreH19 : (prio < 64)) (PreH20 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH21 : (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) err data after )) (PreH22 : (UCOS2_state_inv sg after )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (critical_region_outside critical sg invocation after )
  **  ((( &( "err" ) )) # UChar  |-> err)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  EX (next_history: TaskStatStkChkHistory) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before (prio + 1 ) after next_history ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "err" ) )) # UChar  |->_)
) \/
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (err: Z) (after: UCOS2_Verify_State) (data: (@option TaskStackCheckData)) (PreH1 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = 1)) (PreH2 : ((task_stk_chk_table_pointer (sg) (after) (prio)) <> 0)) (PreH3 : (UCOS2_state_inv sg after )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (0 <= prio)) (PreH6 : (prio < 64)) (PreH7 : (UCOS2_state_inv sg after )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (0 <= prio)) (PreH10 : (prio < 64)) (PreH11 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (task_stat_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH16 : (( &( "stk_data" ) ) <> 0)) (PreH17 : (0 <= prio)) (PreH18 : (prio < 64)) (PreH19 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH20 : (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) err data after )) (PreH21 : (UCOS2_state_inv sg after )) ,
  (critical_region_outside critical sg invocation after )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  EX (next_history: TaskStatStkChkHistory) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before (prio + 1 ) after next_history ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
).

Definition OS_TaskStatStkChk_entail_wit_3_3 := 
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (err: Z) (after: UCOS2_Verify_State) (data: (@option TaskStackCheckData)) (PreH1 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = 0)) (PreH2 : (UCOS2_state_inv sg after )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (0 <= prio)) (PreH5 : (prio < 64)) (PreH6 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = (task_stk_chk_table_pointer (sg) (after) (prio)))) (PreH7 : (UCOS2_state_inv sg after )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (0 <= prio)) (PreH10 : (prio < 64)) (PreH11 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (task_stat_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH16 : (( &( "stk_data" ) ) <> 0)) (PreH17 : (0 <= prio)) (PreH18 : (prio < 64)) (PreH19 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH20 : (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) err data after )) (PreH21 : (UCOS2_state_inv sg after )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (critical_region_outside critical sg invocation after )
  **  ((( &( "err" ) )) # UChar  |-> err)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  EX (next_history: TaskStatStkChkHistory) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before (prio + 1 ) after next_history ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "err" ) )) # UChar  |->_)
) \/
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (err: Z) (after: UCOS2_Verify_State) (data: (@option TaskStackCheckData)) (PreH1 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = 0)) (PreH2 : (UCOS2_state_inv sg after )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (0 <= prio)) (PreH5 : (prio < 64)) (PreH6 : (UCOS2_state_inv sg after )) (PreH7 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (0 <= prio)) (PreH9 : (prio < 64)) (PreH10 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (task_stat_stk_chk_configuration sg )) (PreH13 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH15 : (( &( "stk_data" ) ) <> 0)) (PreH16 : (0 <= prio)) (PreH17 : (prio < 64)) (PreH18 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH19 : (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) err data after )) (PreH20 : (UCOS2_state_inv sg after )) ,
  (critical_region_outside critical sg invocation after )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  EX (next_history: TaskStatStkChkHistory) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before (prio + 1 ) after next_history ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
).

Definition OS_TaskStatStkChk_entail_wit_3_4 := 
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (err: Z) (after: UCOS2_Verify_State) (data: (@option TaskStackCheckData)) (PreH1 : ((unsigned_last_nbits (err) (32)) <> 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio < 64)) (PreH9 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH10 : (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) err data after )) (PreH11 : (UCOS2_state_inv sg after )) ,
  ((( &( "err" ) )) # UChar  |-> err)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  EX (next_history: TaskStatStkChkHistory) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before (prio + 1 ) after next_history ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
  **  ((( &( "err" ) )) # UChar  |->_)
) \/
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (err: Z) (after: UCOS2_Verify_State) (data: (@option TaskStackCheckData)) (PreH1 : ((unsigned_last_nbits (err) (32)) <> 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio < 64)) (PreH9 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH10 : (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) err data after )) (PreH11 : (UCOS2_state_inv sg after )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  EX (next_history: TaskStatStkChkHistory) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before (prio + 1 ) after next_history ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
).

Definition OS_TaskStatStkChk_entail_wit_4 := 
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (after: UCOS2_Verify_State) (next_history: TaskStatStkChkHistory) (prio: Z) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH5 : (( &( "stk_data" ) ) <> 0)) (PreH6 : (0 <= prio)) (PreH7 : (prio < 64)) (PreH8 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before (prio + 1 ) after next_history )) (PreH9 : (UCOS2_state_inv sg after )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  EX (current: UCOS2_Verify_State)  (history: TaskStatStkChkHistory) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= (prio + 1 )) ” 
  &&  “ ((prio + 1 ) <= 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before (prio + 1 ) current history ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation current )
  **  (caller )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
) \/
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (after: UCOS2_Verify_State) (next_history: TaskStatStkChkHistory) (prio: Z) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH5 : (( &( "stk_data" ) ) <> 0)) (PreH6 : (0 <= prio)) (PreH7 : (prio < 64)) (PreH8 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before (prio + 1 ) after next_history )) (PreH9 : (UCOS2_state_inv sg after )) ,
  TT && emp 
|--
  TT && emp 
).

Definition OS_TaskStatStkChk_return_wit_1 := 
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (prio: Z) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (PreH1 : (prio > 63)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio <= 64)) (PreH9 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH10 : (UCOS2_state_inv sg current )) (PreH11 : (( &( "stk_data" ) ) <> 0)) (PreH12 : (task_stat_stk_chk_configuration sg )) (PreH13 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH15 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation current )
  **  (caller )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (task_stat_stk_chk_post critical sg invocation mask caller before after ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
) \/
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (prio: Z) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (PreH1 : (prio > 63)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio <= 64)) (PreH9 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH10 : (UCOS2_state_inv sg current )) (PreH11 : (( &( "stk_data" ) ) <> 0)) (PreH12 : (task_stat_stk_chk_configuration sg )) (PreH13 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH15 : (UCOS2_state_inv sg before )) ,
  TT && emp 
|--
  “ (task_stat_stk_chk_post critical sg invocation mask caller before current ) ”
  &&  emp
).

Definition OS_TaskStatStkChk_return_wit_1_split_goal_1 := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (prio: Z) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (PreH1 : (prio > 63)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio <= 64)) (PreH9 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH10 : (UCOS2_state_inv sg current )) (PreH11 : (( &( "stk_data" ) ) <> 0)) (PreH12 : (task_stat_stk_chk_configuration sg )) (PreH13 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH15 : (UCOS2_state_inv sg before )) ,
  (task_stat_stk_chk_post critical sg invocation mask caller before current )
.

Definition OS_TaskStatStkChk_partial_solve_wit_1 := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH4 : (UCOS2_state_inv sg before )) ,
  (UndefStructPredos_stk_data ( &( "stk_data" ) ) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
|--
  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
  &&  ((&(( &( "stk_data" ) )->ₛ "OSFree")) # UInt  |->_)
  **  ((&(( &( "stk_data" ) )->ₛ "OSUsed")) # UInt  |->_)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (caller )
.

Definition OS_TaskStatStkChk_partial_solve_wit_2_pure := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (prio: Z) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (PreH1 : (prio <= 63)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio <= 64)) (PreH9 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH10 : (UCOS2_state_inv sg current )) (PreH11 : (( &( "stk_data" ) ) <> 0)) (PreH12 : (task_stat_stk_chk_configuration sg )) (PreH13 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH15 : (UCOS2_state_inv sg before )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation current )
  **  (caller )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
  **  ((( &( "err" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history ) ”
.

Definition OS_TaskStatStkChk_partial_solve_wit_2_aux := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (prio: Z) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (PreH1 : (prio <= 63)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio <= 64)) (PreH9 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH10 : (UCOS2_state_inv sg current )) (PreH11 : (( &( "stk_data" ) ) <> 0)) (PreH12 : (task_stat_stk_chk_configuration sg )) (PreH13 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH15 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation current )
  **  (caller )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history ) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
  &&  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation current )
  **  (caller )
.

Definition OS_TaskStatStkChk_partial_solve_wit_2 := OS_TaskStatStkChk_partial_solve_wit_2_pure -> OS_TaskStatStkChk_partial_solve_wit_2_aux.

Definition OS_TaskStatStkChk_partial_solve_wit_3_pure := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (prio: Z) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (( &( "stk_data" ) ) <> 0)) (PreH4 : (0 <= prio)) (PreH5 : (prio < 64)) (PreH6 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH7 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH8 : (task_stk_chk_admission critical sg invocation current caller prio ( &( "stk_data" ) ) )) (PreH9 : (task_stk_chk_safe critical sg invocation current caller prio ( &( "stk_data" ) ) (task_stat_stk_chk_observe_call (critical) (sg) (invocation) (current) (caller) (prio) (( &( "stk_data" ) ))) )) (PreH10 : (prio <= 63)) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (task_stat_stk_chk_configuration sg )) (PreH13 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH15 : (( &( "stk_data" ) ) <> 0)) (PreH16 : (0 <= prio)) (PreH17 : (prio <= 64)) (PreH18 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (( &( "stk_data" ) ) <> 0)) (PreH21 : (task_stat_stk_chk_configuration sg )) (PreH22 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH23 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH24 : (UCOS2_state_inv sg before )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (task_stk_chk_output_pre sg prio ( &( "stk_data" ) ) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation current )
  **  (caller )
  **  ((( &( "err" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (0 <= prio) ” 
  &&  “ (prio <= 255) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation current caller prio ( &( "stk_data" ) ) ) ” 
  &&  “ (task_stk_chk_safe critical sg invocation current caller prio ( &( "stk_data" ) ) (task_stat_stk_chk_observe_call (critical) (sg) (invocation) (current) (caller) (prio) (( &( "stk_data" ) ))) ) ”
.

Definition OS_TaskStatStkChk_partial_solve_wit_3_aux := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (prio: Z) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (( &( "stk_data" ) ) <> 0)) (PreH4 : (0 <= prio)) (PreH5 : (prio < 64)) (PreH6 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH7 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH8 : (task_stk_chk_admission critical sg invocation current caller prio ( &( "stk_data" ) ) )) (PreH9 : (task_stk_chk_safe critical sg invocation current caller prio ( &( "stk_data" ) ) (task_stat_stk_chk_observe_call (critical) (sg) (invocation) (current) (caller) (prio) (( &( "stk_data" ) ))) )) (PreH10 : (prio <= 63)) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (task_stat_stk_chk_configuration sg )) (PreH13 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH15 : (( &( "stk_data" ) ) <> 0)) (PreH16 : (0 <= prio)) (PreH17 : (prio <= 64)) (PreH18 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (( &( "stk_data" ) ) <> 0)) (PreH21 : (task_stat_stk_chk_configuration sg )) (PreH22 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH23 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH24 : (UCOS2_state_inv sg before )) ,
  (task_stk_chk_output_pre sg prio ( &( "stk_data" ) ) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation current )
  **  (caller )
|--
  “ (0 <= prio) ” 
  &&  “ (prio <= 255) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation current caller prio ( &( "stk_data" ) ) ) ” 
  &&  “ (task_stk_chk_safe critical sg invocation current caller prio ( &( "stk_data" ) ) (task_stat_stk_chk_observe_call (critical) (sg) (invocation) (current) (caller) (prio) (( &( "stk_data" ) ))) ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation current caller prio ( &( "stk_data" ) ) ) ” 
  &&  “ (task_stk_chk_safe critical sg invocation current caller prio ( &( "stk_data" ) ) (task_stat_stk_chk_observe_call (critical) (sg) (invocation) (current) (caller) (prio) (( &( "stk_data" ) ))) ) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation current )
  **  (caller )
  **  (task_stk_chk_output_pre sg prio ( &( "stk_data" ) ) )
.

Definition OS_TaskStatStkChk_partial_solve_wit_3 := OS_TaskStatStkChk_partial_solve_wit_3_pure -> OS_TaskStatStkChk_partial_solve_wit_3_aux.

Definition OS_TaskStatStkChk_partial_solve_wit_4_pure := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (err: Z) (after: UCOS2_Verify_State) (data: (@option TaskStackCheckData)) (PreH1 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio < 64)) (PreH9 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH10 : (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) err data after )) (PreH11 : (UCOS2_state_inv sg after )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "err" ) )) # UChar  |-> err)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (UCOS2_state_inv sg after ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ”
.

Definition OS_TaskStatStkChk_partial_solve_wit_4_aux := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (err: Z) (after: UCOS2_Verify_State) (data: (@option TaskStackCheckData)) (PreH1 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio < 64)) (PreH9 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH10 : (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) err data after )) (PreH11 : (UCOS2_state_inv sg after )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation after )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  “ (UCOS2_state_inv sg after ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ ((unsigned_last_nbits (err) (32)) = 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history ) ” 
  &&  “ (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) err data after ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (critical_region_outside critical sg invocation after )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
.

Definition OS_TaskStatStkChk_partial_solve_wit_4 := OS_TaskStatStkChk_partial_solve_wit_4_pure -> OS_TaskStatStkChk_partial_solve_wit_4_aux.

Definition OS_TaskStatStkChk_partial_solve_wit_5_pure := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (err: Z) (after: UCOS2_Verify_State) (data: (@option TaskStackCheckData)) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (task_stat_stk_chk_configuration sg )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH10 : (( &( "stk_data" ) ) <> 0)) (PreH11 : (0 <= prio)) (PreH12 : (prio < 64)) (PreH13 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH14 : (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) err data after )) (PreH15 : (UCOS2_state_inv sg after )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stk_chk_table_frame sg after prio )
  **  ((( &( "err" ) )) # UChar  |-> err)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
|--
  “ (UCOS2_state_inv sg after ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (after) (prio)) = (task_stk_chk_table_pointer (sg) (after) (prio))) ”
.

Definition OS_TaskStatStkChk_partial_solve_wit_5_aux := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (err: Z) (after: UCOS2_Verify_State) (data: (@option TaskStackCheckData)) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (task_stat_stk_chk_configuration sg )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH10 : (( &( "stk_data" ) ) <> 0)) (PreH11 : (0 <= prio)) (PreH12 : (prio < 64)) (PreH13 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH14 : (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) err data after )) (PreH15 : (UCOS2_state_inv sg after )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stk_chk_table_frame sg after prio )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  “ (UCOS2_state_inv sg after ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ ((task_stk_chk_table_pointer (sg) (after) (prio)) = (task_stk_chk_table_pointer (sg) (after) (prio))) ” 
  &&  “ (UCOS2_state_inv sg after ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ ((unsigned_last_nbits (err) (32)) = 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history ) ” 
  &&  “ (task_stat_stk_chk_call_result critical sg invocation mask current caller prio ( &( "stk_data" ) ) err data after ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stk_chk_table_frame sg after prio )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (caller )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
.

Definition OS_TaskStatStkChk_partial_solve_wit_5 := OS_TaskStatStkChk_partial_solve_wit_5_pure -> OS_TaskStatStkChk_partial_solve_wit_5_aux.

Definition OS_TaskStatStkChk_partial_solve_wit_6 := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (prio: Z) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (PreH1 : (prio > 63)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio <= 64)) (PreH9 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) (PreH10 : (UCOS2_state_inv sg current )) (PreH11 : (( &( "stk_data" ) ) <> 0)) (PreH12 : (task_stat_stk_chk_configuration sg )) (PreH13 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH15 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation current )
  **  (caller )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  “ (prio > 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 64) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
  &&  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation current )
  **  (caller )
.

Definition OS_TaskStatStkChk_which_implies_wit_1 := 
(
  ((&(( &( "stk_data" ) )->ₛ "OSFree")) # UInt  |->_)
  **  ((&(( &( "stk_data" ) )->ₛ "OSUsed")) # UInt  |->_)
|--
  “ (( &( "stk_data" ) ) <> 0) ”
  &&  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
) \/
(
  ((&(( &( "stk_data" ) )->ₛ "OSFree")) # UInt  |->_)
  **  ((&(( &( "stk_data" ) )->ₛ "OSUsed")) # UInt  |->_)
|--
  “ (( &( "stk_data" ) ) <> 0) ”
  &&  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
).

Definition OS_TaskStatStkChk_which_implies_wit_1_split_goal_1 := 
  ((&(( &( "stk_data" ) )->ₛ "OSFree")) # UInt  |->_)
  **  ((&(( &( "stk_data" ) )->ₛ "OSUsed")) # UInt  |->_)
|--
  “ (( &( "stk_data" ) ) <> 0) ”
.

Definition OS_TaskStatStkChk_which_implies_wit_1_split_goal_spatial := 
  ((&(( &( "stk_data" ) )->ₛ "OSFree")) # UInt  |->_)
  **  ((&(( &( "stk_data" ) )->ₛ "OSUsed")) # UInt  |->_)
|--
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
.

Definition OS_TaskStatStkChk_which_implies_wit_2 := 
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (( &( "stk_data" ) ) <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH6 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) ,
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_protocol critical sg invocation mask caller before ) ” 
  &&  “ (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation current caller prio ( &( "stk_data" ) ) ) ” 
  &&  “ (task_stk_chk_safe critical sg invocation current caller prio ( &( "stk_data" ) ) (task_stat_stk_chk_observe_call (critical) (sg) (invocation) (current) (caller) (prio) (( &( "stk_data" ) ))) ) ”
  &&  (task_stk_chk_output_pre sg prio ( &( "stk_data" ) ) )
) \/
(
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (( &( "stk_data" ) ) <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH6 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) ,
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  “ (task_stk_chk_safe critical sg invocation current caller prio ( &( "stk_data" ) ) (task_stat_stk_chk_observe_call (critical) (sg) (invocation) (current) (caller) (prio) (( &( "stk_data" ) ))) ) ” 
  &&  “ (task_stk_chk_admission critical sg invocation current caller prio ( &( "stk_data" ) ) ) ” 
  &&  “ (task_stk_chk_configuration sg ) ”
  &&  (task_stk_chk_output_pre sg prio ( &( "stk_data" ) ) )
).

Definition OS_TaskStatStkChk_which_implies_wit_2_split_goal_1 := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (( &( "stk_data" ) ) <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH6 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) ,
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  “ (task_stk_chk_safe critical sg invocation current caller prio ( &( "stk_data" ) ) (task_stat_stk_chk_observe_call (critical) (sg) (invocation) (current) (caller) (prio) (( &( "stk_data" ) ))) ) ”
.

Definition OS_TaskStatStkChk_which_implies_wit_2_split_goal_2 := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (( &( "stk_data" ) ) <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH6 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) ,
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  “ (task_stk_chk_admission critical sg invocation current caller prio ( &( "stk_data" ) ) ) ”
.

Definition OS_TaskStatStkChk_which_implies_wit_2_split_goal_3 := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (( &( "stk_data" ) ) <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH6 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) ,
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  “ (task_stk_chk_configuration sg ) ”
.

Definition OS_TaskStatStkChk_which_implies_wit_2_split_goal_spatial := 
forall (caller: Assertion) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (current: UCOS2_Verify_State) (history: TaskStatStkChkHistory) (prio: Z) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (( &( "stk_data" ) ) <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (task_stat_stk_chk_protocol critical sg invocation mask caller before )) (PreH6 : (task_stat_stk_chk_prefix critical sg invocation mask caller ( &( "stk_data" ) ) before prio current history )) ,
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  (task_stk_chk_output_pre sg prio ( &( "stk_data" ) ) )
.

Definition OS_TaskStatStkChk_which_implies_wit_3 := 
(
forall (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (after: UCOS2_Verify_State) (prio: Z) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) ,
  (critical_region_outside critical sg invocation after )
|--
  “ (UCOS2_state_inv sg after ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stk_chk_table_frame sg after prio )
) \/
(
forall (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (after: UCOS2_Verify_State) (prio: Z) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) ,
  (critical_region_outside critical sg invocation after )
|--
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stk_chk_table_frame sg after prio )
).

Definition OS_TaskStatStkChk_which_implies_wit_3_split_goal_spatial := 
forall (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (after: UCOS2_Verify_State) (prio: Z) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) ,
  (critical_region_outside critical sg invocation after )
|--
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stk_chk_table_frame sg after prio )
.

Definition OS_TaskStatStkChk_which_implies_wit_4 := 
(
forall (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (after: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (ptcb = (task_stk_chk_table_pointer (sg) (after) (prio)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stk_chk_table_frame sg after prio )
|--
  “ (UCOS2_state_inv sg after ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (ptcb = (task_stk_chk_table_pointer (sg) (after) (prio))) ”
  &&  (critical_region_outside critical sg invocation after )
) \/
(
forall (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (after: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (ptcb = (task_stk_chk_table_pointer (sg) (after) (prio)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stk_chk_table_frame sg after prio )
|--
  (critical_region_outside critical sg invocation after )
).

Definition OS_TaskStatStkChk_which_implies_wit_4_split_goal_spatial := 
forall (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (after: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (ptcb = (task_stk_chk_table_pointer (sg) (after) (prio)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stk_chk_table_frame sg after prio )
|--
  (critical_region_outside critical sg invocation after )
.

Definition OS_TaskStatStkChk_which_implies_wit_5 := 
(
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  ((&(( &( "stk_data" ) )->ₛ "OSFree")) # UInt  |->_)
  **  ((&(( &( "stk_data" ) )->ₛ "OSUsed")) # UInt  |->_)
) \/
(
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  EX (x_2: Z)  (x: Z) ,
  ((&(( &( "stk_data" ) )->ₛ "OSUsed")) # UInt  |-> x_2)
  **  ((&(( &( "stk_data" ) )->ₛ "OSFree")) # UInt  |-> x)
).

Module Type VC_Correct.


Axiom proof_of_OS_TaskStatStkChk_safety_wit_1 : OS_TaskStatStkChk_safety_wit_1.
Axiom proof_of_OS_TaskStatStkChk_safety_wit_2 : OS_TaskStatStkChk_safety_wit_2.
Axiom proof_of_OS_TaskStatStkChk_safety_wit_3 : OS_TaskStatStkChk_safety_wit_3.
Axiom proof_of_OS_TaskStatStkChk_entail_wit_1 : OS_TaskStatStkChk_entail_wit_1.
Axiom proof_of_OS_TaskStatStkChk_entail_wit_2 : OS_TaskStatStkChk_entail_wit_2.
Axiom proof_of_OS_TaskStatStkChk_entail_wit_3_1 : OS_TaskStatStkChk_entail_wit_3_1.
Axiom proof_of_OS_TaskStatStkChk_entail_wit_3_2 : OS_TaskStatStkChk_entail_wit_3_2.
Axiom proof_of_OS_TaskStatStkChk_entail_wit_3_3 : OS_TaskStatStkChk_entail_wit_3_3.
Axiom proof_of_OS_TaskStatStkChk_entail_wit_3_4 : OS_TaskStatStkChk_entail_wit_3_4.
Axiom proof_of_OS_TaskStatStkChk_entail_wit_4 : OS_TaskStatStkChk_entail_wit_4.
Axiom proof_of_OS_TaskStatStkChk_return_wit_1 : OS_TaskStatStkChk_return_wit_1.
Axiom proof_of_OS_TaskStatStkChk_partial_solve_wit_1 : OS_TaskStatStkChk_partial_solve_wit_1.
Axiom proof_of_OS_TaskStatStkChk_partial_solve_wit_2_pure : OS_TaskStatStkChk_partial_solve_wit_2_pure.
Axiom proof_of_OS_TaskStatStkChk_partial_solve_wit_2 : OS_TaskStatStkChk_partial_solve_wit_2.
Axiom proof_of_OS_TaskStatStkChk_partial_solve_wit_3_pure : OS_TaskStatStkChk_partial_solve_wit_3_pure.
Axiom proof_of_OS_TaskStatStkChk_partial_solve_wit_3 : OS_TaskStatStkChk_partial_solve_wit_3.
Axiom proof_of_OS_TaskStatStkChk_partial_solve_wit_4_pure : OS_TaskStatStkChk_partial_solve_wit_4_pure.
Axiom proof_of_OS_TaskStatStkChk_partial_solve_wit_4 : OS_TaskStatStkChk_partial_solve_wit_4.
Axiom proof_of_OS_TaskStatStkChk_partial_solve_wit_5_pure : OS_TaskStatStkChk_partial_solve_wit_5_pure.
Axiom proof_of_OS_TaskStatStkChk_partial_solve_wit_5 : OS_TaskStatStkChk_partial_solve_wit_5.
Axiom proof_of_OS_TaskStatStkChk_partial_solve_wit_6 : OS_TaskStatStkChk_partial_solve_wit_6.
Axiom proof_of_OS_TaskStatStkChk_which_implies_wit_1 : OS_TaskStatStkChk_which_implies_wit_1.
Axiom proof_of_OS_TaskStatStkChk_which_implies_wit_2 : OS_TaskStatStkChk_which_implies_wit_2.
Axiom proof_of_OS_TaskStatStkChk_which_implies_wit_3 : OS_TaskStatStkChk_which_implies_wit_3.
Axiom proof_of_OS_TaskStatStkChk_which_implies_wit_4 : OS_TaskStatStkChk_which_implies_wit_4.
Axiom proof_of_OS_TaskStatStkChk_which_implies_wit_5 : OS_TaskStatStkChk_which_implies_wit_5.

End VC_Correct.
