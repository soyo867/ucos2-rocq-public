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
Require Import Ucos2Verify.VC.code.core.spec.task_stat_stk_chk_continuation_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_TaskStatStkChk -----*)

Definition OS_TaskStatStkChk_safety_wit_1 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (history: TaskStatStkChkContinuationHistory) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (prio: Z) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH5 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio <= 64)) (PreH9 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH10 : (UCOS2_state_inv sg current )) (PreH11 : (( &( "stk_data" ) ) <> 0)) (PreH12 : (task_stat_stk_chk_configuration sg )) (PreH13 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH16 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (task_suspend_closed environment critical saved_local sg current_caller mask current )
  **  (caller_frame )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
  **  ((( &( "err" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition OS_TaskStatStkChk_safety_wit_2 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (err: Z) (returned: TaskSuspendCaller) (data: (@option TaskStackCheckData)) (after: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = (task_stk_chk_table_pointer (sg) (after) (prio)))) (PreH6 : (UCOS2_state_inv sg after )) (PreH7 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (0 <= prio)) (PreH9 : (prio < 64)) (PreH10 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (task_stat_stk_chk_configuration sg )) (PreH13 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH15 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH16 : (( &( "stk_data" ) ) <> 0)) (PreH17 : (0 <= prio)) (PreH18 : (prio < 64)) (PreH19 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH20 : (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after )) (PreH21 : (UCOS2_state_inv sg after )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  ((( &( "err" ) )) # UChar  |-> err)
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TaskStatStkChk_safety_wit_3 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (err: Z) (returned: TaskSuspendCaller) (data: (@option TaskStackCheckData)) (after: UCOS2_Verify_State) (PreH1 : ((task_stk_chk_table_pointer (sg) (after) (prio)) <> 0)) (PreH2 : (UCOS2_state_inv sg after )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (0 <= prio)) (PreH5 : (prio < 64)) (PreH6 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = (task_stk_chk_table_pointer (sg) (after) (prio)))) (PreH7 : (UCOS2_state_inv sg after )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (0 <= prio)) (PreH10 : (prio < 64)) (PreH11 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (task_stat_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH16 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH17 : (( &( "stk_data" ) ) <> 0)) (PreH18 : (0 <= prio)) (PreH19 : (prio < 64)) (PreH20 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH21 : (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after )) (PreH22 : (UCOS2_state_inv sg after )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  ((( &( "err" ) )) # UChar  |-> err)
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OS_TaskStatStkChk_entail_wit_1 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (( &( "stk_data" ) ) <> 0)) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) ,
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
  **  (task_suspend_closed environment critical saved_local sg original mask before )
  **  (caller_frame )
|--
  EX (history: TaskStatStkChkContinuationHistory)  (current_caller: TaskSuspendCaller)  (current: UCOS2_Verify_State) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 64) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before 0 history current_caller current ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ”
  &&  (task_suspend_closed environment critical saved_local sg current_caller mask current )
  **  (caller_frame )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (( &( "stk_data" ) ) <> 0)) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) ,
  TT && emp 
|--
  EX (history: TaskStatStkChkContinuationHistory) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 64) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before 0 history original before ) ”
  &&  emp
).

Definition OS_TaskStatStkChk_entail_wit_2 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (prio: Z) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (error: Z) (retval: Z) (PreH1 : (retval = error)) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_configuration sg )) (PreH4 : (( &( "stk_data" ) ) <> 0)) (PreH5 : (0 <= prio)) (PreH6 : (prio < 64)) (PreH7 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH8 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH9 : (task_stk_chk_continuation_admission environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current )) (PreH10 : (task_stk_chk_continuation_safe environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current (task_stat_stk_chk_continuation_observe_call (environment) (critical) (saved_local) (sg) (current_caller) (mask) (caller_frame) (prio) (( &( "stk_data" ) )) (current)) )) (PreH11 : (prio <= 63)) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (task_stat_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH16 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH17 : (( &( "stk_data" ) ) <> 0)) (PreH18 : (0 <= prio)) (PreH19 : (prio <= 64)) (PreH20 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH21 : (UCOS2_state_inv sg current )) (PreH22 : (( &( "stk_data" ) ) <> 0)) (PreH23 : (task_stat_stk_chk_configuration sg )) (PreH24 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH27 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) ,
  (task_stk_chk_continuation_post environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current error (task_stat_stk_chk_continuation_observe_call (environment) (critical) (saved_local) (sg) (current_caller) (mask) (caller_frame) (prio) (( &( "stk_data" ) )) (current)) )
|--
  EX (data: (@option TaskStackCheckData))  (returned: TaskSuspendCaller)  (after: UCOS2_Verify_State) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current ) ” 
  &&  “ (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current retval data returned after ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (prio: Z) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (error: Z) (retval: Z) (PreH1 : (retval = error)) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_configuration sg )) (PreH4 : (( &( "stk_data" ) ) <> 0)) (PreH5 : (0 <= prio)) (PreH6 : (prio < 64)) (PreH7 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH8 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH9 : (task_stk_chk_continuation_admission environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current )) (PreH10 : (task_stk_chk_continuation_safe environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current (task_stat_stk_chk_continuation_observe_call (environment) (critical) (saved_local) (sg) (current_caller) (mask) (caller_frame) (prio) (( &( "stk_data" ) )) (current)) )) (PreH11 : (prio <= 63)) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (task_stat_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH16 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH17 : (( &( "stk_data" ) ) <> 0)) (PreH18 : (0 <= prio)) (PreH19 : (prio <= 64)) (PreH20 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH21 : (UCOS2_state_inv sg current )) (PreH22 : (( &( "stk_data" ) ) <> 0)) (PreH23 : (task_stat_stk_chk_configuration sg )) (PreH24 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH27 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) ,
  (task_stk_chk_continuation_post environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current error (task_stat_stk_chk_continuation_observe_call (environment) (critical) (saved_local) (sg) (current_caller) (mask) (caller_frame) (prio) (( &( "stk_data" ) )) (current)) )
|--
  EX (data: (@option TaskStackCheckData))  (returned: TaskSuspendCaller)  (after: UCOS2_Verify_State) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current ) ” 
  &&  “ (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current retval data returned after ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
).

Definition OS_TaskStatStkChk_entail_wit_3_1 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (err: Z) (returned: TaskSuspendCaller) (data: (@option TaskStackCheckData)) (after: UCOS2_Verify_State) (PreH1 : ((task_stk_chk_table_pointer (sg) (after) (prio)) <> 1)) (PreH2 : ((task_stk_chk_table_pointer (sg) (after) (prio)) <> 0)) (PreH3 : (UCOS2_state_inv sg after )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (0 <= prio)) (PreH6 : (prio < 64)) (PreH7 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = (task_stk_chk_table_pointer (sg) (after) (prio)))) (PreH8 : (UCOS2_state_inv sg after )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (0 <= prio)) (PreH11 : (prio < 64)) (PreH12 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (task_stat_stk_chk_configuration sg )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH17 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH18 : (( &( "stk_data" ) ) <> 0)) (PreH19 : (0 <= prio)) (PreH20 : (prio < 64)) (PreH21 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH22 : (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after )) (PreH23 : (UCOS2_state_inv sg after )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  EX (observed: (@option Z)) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current ) ” 
  &&  “ (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after ) ” 
  &&  “ (task_stat_stk_chk_continuation_table_result sg prio err after observed ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (err: Z) (returned: TaskSuspendCaller) (data: (@option TaskStackCheckData)) (after: UCOS2_Verify_State) (PreH1 : ((task_stk_chk_table_pointer (sg) (after) (prio)) <> 1)) (PreH2 : ((task_stk_chk_table_pointer (sg) (after) (prio)) <> 0)) (PreH3 : (UCOS2_state_inv sg after )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (0 <= prio)) (PreH6 : (prio < 64)) (PreH7 : (UCOS2_state_inv sg after )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (0 <= prio)) (PreH10 : (prio < 64)) (PreH11 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (task_stat_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH16 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH17 : (( &( "stk_data" ) ) <> 0)) (PreH18 : (0 <= prio)) (PreH19 : (prio < 64)) (PreH20 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH21 : (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after )) (PreH22 : (UCOS2_state_inv sg after )) ,
  TT && emp 
|--
  EX (observed: (@option Z)) ,
  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_table_result sg prio err after observed ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  emp
).

Definition OS_TaskStatStkChk_entail_wit_3_2 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (err: Z) (returned: TaskSuspendCaller) (data: (@option TaskStackCheckData)) (after: UCOS2_Verify_State) (PreH1 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = 1)) (PreH2 : ((task_stk_chk_table_pointer (sg) (after) (prio)) <> 0)) (PreH3 : (UCOS2_state_inv sg after )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (0 <= prio)) (PreH6 : (prio < 64)) (PreH7 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = (task_stk_chk_table_pointer (sg) (after) (prio)))) (PreH8 : (UCOS2_state_inv sg after )) (PreH9 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH10 : (0 <= prio)) (PreH11 : (prio < 64)) (PreH12 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (task_stat_stk_chk_configuration sg )) (PreH15 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH16 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH17 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH18 : (( &( "stk_data" ) ) <> 0)) (PreH19 : (0 <= prio)) (PreH20 : (prio < 64)) (PreH21 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH22 : (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after )) (PreH23 : (UCOS2_state_inv sg after )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  EX (observed: (@option Z)) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current ) ” 
  &&  “ (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after ) ” 
  &&  “ (task_stat_stk_chk_continuation_table_result sg prio err after observed ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (err: Z) (returned: TaskSuspendCaller) (data: (@option TaskStackCheckData)) (after: UCOS2_Verify_State) (PreH1 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = 1)) (PreH2 : ((task_stk_chk_table_pointer (sg) (after) (prio)) <> 0)) (PreH3 : (UCOS2_state_inv sg after )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (0 <= prio)) (PreH6 : (prio < 64)) (PreH7 : (UCOS2_state_inv sg after )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (0 <= prio)) (PreH10 : (prio < 64)) (PreH11 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (task_stat_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH16 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH17 : (( &( "stk_data" ) ) <> 0)) (PreH18 : (0 <= prio)) (PreH19 : (prio < 64)) (PreH20 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH21 : (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after )) (PreH22 : (UCOS2_state_inv sg after )) ,
  TT && emp 
|--
  EX (observed: (@option Z)) ,
  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_table_result sg prio err after observed ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  emp
).

Definition OS_TaskStatStkChk_entail_wit_3_3 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (err: Z) (returned: TaskSuspendCaller) (data: (@option TaskStackCheckData)) (after: UCOS2_Verify_State) (PreH1 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = 0)) (PreH2 : (UCOS2_state_inv sg after )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (0 <= prio)) (PreH5 : (prio < 64)) (PreH6 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = (task_stk_chk_table_pointer (sg) (after) (prio)))) (PreH7 : (UCOS2_state_inv sg after )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (0 <= prio)) (PreH10 : (prio < 64)) (PreH11 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (task_stat_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH16 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH17 : (( &( "stk_data" ) ) <> 0)) (PreH18 : (0 <= prio)) (PreH19 : (prio < 64)) (PreH20 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH21 : (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after )) (PreH22 : (UCOS2_state_inv sg after )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  EX (observed: (@option Z)) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current ) ” 
  &&  “ (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after ) ” 
  &&  “ (task_stat_stk_chk_continuation_table_result sg prio err after observed ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (err: Z) (returned: TaskSuspendCaller) (data: (@option TaskStackCheckData)) (after: UCOS2_Verify_State) (PreH1 : ((task_stk_chk_table_pointer (sg) (after) (prio)) = 0)) (PreH2 : (UCOS2_state_inv sg after )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (0 <= prio)) (PreH5 : (prio < 64)) (PreH6 : (UCOS2_state_inv sg after )) (PreH7 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH8 : (0 <= prio)) (PreH9 : (prio < 64)) (PreH10 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (task_stat_stk_chk_configuration sg )) (PreH13 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH15 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH16 : (( &( "stk_data" ) ) <> 0)) (PreH17 : (0 <= prio)) (PreH18 : (prio < 64)) (PreH19 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH20 : (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after )) (PreH21 : (UCOS2_state_inv sg after )) ,
  TT && emp 
|--
  EX (observed: (@option Z)) ,
  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_table_result sg prio err after observed ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  emp
).

Definition OS_TaskStatStkChk_entail_wit_3_4 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (err: Z) (returned: TaskSuspendCaller) (data: (@option TaskStackCheckData)) (after: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (err) (32)) <> 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH7 : (( &( "stk_data" ) ) <> 0)) (PreH8 : (0 <= prio)) (PreH9 : (prio < 64)) (PreH10 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH11 : (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after )) (PreH12 : (UCOS2_state_inv sg after )) ,
  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  EX (observed: (@option Z)) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current ) ” 
  &&  “ (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after ) ” 
  &&  “ (task_stat_stk_chk_continuation_table_result sg prio err after observed ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (err: Z) (returned: TaskSuspendCaller) (data: (@option TaskStackCheckData)) (after: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (err) (32)) <> 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH7 : (( &( "stk_data" ) ) <> 0)) (PreH8 : (0 <= prio)) (PreH9 : (prio < 64)) (PreH10 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH11 : (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after )) (PreH12 : (UCOS2_state_inv sg after )) ,
  TT && emp 
|--
  EX (observed: (@option Z)) ,
  “ (task_stat_stk_chk_continuation_table_result sg prio err after observed ) ”
  &&  emp
).

Definition OS_TaskStatStkChk_entail_wit_4 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (returned: TaskSuspendCaller) (data: (@option TaskStackCheckData)) (after: UCOS2_Verify_State) (prio: Z) (err: Z) (observed: (@option Z)) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH5 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio < 64)) (PreH9 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH10 : (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after )) (PreH11 : (task_stat_stk_chk_continuation_table_result sg prio err after observed )) (PreH12 : (UCOS2_state_inv sg after )) ,
  ((( &( "err" ) )) # UChar  |-> err)
  **  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  EX (next_history: TaskStatStkChkContinuationHistory) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before (prio + 1 ) next_history returned after ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
  **  ((( &( "err" ) )) # UChar  |->_)
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (returned: TaskSuspendCaller) (data: (@option TaskStackCheckData)) (after: UCOS2_Verify_State) (prio: Z) (err: Z) (observed: (@option Z)) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH5 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio < 64)) (PreH9 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH10 : (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after )) (PreH11 : (task_stat_stk_chk_continuation_table_result sg prio err after observed )) (PreH12 : (UCOS2_state_inv sg after )) ,
  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
|--
  EX (next_history: TaskStatStkChkContinuationHistory) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before (prio + 1 ) next_history returned after ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
).

Definition OS_TaskStatStkChk_entail_wit_5 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (returned: TaskSuspendCaller) (after: UCOS2_Verify_State) (next_history: TaskStatStkChkContinuationHistory) (prio: Z) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH5 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio < 64)) (PreH9 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before (prio + 1 ) next_history returned after )) (PreH10 : (UCOS2_state_inv sg after )) ,
  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  EX (history: TaskStatStkChkContinuationHistory)  (current_caller: TaskSuspendCaller)  (current: UCOS2_Verify_State) ,
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= (prio + 1 )) ” 
  &&  “ ((prio + 1 ) <= 64) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before (prio + 1 ) history current_caller current ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ”
  &&  (task_suspend_closed environment critical saved_local sg current_caller mask current )
  **  (caller_frame )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (returned: TaskSuspendCaller) (after: UCOS2_Verify_State) (next_history: TaskStatStkChkContinuationHistory) (prio: Z) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (task_stat_stk_chk_configuration sg )) (PreH3 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH4 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH5 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH6 : (( &( "stk_data" ) ) <> 0)) (PreH7 : (0 <= prio)) (PreH8 : (prio < 64)) (PreH9 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before (prio + 1 ) next_history returned after )) (PreH10 : (UCOS2_state_inv sg after )) ,
  TT && emp 
|--
  TT && emp 
).

Definition OS_TaskStatStkChk_return_wit_1 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (prio: Z) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (PreH1 : (prio > 63)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH7 : (( &( "stk_data" ) ) <> 0)) (PreH8 : (0 <= prio)) (PreH9 : (prio <= 64)) (PreH10 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH11 : (UCOS2_state_inv sg current )) (PreH12 : (( &( "stk_data" ) ) <> 0)) (PreH13 : (task_stat_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH17 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) ,
  (task_suspend_closed environment critical saved_local sg current_caller mask current )
  **  (caller_frame )
|--
  (task_stat_stk_chk_continuation_post environment critical saved_local sg original mask caller_frame before X )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (prio: Z) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (PreH1 : (prio > 63)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH7 : (( &( "stk_data" ) ) <> 0)) (PreH8 : (0 <= prio)) (PreH9 : (prio <= 64)) (PreH10 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH11 : (UCOS2_state_inv sg current )) (PreH12 : (( &( "stk_data" ) ) <> 0)) (PreH13 : (task_stat_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH17 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) ,
  (task_suspend_closed environment critical saved_local sg current_caller mask current )
  **  (caller_frame )
|--
  (task_stat_stk_chk_continuation_post environment critical saved_local sg original mask caller_frame before X )
).

Definition OS_TaskStatStkChk_return_wit_1_split_goal_spatial := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (prio: Z) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (PreH1 : (prio > 63)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH7 : (( &( "stk_data" ) ) <> 0)) (PreH8 : (0 <= prio)) (PreH9 : (prio <= 64)) (PreH10 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH11 : (UCOS2_state_inv sg current )) (PreH12 : (( &( "stk_data" ) ) <> 0)) (PreH13 : (task_stat_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH17 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) ,
  (task_suspend_closed environment critical saved_local sg current_caller mask current )
  **  (caller_frame )
|--
  (task_stat_stk_chk_continuation_post environment critical saved_local sg original mask caller_frame before X )
.

Definition OS_TaskStatStkChk_partial_solve_wit_1 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH5 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) ,
  (UndefStructPredos_stk_data ( &( "stk_data" ) ) )
  **  (task_suspend_closed environment critical saved_local sg original mask before )
  **  (caller_frame )
|--
  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ”
  &&  ((&(( &( "stk_data" ) )->ₛ "OSFree")) # UInt  |->_)
  **  ((&(( &( "stk_data" ) )->ₛ "OSUsed")) # UInt  |->_)
  **  (task_suspend_closed environment critical saved_local sg original mask before )
  **  (caller_frame )
.

Definition OS_TaskStatStkChk_partial_solve_wit_2_pure := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (prio: Z) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (PreH1 : (prio <= 63)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH7 : (( &( "stk_data" ) ) <> 0)) (PreH8 : (0 <= prio)) (PreH9 : (prio <= 64)) (PreH10 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH11 : (UCOS2_state_inv sg current )) (PreH12 : (( &( "stk_data" ) ) <> 0)) (PreH13 : (task_stat_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH17 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (task_suspend_closed environment critical saved_local sg current_caller mask current )
  **  (caller_frame )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
  **  ((( &( "err" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current ) ”
.

Definition OS_TaskStatStkChk_partial_solve_wit_2_aux := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (prio: Z) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (PreH1 : (prio <= 63)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH7 : (( &( "stk_data" ) ) <> 0)) (PreH8 : (0 <= prio)) (PreH9 : (prio <= 64)) (PreH10 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH11 : (UCOS2_state_inv sg current )) (PreH12 : (( &( "stk_data" ) ) <> 0)) (PreH13 : (task_stat_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH17 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) ,
  (task_suspend_closed environment critical saved_local sg current_caller mask current )
  **  (caller_frame )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current ) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 64) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ”
  &&  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
  **  (task_suspend_closed environment critical saved_local sg current_caller mask current )
  **  (caller_frame )
.

Definition OS_TaskStatStkChk_partial_solve_wit_2 := OS_TaskStatStkChk_partial_solve_wit_2_pure -> OS_TaskStatStkChk_partial_solve_wit_2_aux.

Definition OS_TaskStatStkChk_partial_solve_wit_3_pure := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (prio: Z) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (( &( "stk_data" ) ) <> 0)) (PreH4 : (0 <= prio)) (PreH5 : (prio < 64)) (PreH6 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH7 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH8 : (task_stk_chk_continuation_admission environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current )) (PreH9 : (task_stk_chk_continuation_safe environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current (task_stat_stk_chk_continuation_observe_call (environment) (critical) (saved_local) (sg) (current_caller) (mask) (caller_frame) (prio) (( &( "stk_data" ) )) (current)) )) (PreH10 : (prio <= 63)) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (task_stat_stk_chk_configuration sg )) (PreH13 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH15 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH16 : (( &( "stk_data" ) ) <> 0)) (PreH17 : (0 <= prio)) (PreH18 : (prio <= 64)) (PreH19 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH20 : (UCOS2_state_inv sg current )) (PreH21 : (( &( "stk_data" ) ) <> 0)) (PreH22 : (task_stat_stk_chk_configuration sg )) (PreH23 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH26 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (task_stk_chk_output_pre sg prio ( &( "stk_data" ) ) )
  **  (task_suspend_closed environment critical saved_local sg current_caller mask current )
  **  (caller_frame )
  **  ((( &( "err" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (0 <= prio) ” 
  &&  “ (prio <= 255) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_continuation_admission environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current ) ” 
  &&  “ (task_stk_chk_continuation_safe environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current (task_stat_stk_chk_continuation_observe_call (environment) (critical) (saved_local) (sg) (current_caller) (mask) (caller_frame) (prio) (( &( "stk_data" ) )) (current)) ) ”
.

Definition OS_TaskStatStkChk_partial_solve_wit_3_aux := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (prio: Z) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (task_stk_chk_configuration sg )) (PreH3 : (( &( "stk_data" ) ) <> 0)) (PreH4 : (0 <= prio)) (PreH5 : (prio < 64)) (PreH6 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH7 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH8 : (task_stk_chk_continuation_admission environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current )) (PreH9 : (task_stk_chk_continuation_safe environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current (task_stat_stk_chk_continuation_observe_call (environment) (critical) (saved_local) (sg) (current_caller) (mask) (caller_frame) (prio) (( &( "stk_data" ) )) (current)) )) (PreH10 : (prio <= 63)) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (task_stat_stk_chk_configuration sg )) (PreH13 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH14 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH15 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH16 : (( &( "stk_data" ) ) <> 0)) (PreH17 : (0 <= prio)) (PreH18 : (prio <= 64)) (PreH19 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH20 : (UCOS2_state_inv sg current )) (PreH21 : (( &( "stk_data" ) ) <> 0)) (PreH22 : (task_stat_stk_chk_configuration sg )) (PreH23 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH26 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) ,
  (task_stk_chk_output_pre sg prio ( &( "stk_data" ) ) )
  **  (task_suspend_closed environment critical saved_local sg current_caller mask current )
  **  (caller_frame )
|--
  “ (0 <= prio) ” 
  &&  “ (prio <= 255) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stk_chk_continuation_admission environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current ) ” 
  &&  “ (task_stk_chk_continuation_safe environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current (task_stat_stk_chk_continuation_observe_call (environment) (critical) (saved_local) (sg) (current_caller) (mask) (caller_frame) (prio) (( &( "stk_data" ) )) (current)) ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current ) ” 
  &&  “ (task_stk_chk_continuation_admission environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current ) ” 
  &&  “ (task_stk_chk_continuation_safe environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current (task_stat_stk_chk_continuation_observe_call (environment) (critical) (saved_local) (sg) (current_caller) (mask) (caller_frame) (prio) (( &( "stk_data" ) )) (current)) ) ” 
  &&  “ (prio <= 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 64) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ”
  &&  (task_suspend_closed environment critical saved_local sg current_caller mask current )
  **  (caller_frame )
  **  (task_stk_chk_output_pre sg prio ( &( "stk_data" ) ) )
.

Definition OS_TaskStatStkChk_partial_solve_wit_3 := OS_TaskStatStkChk_partial_solve_wit_3_pure -> OS_TaskStatStkChk_partial_solve_wit_3_aux.

Definition OS_TaskStatStkChk_partial_solve_wit_4_pure := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (err: Z) (returned: TaskSuspendCaller) (data: (@option TaskStackCheckData)) (after: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH7 : (( &( "stk_data" ) ) <> 0)) (PreH8 : (0 <= prio)) (PreH9 : (prio < 64)) (PreH10 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH11 : (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after )) (PreH12 : (UCOS2_state_inv sg after )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "err" ) )) # UChar  |-> err)
  **  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (UCOS2_state_inv sg after ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ”
.

Definition OS_TaskStatStkChk_partial_solve_wit_4_aux := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (err: Z) (returned: TaskSuspendCaller) (data: (@option TaskStackCheckData)) (after: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH7 : (( &( "stk_data" ) ) <> 0)) (PreH8 : (0 <= prio)) (PreH9 : (prio < 64)) (PreH10 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH11 : (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after )) (PreH12 : (UCOS2_state_inv sg after )) ,
  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
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
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current ) ” 
  &&  “ (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (task_suspend_closed environment critical saved_local sg returned mask after )
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
.

Definition OS_TaskStatStkChk_partial_solve_wit_4 := OS_TaskStatStkChk_partial_solve_wit_4_pure -> OS_TaskStatStkChk_partial_solve_wit_4_aux.

Definition OS_TaskStatStkChk_partial_solve_wit_5_pure := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (err: Z) (returned: TaskSuspendCaller) (data: (@option TaskStackCheckData)) (after: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (task_stat_stk_chk_configuration sg )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH10 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH11 : (( &( "stk_data" ) ) <> 0)) (PreH12 : (0 <= prio)) (PreH13 : (prio < 64)) (PreH14 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH15 : (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after )) (PreH16 : (UCOS2_state_inv sg after )) ,
  ((( &( "prio" ) )) # UChar  |-> prio)
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stat_stk_chk_continuation_table_frame environment saved_local sg returned mask after prio )
  **  ((( &( "err" ) )) # UChar  |-> err)
  **  (caller_frame )
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
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (err: Z) (returned: TaskSuspendCaller) (data: (@option TaskStackCheckData)) (after: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : ((unsigned_last_nbits (err) (32)) = 0)) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (task_stat_stk_chk_configuration sg )) (PreH8 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH9 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH10 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH11 : (( &( "stk_data" ) ) <> 0)) (PreH12 : (0 <= prio)) (PreH13 : (prio < 64)) (PreH14 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH15 : (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after )) (PreH16 : (UCOS2_state_inv sg after )) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stat_stk_chk_continuation_table_frame environment saved_local sg returned mask after prio )
  **  (caller_frame )
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
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current ) ” 
  &&  “ (task_stat_stk_chk_continuation_call_result environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current err data returned after ) ” 
  &&  “ (UCOS2_state_inv sg after ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stat_stk_chk_continuation_table_frame environment saved_local sg returned mask after prio )
  **  (caller_frame )
  **  (task_stk_chk_output_post ( &( "stk_data" ) ) data )
.

Definition OS_TaskStatStkChk_partial_solve_wit_5 := OS_TaskStatStkChk_partial_solve_wit_5_pure -> OS_TaskStatStkChk_partial_solve_wit_5_aux.

Definition OS_TaskStatStkChk_partial_solve_wit_6 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (prio: Z) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (PreH1 : (prio > 63)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (task_stat_stk_chk_configuration sg )) (PreH4 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) (PreH7 : (( &( "stk_data" ) ) <> 0)) (PreH8 : (0 <= prio)) (PreH9 : (prio <= 64)) (PreH10 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) (PreH11 : (UCOS2_state_inv sg current )) (PreH12 : (( &( "stk_data" ) ) <> 0)) (PreH13 : (task_stat_stk_chk_configuration sg )) (PreH14 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH17 : (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X )) ,
  (task_suspend_closed environment critical saved_local sg current_caller mask current )
  **  (caller_frame )
  **  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  “ (prio > 63) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio <= 64) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_safe environment critical saved_local sg original mask caller_frame before X ) ”
  &&  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
  **  (task_suspend_closed environment critical saved_local sg current_caller mask current )
  **  (caller_frame )
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
forall (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (( &( "stk_data" ) ) <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) ,
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  “ (task_stat_stk_chk_configuration sg ) ” 
  &&  “ (task_stk_chk_configuration sg ) ” 
  &&  “ (( &( "stk_data" ) ) <> 0) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before ) ” 
  &&  “ (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current ) ” 
  &&  “ (task_stk_chk_continuation_admission environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current ) ” 
  &&  “ (task_stk_chk_continuation_safe environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current (task_stat_stk_chk_continuation_observe_call (environment) (critical) (saved_local) (sg) (current_caller) (mask) (caller_frame) (prio) (( &( "stk_data" ) )) (current)) ) ”
  &&  (task_stk_chk_output_pre sg prio ( &( "stk_data" ) ) )
) \/
(
forall (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (( &( "stk_data" ) ) <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) ,
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  “ (task_stk_chk_continuation_safe environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current (task_stat_stk_chk_continuation_observe_call (environment) (critical) (saved_local) (sg) (current_caller) (mask) (caller_frame) (prio) (( &( "stk_data" ) )) (current)) ) ” 
  &&  “ (task_stk_chk_continuation_admission environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current ) ” 
  &&  “ (task_stk_chk_configuration sg ) ”
  &&  (task_stk_chk_output_pre sg prio ( &( "stk_data" ) ) )
).

Definition OS_TaskStatStkChk_which_implies_wit_2_split_goal_1 := 
forall (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (( &( "stk_data" ) ) <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) ,
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  “ (task_stk_chk_continuation_safe environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current (task_stat_stk_chk_continuation_observe_call (environment) (critical) (saved_local) (sg) (current_caller) (mask) (caller_frame) (prio) (( &( "stk_data" ) )) (current)) ) ”
.

Definition OS_TaskStatStkChk_which_implies_wit_2_split_goal_2 := 
forall (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (( &( "stk_data" ) ) <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) ,
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  “ (task_stk_chk_continuation_admission environment critical saved_local sg current_caller mask caller_frame prio ( &( "stk_data" ) ) current ) ”
.

Definition OS_TaskStatStkChk_which_implies_wit_2_split_goal_3 := 
forall (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (( &( "stk_data" ) ) <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) ,
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  “ (task_stk_chk_configuration sg ) ”
.

Definition OS_TaskStatStkChk_which_implies_wit_2_split_goal_spatial := 
forall (caller_frame: Assertion) (before: UCOS2_Verify_State) (mask: Z) (original: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (current_caller: TaskSuspendCaller) (current: UCOS2_Verify_State) (history: TaskStatStkChkContinuationHistory) (prio: Z) (PreH1 : (task_stat_stk_chk_configuration sg )) (PreH2 : (( &( "stk_data" ) ) <> 0)) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (task_stat_stk_chk_continuation_protocol environment critical saved_local sg original mask caller_frame before )) (PreH6 : (task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask caller_frame ( &( "stk_data" ) ) original before prio history current_caller current )) ,
  (task_stk_chk_output_undef ( &( "stk_data" ) ) )
|--
  (task_stk_chk_output_pre sg prio ( &( "stk_data" ) ) )
.

Definition OS_TaskStatStkChk_which_implies_wit_3 := 
(
forall (mask: Z) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (returned: TaskSuspendCaller) (after: UCOS2_Verify_State) (prio: Z) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) ,
  (task_suspend_closed environment critical saved_local sg returned mask after )
|--
  “ (UCOS2_state_inv sg after ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stat_stk_chk_continuation_table_frame environment saved_local sg returned mask after prio )
) \/
(
forall (mask: Z) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (returned: TaskSuspendCaller) (after: UCOS2_Verify_State) (prio: Z) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) ,
  (task_suspend_closed environment critical saved_local sg returned mask after )
|--
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stat_stk_chk_continuation_table_frame environment saved_local sg returned mask after prio )
).

Definition OS_TaskStatStkChk_which_implies_wit_3_split_goal_spatial := 
forall (mask: Z) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (returned: TaskSuspendCaller) (after: UCOS2_Verify_State) (prio: Z) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) ,
  (task_suspend_closed environment critical saved_local sg returned mask after )
|--
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stat_stk_chk_continuation_table_frame environment saved_local sg returned mask after prio )
.

Definition OS_TaskStatStkChk_which_implies_wit_4 := 
(
forall (mask: Z) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (returned: TaskSuspendCaller) (after: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (ptcb = (task_stk_chk_table_pointer (sg) (after) (prio)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stat_stk_chk_continuation_table_frame environment saved_local sg returned mask after prio )
|--
  “ (UCOS2_state_inv sg after ) ” 
  &&  “ (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) ) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 64) ” 
  &&  “ (ptcb = (task_stk_chk_table_pointer (sg) (after) (prio))) ”
  &&  (task_suspend_closed environment critical saved_local sg returned mask after )
) \/
(
forall (mask: Z) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (returned: TaskSuspendCaller) (after: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (ptcb = (task_stk_chk_table_pointer (sg) (after) (prio)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stat_stk_chk_continuation_table_frame environment saved_local sg returned mask after prio )
|--
  (task_suspend_closed environment critical saved_local sg returned mask after )
).

Definition OS_TaskStatStkChk_which_implies_wit_4_split_goal_spatial := 
forall (mask: Z) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (returned: TaskSuspendCaller) (after: UCOS2_Verify_State) (prio: Z) (ptcb: Z) (PreH1 : (UCOS2_state_inv sg after )) (PreH2 : (task_stk_chk_global_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSTCBPrioTbl" ) ) )) (PreH3 : (0 <= prio)) (PreH4 : (prio < 64)) (PreH5 : (ptcb = (task_stk_chk_table_pointer (sg) (after) (prio)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (task_stk_chk_table_pointer (sg) (after) (prio)))
  **  (task_stat_stk_chk_continuation_table_frame environment saved_local sg returned mask after prio )
|--
  (task_suspend_closed environment critical saved_local sg returned mask after )
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
Axiom proof_of_OS_TaskStatStkChk_entail_wit_5 : OS_TaskStatStkChk_entail_wit_5.
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
