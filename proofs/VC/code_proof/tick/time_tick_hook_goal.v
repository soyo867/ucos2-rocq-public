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
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_hook_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_api_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSTimeTickHook -----*)

Definition OSTimeTickHook_safety_wit_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (app_time_tick_hook_step sg before before )) (PreH2 : (0 <= counter)) (PreH3 : (counter <= 65535)) (PreH4 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH5 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH6 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> (unsigned_last_nbits ((counter + 1 )) (16)))
|--
  “ (10 <> 0) ”
.

Definition OSTimeTickHook_return_wit_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_signal_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed )) (PreH4 : (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid )) (PreH5 : (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before )) (PreH6 : (tmr_signal_safe environment critical sg caller mask eid before (time_tick_hook_signal_continuation (X)) )) (PreH7 : ((unsigned_last_nbits ((counter + 1 )) (16)) >= (100 ÷ 10 ))) (PreH8 : (app_time_tick_hook_step sg before before )) (PreH9 : (0 <= counter)) (PreH10 : (counter <= 65535)) (PreH11 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH12 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH13 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_hook_post environment critical saved_local sg caller mask eid ( &( "OSTmrCtr" ) ) counter before X )
|--
  (time_tick_hook_post environment critical saved_local sg caller mask eid ( &( "OSTmrCtr" ) ) counter before X )
.

Definition OSTimeTickHook_return_wit_2 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((counter + 1 )) (16)) < (100 ÷ 10 ))) (PreH2 : (app_time_tick_hook_step sg before before )) (PreH3 : (0 <= counter)) (PreH4 : (counter <= 65535)) (PreH5 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH6 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH7 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> (unsigned_last_nbits ((counter + 1 )) (16)))
|--
  (time_tick_hook_post environment critical saved_local sg caller mask eid ( &( "OSTmrCtr" ) ) counter before X )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((counter + 1 )) (16)) < (100 ÷ 10 ))) (PreH2 : (app_time_tick_hook_step sg before before )) (PreH3 : (0 <= counter)) (PreH4 : (counter <= 65535)) (PreH5 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH6 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH7 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> (unsigned_last_nbits ((counter + 1 )) (16)))
|--
  (time_tick_hook_post environment critical saved_local sg caller mask eid ( &( "OSTmrCtr" ) ) counter before X )
).

Definition OSTimeTickHook_return_wit_2_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((counter + 1 )) (16)) < (100 ÷ 10 ))) (PreH2 : (app_time_tick_hook_step sg before before )) (PreH3 : (0 <= counter)) (PreH4 : (counter <= 65535)) (PreH5 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH6 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH7 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> (unsigned_last_nbits ((counter + 1 )) (16)))
|--
  (time_tick_hook_post environment critical saved_local sg caller mask eid ( &( "OSTmrCtr" ) ) counter before X )
.

Definition OSTimeTickHook_partial_solve_wit_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= counter)) (PreH2 : (counter <= 65535)) (PreH3 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH4 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH5 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_hook_frame environment critical saved_local sg caller mask ( &( "OSTmrCtr" ) ) counter before )
|--
  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed ) ” 
  &&  “ (time_tick_hook_safe environment critical sg caller mask eid counter before X ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (time_tick_hook_frame environment critical saved_local sg caller mask ( &( "OSTmrCtr" ) ) counter before )
.

Definition OSTimeTickHook_partial_solve_wit_2 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (app_time_tick_hook_step sg before before )) (PreH2 : (0 <= counter)) (PreH3 : (counter <= 65535)) (PreH4 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH5 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH6 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_hook_frame environment critical saved_local sg caller mask ( &( "OSTmrCtr" ) ) counter before )
|--
  “ (app_time_tick_hook_step sg before before ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed ) ” 
  &&  “ (time_tick_hook_safe environment critical sg caller mask eid counter before X ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (time_tick_hook_frame environment critical saved_local sg caller mask ( &( "OSTmrCtr" ) ) counter before )
.

Definition OSTimeTickHook_partial_solve_wit_3_pure := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((counter + 1 )) (16)) >= (100 ÷ 10 ))) (PreH2 : (app_time_tick_hook_step sg before before )) (PreH3 : (0 <= counter)) (PreH4 : (counter <= 65535)) (PreH5 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH6 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH7 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  “ (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed ) ” 
  &&  “ (time_tick_hook_safe environment critical sg caller mask eid counter before X ) ” 
  &&  “ (10 <= (time_tick_hook_advanced (counter))) ”
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((counter + 1 )) (16)) >= (100 ÷ 10 ))) (PreH2 : (app_time_tick_hook_step sg before before )) (PreH3 : (0 <= counter)) (PreH4 : (counter <= 65535)) (PreH5 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH6 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH7 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  “ (10 <= (time_tick_hook_advanced (counter))) ”
).

Definition OSTimeTickHook_partial_solve_wit_3_pure_split_goal_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((counter + 1 )) (16)) >= (100 ÷ 10 ))) (PreH2 : (app_time_tick_hook_step sg before before )) (PreH3 : (0 <= counter)) (PreH4 : (counter <= 65535)) (PreH5 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH6 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH7 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  “ (10 <= (time_tick_hook_advanced (counter))) ”
.

Definition OSTimeTickHook_partial_solve_wit_3_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((counter + 1 )) (16)) >= (100 ÷ 10 ))) (PreH2 : (app_time_tick_hook_step sg before before )) (PreH3 : (0 <= counter)) (PreH4 : (counter <= 65535)) (PreH5 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH6 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH7 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  “ (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed ) ” 
  &&  “ (time_tick_hook_safe environment critical sg caller mask eid counter before X ) ” 
  &&  “ (10 <= (time_tick_hook_advanced (counter))) ” 
  &&  “ ((unsigned_last_nbits ((counter + 1 )) (16)) >= (100 ÷ 10 )) ” 
  &&  “ (app_time_tick_hook_step sg before before ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed ) ” 
  &&  “ (time_tick_hook_safe environment critical sg caller mask eid counter before X ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
.

Definition OSTimeTickHook_partial_solve_wit_3 := OSTimeTickHook_partial_solve_wit_3_pure -> OSTimeTickHook_partial_solve_wit_3_aux.

Definition OSTimeTickHook_partial_solve_wit_4_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_signal_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed )) (PreH4 : (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid )) (PreH5 : (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before )) (PreH6 : (tmr_signal_safe environment critical sg caller mask eid before (time_tick_hook_signal_continuation (X)) )) (PreH7 : ((unsigned_last_nbits ((counter + 1 )) (16)) >= (100 ÷ 10 ))) (PreH8 : (app_time_tick_hook_step sg before before )) (PreH9 : (0 <= counter)) (PreH10 : (counter <= 65535)) (PreH11 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH12 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH13 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  “ (tmr_signal_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed ) ” 
  &&  “ (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before ) ” 
  &&  “ (tmr_signal_safe environment critical sg caller mask eid before (time_tick_hook_signal_continuation (X)) ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTimeTickHook_partial_solve_wit_4_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_signal_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed )) (PreH4 : (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid )) (PreH5 : (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before )) (PreH6 : (tmr_signal_safe environment critical sg caller mask eid before (time_tick_hook_signal_continuation (X)) )) (PreH7 : ((unsigned_last_nbits ((counter + 1 )) (16)) >= (100 ÷ 10 ))) (PreH8 : (app_time_tick_hook_step sg before before )) (PreH9 : (0 <= counter)) (PreH10 : (counter <= 65535)) (PreH11 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH12 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH13 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  “ (tmr_signal_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed ) ” 
  &&  “ (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before ) ” 
  &&  “ (tmr_signal_safe environment critical sg caller mask eid before (time_tick_hook_signal_continuation (X)) ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_signal_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed ) ” 
  &&  “ (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before ) ” 
  &&  “ (tmr_signal_safe environment critical sg caller mask eid before (time_tick_hook_signal_continuation (X)) ) ” 
  &&  “ ((unsigned_last_nbits ((counter + 1 )) (16)) >= (100 ÷ 10 )) ” 
  &&  “ (app_time_tick_hook_step sg before before ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed ) ” 
  &&  “ (time_tick_hook_safe environment critical sg caller mask eid counter before X ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
.

Definition OSTimeTickHook_partial_solve_wit_4 := OSTimeTickHook_partial_solve_wit_4_pure -> OSTimeTickHook_partial_solve_wit_4_aux.

Definition OSTimeTickHook_partial_solve_wit_5_pure := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (tmr_signal_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed )) (PreH4 : (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid )) (PreH5 : (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before )) (PreH6 : (tmr_signal_safe environment critical sg caller mask eid before (time_tick_hook_signal_continuation (X)) )) (PreH7 : ((unsigned_last_nbits ((counter + 1 )) (16)) >= (100 ÷ 10 ))) (PreH8 : (app_time_tick_hook_step sg before before )) (PreH9 : (0 <= counter)) (PreH10 : (counter <= 65535)) (PreH11 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH12 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH13 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (tmr_signal_post environment critical saved_local sg caller mask eid before retval (time_tick_hook_signal_continuation (X)) )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  “ (10 <= (time_tick_hook_advanced (counter))) ”
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (tmr_signal_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed )) (PreH4 : (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid )) (PreH5 : (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before )) (PreH6 : (tmr_signal_safe environment critical sg caller mask eid before (time_tick_hook_signal_continuation (X)) )) (PreH7 : ((unsigned_last_nbits ((counter + 1 )) (16)) >= (100 ÷ 10 ))) (PreH8 : (app_time_tick_hook_step sg before before )) (PreH9 : (0 <= counter)) (PreH10 : (counter <= 65535)) (PreH11 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH12 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH13 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (tmr_signal_post environment critical saved_local sg caller mask eid before retval (time_tick_hook_signal_continuation (X)) )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  “ (10 <= (time_tick_hook_advanced (counter))) ”
).

Definition OSTimeTickHook_partial_solve_wit_5_pure_split_goal_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (tmr_signal_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed )) (PreH4 : (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid )) (PreH5 : (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before )) (PreH6 : (tmr_signal_safe environment critical sg caller mask eid before (time_tick_hook_signal_continuation (X)) )) (PreH7 : ((unsigned_last_nbits ((counter + 1 )) (16)) >= (100 ÷ 10 ))) (PreH8 : (app_time_tick_hook_step sg before before )) (PreH9 : (0 <= counter)) (PreH10 : (counter <= 65535)) (PreH11 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH12 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH13 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (tmr_signal_post environment critical saved_local sg caller mask eid before retval (time_tick_hook_signal_continuation (X)) )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  “ (10 <= (time_tick_hook_advanced (counter))) ”
.

Definition OSTimeTickHook_partial_solve_wit_5_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (tmr_signal_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed )) (PreH4 : (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid )) (PreH5 : (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before )) (PreH6 : (tmr_signal_safe environment critical sg caller mask eid before (time_tick_hook_signal_continuation (X)) )) (PreH7 : ((unsigned_last_nbits ((counter + 1 )) (16)) >= (100 ÷ 10 ))) (PreH8 : (app_time_tick_hook_step sg before before )) (PreH9 : (0 <= counter)) (PreH10 : (counter <= 65535)) (PreH11 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH12 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) (PreH13 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (tmr_signal_post environment critical saved_local sg caller mask eid before retval (time_tick_hook_signal_continuation (X)) )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  “ (10 <= (time_tick_hook_advanced (counter))) ” 
  &&  “ (tmr_signal_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed ) ” 
  &&  “ (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before ) ” 
  &&  “ (tmr_signal_safe environment critical sg caller mask eid before (time_tick_hook_signal_continuation (X)) ) ” 
  &&  “ ((unsigned_last_nbits ((counter + 1 )) (16)) >= (100 ÷ 10 )) ” 
  &&  “ (app_time_tick_hook_step sg before before ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed ) ” 
  &&  “ (time_tick_hook_safe environment critical sg caller mask eid counter before X ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
  **  (tmr_signal_post environment critical saved_local sg caller mask eid before retval (time_tick_hook_signal_continuation (X)) )
.

Definition OSTimeTickHook_partial_solve_wit_5 := OSTimeTickHook_partial_solve_wit_5_pure -> OSTimeTickHook_partial_solve_wit_5_aux.

Definition OSTimeTickHook_which_implies_wit_1 := 
(
forall (counter: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) ,
  (time_tick_hook_frame environment critical saved_local sg caller mask ( &( "OSTmrCtr" ) ) counter before )
|--
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> counter)
) \/
(
forall (counter: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) ,
  (time_tick_hook_frame environment critical saved_local sg caller mask ( &( "OSTmrCtr" ) ) counter before )
|--
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> counter)
).

Definition OSTimeTickHook_which_implies_wit_1_split_goal_spatial := 
forall (counter: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) ,
  (time_tick_hook_frame environment critical saved_local sg caller mask ( &( "OSTmrCtr" ) ) counter before )
|--
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> counter)
.

Definition OSTimeTickHook_which_implies_wit_2 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (10 <= (time_tick_hook_advanced (counter)))) (PreH2 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH3 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  “ (tmr_signal_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed ) ” 
  &&  “ (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before ) ” 
  &&  “ (tmr_signal_safe environment critical sg caller mask eid before (time_tick_hook_signal_continuation (X)) ) ”
  &&  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (10 <= (time_tick_hook_advanced (counter)))) (PreH2 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH3 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) ,
  TT && emp 
|--
  “ (tmr_signal_safe environment critical sg caller mask eid before (time_tick_hook_signal_continuation (X)) ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before ) ” 
  &&  “ (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid ) ” 
  &&  “ (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_signal_profile sg ) ”
  &&  emp
).

Definition OSTimeTickHook_which_implies_wit_2_split_goal_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (10 <= (time_tick_hook_advanced (counter)))) (PreH2 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH3 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) ,
  (tmr_signal_safe environment critical sg caller mask eid before (time_tick_hook_signal_continuation (X)) )
.

Definition OSTimeTickHook_which_implies_wit_2_split_goal_2 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (10 <= (time_tick_hook_advanced (counter)))) (PreH2 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH3 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) ,
  (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before )
.

Definition OSTimeTickHook_which_implies_wit_2_split_goal_3 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (10 <= (time_tick_hook_advanced (counter)))) (PreH2 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH3 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) ,
  (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid )
.

Definition OSTimeTickHook_which_implies_wit_2_split_goal_4 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (10 <= (time_tick_hook_advanced (counter)))) (PreH2 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH3 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) ,
  (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed )
.

Definition OSTimeTickHook_which_implies_wit_2_split_goal_5 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (10 <= (time_tick_hook_advanced (counter)))) (PreH2 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH3 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) ,
  (UCOS2_state_inv sg before )
.

Definition OSTimeTickHook_which_implies_wit_2_split_goal_6 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (10 <= (time_tick_hook_advanced (counter)))) (PreH2 : (time_tick_hook_call_inputs environment critical sg caller mask counter before eid observed )) (PreH3 : (time_tick_hook_safe environment critical sg caller mask eid counter before X )) ,
  (tmr_signal_profile sg )
.

Definition OSTimeTickHook_which_implies_wit_3 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (error: Z) (PreH1 : (10 <= (time_tick_hook_advanced (counter)))) ,
  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
  **  (tmr_signal_post environment critical saved_local sg caller mask eid before error (time_tick_hook_signal_continuation (X)) )
|--
  (time_tick_hook_post environment critical saved_local sg caller mask eid ( &( "OSTmrCtr" ) ) counter before X )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (error: Z) (PreH1 : (10 <= (time_tick_hook_advanced (counter)))) ,
  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
  **  (tmr_signal_post environment critical saved_local sg caller mask eid before error (time_tick_hook_signal_continuation (X)) )
|--
  (time_tick_hook_post environment critical saved_local sg caller mask eid ( &( "OSTmrCtr" ) ) counter before X )
).

Definition OSTimeTickHook_which_implies_wit_3_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (error: Z) (PreH1 : (10 <= (time_tick_hook_advanced (counter)))) ,
  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
  **  (tmr_signal_post environment critical saved_local sg caller mask eid before error (time_tick_hook_signal_continuation (X)) )
|--
  (time_tick_hook_post environment critical saved_local sg caller mask eid ( &( "OSTmrCtr" ) ) counter before X )
.

Module Type VC_Correct.


Axiom proof_of_OSTimeTickHook_safety_wit_1 : OSTimeTickHook_safety_wit_1.
Axiom proof_of_OSTimeTickHook_return_wit_1 : OSTimeTickHook_return_wit_1.
Axiom proof_of_OSTimeTickHook_return_wit_2 : OSTimeTickHook_return_wit_2.
Axiom proof_of_OSTimeTickHook_partial_solve_wit_1 : OSTimeTickHook_partial_solve_wit_1.
Axiom proof_of_OSTimeTickHook_partial_solve_wit_2 : OSTimeTickHook_partial_solve_wit_2.
Axiom proof_of_OSTimeTickHook_partial_solve_wit_3_pure : OSTimeTickHook_partial_solve_wit_3_pure.
Axiom proof_of_OSTimeTickHook_partial_solve_wit_3 : OSTimeTickHook_partial_solve_wit_3.
Axiom proof_of_OSTimeTickHook_partial_solve_wit_4_pure : OSTimeTickHook_partial_solve_wit_4_pure.
Axiom proof_of_OSTimeTickHook_partial_solve_wit_4 : OSTimeTickHook_partial_solve_wit_4.
Axiom proof_of_OSTimeTickHook_partial_solve_wit_5_pure : OSTimeTickHook_partial_solve_wit_5_pure.
Axiom proof_of_OSTimeTickHook_partial_solve_wit_5 : OSTimeTickHook_partial_solve_wit_5.
Axiom proof_of_OSTimeTickHook_which_implies_wit_1 : OSTimeTickHook_which_implies_wit_1.
Axiom proof_of_OSTimeTickHook_which_implies_wit_2 : OSTimeTickHook_which_implies_wit_2.
Axiom proof_of_OSTimeTickHook_which_implies_wit_3 : OSTimeTickHook_which_implies_wit_3.

End VC_Correct.
