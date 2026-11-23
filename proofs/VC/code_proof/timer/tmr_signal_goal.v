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
Require Import Ucos2Verify.VC.code.timer.spec.tmr_signal_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSTmrSignal -----*)

Definition OSTmrSignal_return_wit_1 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (sem_post_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (sem_post_api_safe environment critical sg caller mask (tmr_signal_pointer (before)) eid before X )) (PreH4 : (tmr_signal_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH7 : (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed )) (PreH8 : (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid )) (PreH9 : (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before )) (PreH10 : (tmr_signal_safe environment critical sg caller mask eid before X )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_post environment critical saved_local sg caller mask (tmr_signal_pointer (before)) eid before retval X )
|--
  (tmr_signal_post environment critical saved_local sg caller mask eid before retval X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (sem_post_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (sem_post_api_safe environment critical sg caller mask (tmr_signal_pointer (before)) eid before X )) (PreH4 : (tmr_signal_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH7 : (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed )) (PreH8 : (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid )) (PreH9 : (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before )) (PreH10 : (tmr_signal_safe environment critical sg caller mask eid before X )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_post environment critical saved_local sg caller mask (tmr_signal_pointer (before)) eid before retval X )
|--
  (tmr_signal_post environment critical saved_local sg caller mask eid before retval X )
).

Definition OSTmrSignal_return_wit_1_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (sem_post_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (sem_post_api_safe environment critical sg caller mask (tmr_signal_pointer (before)) eid before X )) (PreH4 : (tmr_signal_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH7 : (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed )) (PreH8 : (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid )) (PreH9 : (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before )) (PreH10 : (tmr_signal_safe environment critical sg caller mask eid before X )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_post environment critical saved_local sg caller mask (tmr_signal_pointer (before)) eid before retval X )
|--
  (tmr_signal_post environment critical saved_local sg caller mask eid before retval X )
.

Definition OSTmrSignal_partial_solve_wit_1_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_signal_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH4 : (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed )) (PreH5 : (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid )) (PreH6 : (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before )) (PreH7 : (tmr_signal_safe environment critical sg caller mask eid before X )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "err" ) )) # UChar  |->_)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (tmr_signal_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (tmr_signal_safe environment critical sg caller mask eid before X ) ”
.

Definition OSTmrSignal_partial_solve_wit_1_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_signal_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH4 : (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed )) (PreH5 : (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid )) (PreH6 : (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before )) (PreH7 : (tmr_signal_safe environment critical sg caller mask eid before X )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (tmr_signal_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (tmr_signal_safe environment critical sg caller mask eid before X ) ” 
  &&  “ (tmr_signal_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed ) ” 
  &&  “ (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before ) ” 
  &&  “ (tmr_signal_safe environment critical sg caller mask eid before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_closed environment critical saved_local sg caller mask before )
.

Definition OSTmrSignal_partial_solve_wit_1 := OSTmrSignal_partial_solve_wit_1_pure -> OSTmrSignal_partial_solve_wit_1_aux.

Definition OSTmrSignal_partial_solve_wit_2_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (sem_post_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (sem_post_api_safe environment critical sg caller mask (tmr_signal_pointer (before)) eid before X )) (PreH4 : (tmr_signal_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH7 : (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed )) (PreH8 : (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid )) (PreH9 : (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before )) (PreH10 : (tmr_signal_safe environment critical sg caller mask eid before X )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> (tmr_signal_pointer (before)))
  **  (tmr_signal_read_frame environment saved_local sg caller mask before )
  **  ((( &( "err" ) )) # UChar  |->_)
|--
  “ ((tmr_signal_pointer (before)) = (tmr_signal_pointer (before))) ” 
  &&  “ (tmr_signal_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed ) ” 
  &&  “ (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before ) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask (tmr_signal_pointer (before)) eid before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrSignal_partial_solve_wit_2_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (sem_post_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (sem_post_api_safe environment critical sg caller mask (tmr_signal_pointer (before)) eid before X )) (PreH4 : (tmr_signal_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH7 : (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed )) (PreH8 : (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid )) (PreH9 : (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before )) (PreH10 : (tmr_signal_safe environment critical sg caller mask eid before X )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> (tmr_signal_pointer (before)))
  **  (tmr_signal_read_frame environment saved_local sg caller mask before )
|--
  “ ((tmr_signal_pointer (before)) = (tmr_signal_pointer (before))) ” 
  &&  “ (tmr_signal_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed ) ” 
  &&  “ (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before ) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask (tmr_signal_pointer (before)) eid before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask (tmr_signal_pointer (before)) eid before X ) ” 
  &&  “ (tmr_signal_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (sem_post_api_call_input critical sg caller (tmr_signal_pointer (before)) before eid observed ) ” 
  &&  “ (tmr_signal_optional_event_layout sg (tmr_signal_pointer (before)) eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask (tmr_signal_pointer (before)) eid before ) ” 
  &&  “ (tmr_signal_safe environment critical sg caller mask eid before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> (tmr_signal_pointer (before)))
  **  (tmr_signal_read_frame environment saved_local sg caller mask before )
.

Definition OSTmrSignal_partial_solve_wit_2 := OSTmrSignal_partial_solve_wit_2_pure -> OSTmrSignal_partial_solve_wit_2_aux.

Definition OSTmrSignal_which_implies_wit_1 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_signal_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH4 : (tmr_signal_safe environment critical sg caller mask eid before X )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask (tmr_signal_pointer (before)) eid before X ) ”
  &&  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> (tmr_signal_pointer (before)))
  **  (tmr_signal_read_frame environment saved_local sg caller mask before )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_signal_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH4 : (tmr_signal_safe environment critical sg caller mask eid before X )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (sem_post_api_safe environment critical sg caller mask (tmr_signal_pointer (before)) eid before X ) ” 
  &&  “ (sem_post_profile sg ) ”
  &&  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> (tmr_signal_pointer (before)))
  **  (tmr_signal_read_frame environment saved_local sg caller mask before )
).

Definition OSTmrSignal_which_implies_wit_1_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_signal_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH4 : (tmr_signal_safe environment critical sg caller mask eid before X )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (sem_post_api_safe environment critical sg caller mask (tmr_signal_pointer (before)) eid before X ) ”
.

Definition OSTmrSignal_which_implies_wit_1_split_goal_2 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_signal_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH4 : (tmr_signal_safe environment critical sg caller mask eid before X )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (sem_post_profile sg ) ”
.

Definition OSTmrSignal_which_implies_wit_1_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (tmr_signal_profile sg )) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH4 : (tmr_signal_safe environment critical sg caller mask eid before X )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> (tmr_signal_pointer (before)))
  **  (tmr_signal_read_frame environment saved_local sg caller mask before )
.

Definition OSSemPost_derive_tmr_signal_sem_post_by_sem_post_api := 
forall (pevent_pre: Z) (X_tmr_signal_sem_post: (Z -> (UCOS2_Verify_State -> Prop))) (observed_tmr_signal_sem_post: OSEventAbstractState) (eid_tmr_signal_sem_post: Z) (before_tmr_signal_sem_post: UCOS2_Verify_State) (mask_tmr_signal_sem_post: Z) (caller_tmr_signal_sem_post: TaskResumeCaller) (sg_tmr_signal_sem_post: StableGlobVars) (critical_tmr_signal_sem_post: CriticalRegionResources) (saved_local_tmr_signal_sem_post: (Armv7aContinuation -> Assertion)) (environment_tmr_signal_sem_post: TaskStackCallEnvironment) ,
  “ (pevent_pre = (tmr_signal_pointer (before_tmr_signal_sem_post))) ” 
  &&  “ (tmr_signal_profile sg_tmr_signal_sem_post ) ” 
  &&  “ (UCOS2_state_inv sg_tmr_signal_sem_post before_tmr_signal_sem_post ) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg_tmr_signal_sem_post))) ” 
  &&  “ (sem_post_api_call_input critical_tmr_signal_sem_post sg_tmr_signal_sem_post caller_tmr_signal_sem_post (tmr_signal_pointer (before_tmr_signal_sem_post)) before_tmr_signal_sem_post eid_tmr_signal_sem_post observed_tmr_signal_sem_post ) ” 
  &&  “ (tmr_signal_optional_event_layout sg_tmr_signal_sem_post (tmr_signal_pointer (before_tmr_signal_sem_post)) eid_tmr_signal_sem_post ) ” 
  &&  “ (sem_post_api_schedule_protocol environment_tmr_signal_sem_post critical_tmr_signal_sem_post sg_tmr_signal_sem_post caller_tmr_signal_sem_post mask_tmr_signal_sem_post (tmr_signal_pointer (before_tmr_signal_sem_post)) eid_tmr_signal_sem_post before_tmr_signal_sem_post ) ” 
  &&  “ (sem_post_api_safe environment_tmr_signal_sem_post critical_tmr_signal_sem_post sg_tmr_signal_sem_post caller_tmr_signal_sem_post mask_tmr_signal_sem_post (tmr_signal_pointer (before_tmr_signal_sem_post)) eid_tmr_signal_sem_post before_tmr_signal_sem_post X_tmr_signal_sem_post ) ” 
  &&  “ (os_sched_global_addresses sg_tmr_signal_sem_post ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> (tmr_signal_pointer (before_tmr_signal_sem_post)))
  **  (tmr_signal_read_frame environment_tmr_signal_sem_post saved_local_tmr_signal_sem_post sg_tmr_signal_sem_post caller_tmr_signal_sem_post mask_tmr_signal_sem_post before_tmr_signal_sem_post )
|--
EX (environment_sem_post_api: TaskStackCallEnvironment) (saved_local_sem_post_api: (Armv7aContinuation -> Assertion)) (critical_sem_post_api: CriticalRegionResources) (sg_sem_post_api: StableGlobVars) (caller_sem_post_api: TaskResumeCaller) (mask_sem_post_api: Z) (before_sem_post_api: UCOS2_Verify_State) (eid_sem_post_api: Z) (observed_sem_post_api: OSEventAbstractState) (pe_sem_post_api: Z) (X_sem_post_api: (Z -> (UCOS2_Verify_State -> Prop))) ,
  ((“ (pevent_pre = pe_sem_post_api) ” 
  &&  “ (sem_post_profile sg_sem_post_api ) ” 
  &&  “ (UCOS2_state_inv sg_sem_post_api before_sem_post_api ) ” 
  &&  “ (sem_post_api_call_input critical_sem_post_api sg_sem_post_api caller_sem_post_api pe_sem_post_api before_sem_post_api eid_sem_post_api observed_sem_post_api ) ” 
  &&  “ (event_object_layout_prop sg_sem_post_api eid_sem_post_api ) ” 
  &&  “ (sem_post_api_schedule_protocol environment_sem_post_api critical_sem_post_api sg_sem_post_api caller_sem_post_api mask_sem_post_api pe_sem_post_api eid_sem_post_api before_sem_post_api ) ” 
  &&  “ (sem_post_api_safe environment_sem_post_api critical_sem_post_api sg_sem_post_api caller_sem_post_api mask_sem_post_api pe_sem_post_api eid_sem_post_api before_sem_post_api X_sem_post_api ) ” 
  &&  “ (os_sched_global_addresses sg_sem_post_api ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_closed environment_sem_post_api critical_sem_post_api saved_local_sem_post_api sg_sem_post_api caller_sem_post_api mask_sem_post_api before_sem_post_api ))
  ||
  (“ (pevent_pre = pe_sem_post_api) ” 
  &&  “ (sem_post_profile sg_sem_post_api ) ” 
  &&  “ (UCOS2_state_inv sg_sem_post_api before_sem_post_api ) ” 
  &&  “ (sem_post_api_call_input critical_sem_post_api sg_sem_post_api caller_sem_post_api pe_sem_post_api before_sem_post_api eid_sem_post_api observed_sem_post_api ) ” 
  &&  “ (pevent_pre = 0) ” 
  &&  “ (sem_post_api_schedule_protocol environment_sem_post_api critical_sem_post_api sg_sem_post_api caller_sem_post_api mask_sem_post_api pe_sem_post_api eid_sem_post_api before_sem_post_api ) ” 
  &&  “ (sem_post_api_safe environment_sem_post_api critical_sem_post_api sg_sem_post_api caller_sem_post_api mask_sem_post_api pe_sem_post_api eid_sem_post_api before_sem_post_api X_sem_post_api ) ” 
  &&  “ (os_sched_global_addresses sg_sem_post_api ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_closed environment_sem_post_api critical_sem_post_api saved_local_sem_post_api sg_sem_post_api caller_sem_post_api mask_sem_post_api before_sem_post_api )))
  **
  ((EX retval_2,
  (sem_post_api_post environment_sem_post_api critical_sem_post_api saved_local_sem_post_api sg_sem_post_api caller_sem_post_api mask_sem_post_api pe_sem_post_api eid_sem_post_api before_sem_post_api retval_2 X_sem_post_api ))
  -*
  (EX retval,
  (sem_post_api_post environment_tmr_signal_sem_post critical_tmr_signal_sem_post saved_local_tmr_signal_sem_post sg_tmr_signal_sem_post caller_tmr_signal_sem_post mask_tmr_signal_sem_post (tmr_signal_pointer (before_tmr_signal_sem_post)) eid_tmr_signal_sem_post before_tmr_signal_sem_post retval X_tmr_signal_sem_post )))
.

Module Type VC_Correct.


Axiom proof_of_OSTmrSignal_return_wit_1 : OSTmrSignal_return_wit_1.
Axiom proof_of_OSTmrSignal_partial_solve_wit_1_pure : OSTmrSignal_partial_solve_wit_1_pure.
Axiom proof_of_OSTmrSignal_partial_solve_wit_1 : OSTmrSignal_partial_solve_wit_1.
Axiom proof_of_OSTmrSignal_partial_solve_wit_2_pure : OSTmrSignal_partial_solve_wit_2_pure.
Axiom proof_of_OSTmrSignal_partial_solve_wit_2 : OSTmrSignal_partial_solve_wit_2.
Axiom proof_of_OSTmrSignal_which_implies_wit_1 : OSTmrSignal_which_implies_wit_1.
Axiom proof_of_OSSemPost_derive_tmr_signal_sem_post_by_sem_post_api : OSSemPost_derive_tmr_signal_sem_post_by_sem_post_api.

End VC_Correct.
