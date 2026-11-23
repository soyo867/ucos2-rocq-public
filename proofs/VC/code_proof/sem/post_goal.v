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
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_api_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSSemPost -----*)

Definition OSSemPost_safety_wit_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = pe)) (PreH2 : (sem_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH5 : (event_object_layout_prop sg eid )) (PreH6 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH7 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemPost_safety_wit_2 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = pe)) (PreH2 : (sem_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH5 : (pevent_pre = 0)) (PreH6 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH7 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemPost_safety_wit_3 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH6 : (pevent_pre = 0)) (PreH7 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH8 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ False ”
.

Definition OSSemPost_safety_wit_4 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (sem_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (event_object_layout_prop sg eid )) (PreH15 : (sem_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (sem_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH25 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_save_result environment critical saved_local sg caller mask retval before eid observed )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemPost_safety_wit_5 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (sem_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (event_object_layout_prop sg eid )) (PreH17 : (sem_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (sem_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH27 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 1 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemPost_safety_wit_6 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH3 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_restore_post environment critical saved_local sg caller mask pe eid before 0 1 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemPost_safety_wit_7 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (current_2: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current_2)) < 65535)) (PreH2 : (0 <= (encode_event_cnt_value (current_2)))) (PreH3 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH4 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (event_object_layout_prop sg eid )) (PreH9 : (sem_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (sem_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH27 : (event_object_layout_prop sg eid )) (PreH28 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH29 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid before 0 0 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemPost_safety_wit_8 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (current_2: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current_2)) >= 65535)) (PreH2 : (0 <= (encode_event_cnt_value (current_2)))) (PreH3 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH4 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (event_object_layout_prop sg eid )) (PreH9 : (sem_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (sem_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH27 : (event_object_layout_prop sg eid )) (PreH28 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH29 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid before 51 0 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemPost_entail_wit_1 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (sem_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = pe)) (PreH10 : (sem_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH13 : (event_object_layout_prop sg eid )) (PreH14 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH15 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (sem_post_profile sg )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (pevent_pre = pe)) (PreH12 : (sem_post_profile sg )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH15 : (event_object_layout_prop sg eid )) (PreH16 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH17 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ”
  &&  emp
).

Definition OSSemPost_entail_wit_1_split_goal_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (sem_post_profile sg )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (pevent_pre = pe)) (PreH12 : (sem_post_profile sg )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH15 : (event_object_layout_prop sg eid )) (PreH16 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH17 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((event_slot_type_value ((EventState (before))) (eid)) <= 255)
.

Definition OSSemPost_entail_wit_1_split_goal_2 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (sem_post_profile sg )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (pevent_pre = pe)) (PreH12 : (sem_post_profile sg )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH15 : (event_object_layout_prop sg eid )) (PreH16 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH17 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (0 <= (event_slot_type_value ((EventState (before))) (eid)))
.

Definition OSSemPost_entail_wit_2 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (tid_2: Z) (old_2: TaskAbstractState) (retval_2: Z) (PreH1 : ((unsigned_last_nbits ((sem_post_group (acquired_2) (current_2))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (event_object_layout_prop sg eid )) (PreH6 : (sem_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (event_object_layout_prop sg eid )) (PreH16 : (sem_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (sem_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH24 : (event_object_layout_prop sg eid )) (PreH25 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH26 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (event_task_rdy_post sg (TskState (acquired_3)) eid current_3 tid_2 old_2 0 1 0 (q_post_sched_group (acquired_3)) (q_post_sched_rows (acquired_3)) retval_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (sem_post_api_wake_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 tid_2 old_2 )
|--
  EX (priority: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pe <> 0) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (sem_post_api_wake_context environment critical saved_local sg caller active mask retval before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old 0 1 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
.

Definition OSSemPost_return_wit_1 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (current_2: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current_2)) >= 65535)) (PreH2 : (0 <= (encode_event_cnt_value (current_2)))) (PreH3 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH4 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (event_object_layout_prop sg eid )) (PreH9 : (sem_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (sem_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH27 : (event_object_layout_prop sg eid )) (PreH28 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH29 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid before 51 0 )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 51 X )
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (current_2: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current_2)) >= 65535)) (PreH2 : (0 <= (encode_event_cnt_value (current_2)))) (PreH3 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH4 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (event_object_layout_prop sg eid )) (PreH9 : (sem_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (sem_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH27 : (event_object_layout_prop sg eid )) (PreH28 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH29 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid before 51 0 )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 51 X )
).

Definition OSSemPost_return_wit_1_split_goal_spatial := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (current_2: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current_2)) >= 65535)) (PreH2 : (0 <= (encode_event_cnt_value (current_2)))) (PreH3 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH4 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (event_object_layout_prop sg eid )) (PreH9 : (sem_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (sem_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH27 : (event_object_layout_prop sg eid )) (PreH28 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH29 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid before 51 0 )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 51 X )
.

Definition OSSemPost_return_wit_2 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (current_2: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current_2)) < 65535)) (PreH2 : (0 <= (encode_event_cnt_value (current_2)))) (PreH3 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH4 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (event_object_layout_prop sg eid )) (PreH9 : (sem_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (sem_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH27 : (event_object_layout_prop sg eid )) (PreH28 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH29 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid before 0 0 )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 0 X )
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (current_2: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current_2)) < 65535)) (PreH2 : (0 <= (encode_event_cnt_value (current_2)))) (PreH3 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH4 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (event_object_layout_prop sg eid )) (PreH9 : (sem_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (sem_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH27 : (event_object_layout_prop sg eid )) (PreH28 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH29 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid before 0 0 )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 0 X )
).

Definition OSSemPost_return_wit_2_split_goal_spatial := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (current_2: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current_2)) < 65535)) (PreH2 : (0 <= (encode_event_cnt_value (current_2)))) (PreH3 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH4 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (event_object_layout_prop sg eid )) (PreH9 : (sem_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (sem_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH27 : (event_object_layout_prop sg eid )) (PreH28 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH29 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid before 0 0 )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 0 X )
.

Definition OSSemPost_return_wit_3 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (sem_post_api_prefix_result environment critical sg caller mask pe eid before 0 1 returned restored )) (PreH2 : (pe <> 0)) (PreH3 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH4 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (sem_post_api_prefix_result environment critical sg caller mask pe eid before 0 1 returned restored )) (PreH2 : (pe <> 0)) (PreH3 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH4 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 0 X )
).

Definition OSSemPost_return_wit_3_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (sem_post_api_prefix_result environment critical sg caller mask pe eid before 0 1 returned restored )) (PreH2 : (pe <> 0)) (PreH3 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH4 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 0 X )
.

Definition OSSemPost_return_wit_4 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (sem_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH20 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 1 X )
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (sem_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH20 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 1 X )
).

Definition OSSemPost_return_wit_4_split_goal_spatial := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (sem_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH20 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 1 X )
.

Definition OSSemPost_return_wit_5 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH8 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 4 X )
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH8 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 4 X )
).

Definition OSSemPost_return_wit_5_split_goal_spatial := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH8 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 4 X )
.

Definition OSSemPost_return_wit_6 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH6 : (pevent_pre = 0)) (PreH7 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH8 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 4 X )
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH6 : (pevent_pre = 0)) (PreH7 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH8 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 4 X )
).

Definition OSSemPost_return_wit_6_split_goal_spatial := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH6 : (pevent_pre = 0)) (PreH7 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH8 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (sem_post_api_post environment critical saved_local sg caller mask pe eid before 4 X )
.

Definition OSSemPost_partial_solve_wit_1_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH8 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (event_object_layout_prop sg eid ) ”
.

Definition OSSemPost_partial_solve_wit_1_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH8 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_closed environment critical saved_local sg caller mask before )
.

Definition OSSemPost_partial_solve_wit_1 := OSSemPost_partial_solve_wit_1_pure -> OSSemPost_partial_solve_wit_1_aux.

Definition OSSemPost_partial_solve_wit_2_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (sem_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH20 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ”
.

Definition OSSemPost_partial_solve_wit_2_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (sem_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH20 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
.

Definition OSSemPost_partial_solve_wit_2 := OSSemPost_partial_solve_wit_2_pure -> OSSemPost_partial_solve_wit_2_aux.

Definition OSSemPost_partial_solve_wit_3 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (sem_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (event_object_layout_prop sg eid )) (PreH15 : (sem_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (sem_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH25 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_save_pre environment critical saved_local sg caller mask before pe eid observed )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (sem_post_api_save_pre environment critical saved_local sg caller mask before (event_addr (sg) (eid)) eid observed )
.

Definition OSSemPost_partial_solve_wit_4_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (sem_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (event_object_layout_prop sg eid )) (PreH15 : (sem_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (sem_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH25 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_save_result environment critical saved_local sg caller mask retval before eid observed )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ”
.

Definition OSSemPost_partial_solve_wit_4_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (sem_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (event_object_layout_prop sg eid )) (PreH15 : (sem_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (sem_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH23 : (event_object_layout_prop sg eid )) (PreH24 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH25 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_save_result environment critical saved_local sg caller mask retval before eid observed )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (sem_post_api_save_result environment critical saved_local sg caller mask retval before eid observed )
.

Definition OSSemPost_partial_solve_wit_4 := OSSemPost_partial_solve_wit_4_pure -> OSSemPost_partial_solve_wit_4_aux.

Definition OSSemPost_partial_solve_wit_5_pure := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (sem_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (event_object_layout_prop sg eid )) (PreH17 : (sem_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (sem_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH27 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (acquired) (current)))
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((sem_post_group (acquired) (current)) <> 0) ”
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (event_object_layout_prop sg eid )) (PreH8 : (sem_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (sem_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (sem_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH28 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (acquired) (current)))
|--
  “ ((sem_post_group (acquired) (current)) <> 0) ”
).

Definition OSSemPost_partial_solve_wit_5_pure_split_goal_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (event_object_layout_prop sg eid )) (PreH8 : (sem_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (sem_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (sem_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH28 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (acquired) (current)))
|--
  “ ((sem_post_group (acquired) (current)) <> 0) ”
.

Definition OSSemPost_partial_solve_wit_5_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (sem_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (event_object_layout_prop sg eid )) (PreH17 : (sem_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (sem_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH27 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (acquired) (current)))
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((sem_post_group (acquired) (current)) <> 0) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (sem_post_api_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (acquired) (current)))
.

Definition OSSemPost_partial_solve_wit_5 := OSSemPost_partial_solve_wit_5_pure -> OSSemPost_partial_solve_wit_5_aux.

Definition OSSemPost_partial_solve_wit_6_pure := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (sem_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (event_object_layout_prop sg eid )) (PreH17 : (sem_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (sem_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH27 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 1 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ”
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (event_object_layout_prop sg eid )) (PreH8 : (sem_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (sem_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (sem_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH28 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 1 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
).

Definition OSSemPost_partial_solve_wit_6_pure_split_goal_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (event_object_layout_prop sg eid )) (PreH8 : (sem_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (sem_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (sem_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH28 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 1 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ”
.

Definition OSSemPost_partial_solve_wit_6_pure_split_goal_2 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (event_object_layout_prop sg eid )) (PreH8 : (sem_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (sem_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (sem_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH28 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 1 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
.

Definition OSSemPost_partial_solve_wit_6_pure_split_goal_3 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (event_object_layout_prop sg eid )) (PreH8 : (sem_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (sem_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (sem_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH28 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 1 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
|--
  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
.

Definition OSSemPost_partial_solve_wit_6_pure_split_goal_4 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (event_object_layout_prop sg eid )) (PreH8 : (sem_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (sem_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (sem_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH28 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 1 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
|--
  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
.

Definition OSSemPost_partial_solve_wit_6_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (sem_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (event_object_layout_prop sg eid )) (PreH17 : (sem_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (sem_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH27 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 1 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 = 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 1 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  (sem_post_api_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
.

Definition OSSemPost_partial_solve_wit_6 := OSSemPost_partial_solve_wit_6_pure -> OSSemPost_partial_solve_wit_6_aux.

Definition OSSemPost_partial_solve_wit_7_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (priority: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH3 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (sem_post_api_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old 0 1 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
|--
  “ (pe <> 0) ”
.

Definition OSSemPost_partial_solve_wit_7_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (priority: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH3 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old 0 1 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
|--
  “ (pe <> 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (sem_post_api_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old 0 1 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
.

Definition OSSemPost_partial_solve_wit_7 := OSSemPost_partial_solve_wit_7_pure -> OSSemPost_partial_solve_wit_7_aux.

Definition OSSemPost_partial_solve_wit_8_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : (pe <> 0)) (PreH2 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH3 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (sem_post_api_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid before acquired released 0 1 )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSSemPost_partial_solve_wit_8_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : (pe <> 0)) (PreH2 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH3 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid before acquired released 0 1 )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (sem_post_api_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid before acquired released 0 1 )
.

Definition OSSemPost_partial_solve_wit_8 := OSSemPost_partial_solve_wit_8_pure -> OSSemPost_partial_solve_wit_8_aux.

Definition OSSemPost_partial_solve_wit_9_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH3 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_restore_post environment critical saved_local sg caller mask pe eid before 0 1 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ”
.

Definition OSSemPost_partial_solve_wit_9_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH3 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_restore_post environment critical saved_local sg caller mask pe eid before 0 1 )
|--
  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (sem_post_api_restore_post environment critical saved_local sg caller mask pe eid before 0 1 )
.

Definition OSSemPost_partial_solve_wit_9 := OSSemPost_partial_solve_wit_9_pure -> OSSemPost_partial_solve_wit_9_aux.

Definition OSSemPost_partial_solve_wit_10_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (sem_post_api_prefix_result environment critical sg caller mask pe eid before 0 1 returned restored )) (PreH2 : (pe <> 0)) (PreH3 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH4 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSSemPost_partial_solve_wit_10_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (sem_post_api_prefix_result environment critical sg caller mask pe eid before 0 1 returned restored )) (PreH2 : (pe <> 0)) (PreH3 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH4 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (sem_post_api_prefix_result environment critical sg caller mask pe eid before 0 1 returned restored ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
.

Definition OSSemPost_partial_solve_wit_10 := OSSemPost_partial_solve_wit_10_pure -> OSSemPost_partial_solve_wit_10_aux.

Definition OSSemPost_partial_solve_wit_11_pure := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (sem_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (event_object_layout_prop sg eid )) (PreH17 : (sem_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (sem_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH27 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (acquired) (current)))
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((sem_post_group (acquired) (current)) = 0) ”
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (event_object_layout_prop sg eid )) (PreH8 : (sem_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (sem_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (sem_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH28 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (acquired) (current)))
|--
  “ ((sem_post_group (acquired) (current)) = 0) ”
).

Definition OSSemPost_partial_solve_wit_11_pure_split_goal_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (event_object_layout_prop sg eid )) (PreH8 : (sem_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (event_object_layout_prop sg eid )) (PreH18 : (sem_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (sem_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH26 : (event_object_layout_prop sg eid )) (PreH27 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH28 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (acquired) (current)))
|--
  “ ((sem_post_group (acquired) (current)) = 0) ”
.

Definition OSSemPost_partial_solve_wit_11_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (event_object_layout_prop sg eid )) (PreH7 : (sem_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (event_object_layout_prop sg eid )) (PreH17 : (sem_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (sem_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH25 : (event_object_layout_prop sg eid )) (PreH26 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH27 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (acquired) (current)))
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((sem_post_group (acquired) (current)) = 0) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (sem_post_api_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (acquired) (current)))
.

Definition OSSemPost_partial_solve_wit_11 := OSSemPost_partial_solve_wit_11_pure -> OSSemPost_partial_solve_wit_11_aux.

Definition OSSemPost_partial_solve_wit_12_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current_2: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) < 65535)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (encode_event_cnt_value (current)))) (PreH4 : ((encode_event_cnt_value (current)) <= 65535)) (PreH5 : ((unsigned_last_nbits ((sem_post_group (acquired) (current_2))) (32)) = 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pe <> 0)) (PreH18 : (valid_event_id sg eid )) (PreH19 : (event_object_layout_prop sg eid )) (PreH20 : (sem_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (sem_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH28 : (event_object_layout_prop sg eid )) (PreH29 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH30 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_count_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((encode_event_cnt_value (current)) + 1 ))
|--
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= (encode_event_cnt_value (current))) ” 
  &&  “ ((encode_event_cnt_value (current)) < 65535) ”
.

Definition OSSemPost_partial_solve_wit_12_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current_2: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) < 65535)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (encode_event_cnt_value (current)))) (PreH4 : ((encode_event_cnt_value (current)) <= 65535)) (PreH5 : ((unsigned_last_nbits ((sem_post_group (acquired) (current_2))) (32)) = 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pe <> 0)) (PreH18 : (valid_event_id sg eid )) (PreH19 : (event_object_layout_prop sg eid )) (PreH20 : (sem_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (sem_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH28 : (event_object_layout_prop sg eid )) (PreH29 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH30 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (sem_post_api_count_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((encode_event_cnt_value (current)) + 1 ))
|--
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= (encode_event_cnt_value (current))) ” 
  &&  “ ((encode_event_cnt_value (current)) < 65535) ” 
  &&  “ ((encode_event_cnt_value (current)) < 65535) ” 
  &&  “ (0 <= (encode_event_cnt_value (current))) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 65535) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (acquired) (current_2))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (sem_post_api_count_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((encode_event_cnt_value (current)) + 1 ))
.

Definition OSSemPost_partial_solve_wit_12 := OSSemPost_partial_solve_wit_12_pure -> OSSemPost_partial_solve_wit_12_aux.

Definition OSSemPost_partial_solve_wit_13_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (current_2: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : ((encode_event_cnt_value (current_2)) < 65535)) (PreH2 : (0 <= (encode_event_cnt_value (current_2)))) (PreH3 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH4 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (event_object_layout_prop sg eid )) (PreH9 : (sem_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (sem_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH27 : (event_object_layout_prop sg eid )) (PreH28 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH29 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_restore_pre environment critical saved_local sg caller active mask retval pe eid before acquired_2 released 0 0 )
|--
  “ (retval = retval) ”
.

Definition OSSemPost_partial_solve_wit_13_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (current_2: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : ((encode_event_cnt_value (current_2)) < 65535)) (PreH2 : (0 <= (encode_event_cnt_value (current_2)))) (PreH3 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH4 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (event_object_layout_prop sg eid )) (PreH9 : (sem_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (sem_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH27 : (event_object_layout_prop sg eid )) (PreH28 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH29 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_restore_pre environment critical saved_local sg caller active mask retval pe eid before acquired_2 released 0 0 )
|--
  “ (retval = retval) ” 
  &&  “ ((encode_event_cnt_value (current_2)) < 65535) ” 
  &&  “ (0 <= (encode_event_cnt_value (current_2))) ” 
  &&  “ ((encode_event_cnt_value (current_2)) <= 65535) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (sem_post_api_restore_pre environment critical saved_local sg caller active mask retval (event_addr (sg) (eid)) eid before acquired_2 released 0 0 )
.

Definition OSSemPost_partial_solve_wit_13 := OSSemPost_partial_solve_wit_13_pure -> OSSemPost_partial_solve_wit_13_aux.

Definition OSSemPost_partial_solve_wit_14_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current_2: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) >= 65535)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (encode_event_cnt_value (current)))) (PreH4 : ((encode_event_cnt_value (current)) <= 65535)) (PreH5 : ((unsigned_last_nbits ((sem_post_group (acquired) (current_2))) (32)) = 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pe <> 0)) (PreH18 : (valid_event_id sg eid )) (PreH19 : (event_object_layout_prop sg eid )) (PreH20 : (sem_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (sem_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH28 : (event_object_layout_prop sg eid )) (PreH29 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH30 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_count_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
|--
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_cnt_value (current)) >= 65535) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 65535) ”
.

Definition OSSemPost_partial_solve_wit_14_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current_2: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) >= 65535)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (encode_event_cnt_value (current)))) (PreH4 : ((encode_event_cnt_value (current)) <= 65535)) (PreH5 : ((unsigned_last_nbits ((sem_post_group (acquired) (current_2))) (32)) = 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (event_object_layout_prop sg eid )) (PreH10 : (sem_post_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pe <> 0)) (PreH18 : (valid_event_id sg eid )) (PreH19 : (event_object_layout_prop sg eid )) (PreH20 : (sem_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (sem_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH28 : (event_object_layout_prop sg eid )) (PreH29 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH30 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (sem_post_api_count_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
|--
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_cnt_value (current)) >= 65535) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 65535) ” 
  &&  “ ((encode_event_cnt_value (current)) >= 65535) ” 
  &&  “ (0 <= (encode_event_cnt_value (current))) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 65535) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (acquired) (current_2))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (sem_post_api_count_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
.

Definition OSSemPost_partial_solve_wit_14 := OSSemPost_partial_solve_wit_14_pure -> OSSemPost_partial_solve_wit_14_aux.

Definition OSSemPost_partial_solve_wit_15_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (current_2: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : ((encode_event_cnt_value (current_2)) >= 65535)) (PreH2 : (0 <= (encode_event_cnt_value (current_2)))) (PreH3 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH4 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (event_object_layout_prop sg eid )) (PreH9 : (sem_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (sem_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH27 : (event_object_layout_prop sg eid )) (PreH28 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH29 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (sem_post_api_restore_pre environment critical saved_local sg caller active mask retval pe eid before acquired_2 released 51 0 )
|--
  “ (retval = retval) ”
.

Definition OSSemPost_partial_solve_wit_15_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (current_2: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : ((encode_event_cnt_value (current_2)) >= 65535)) (PreH2 : (0 <= (encode_event_cnt_value (current_2)))) (PreH3 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH4 : ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (event_object_layout_prop sg eid )) (PreH9 : (sem_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (event_object_layout_prop sg eid )) (PreH19 : (sem_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (sem_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH27 : (event_object_layout_prop sg eid )) (PreH28 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) (PreH29 : (sem_post_api_safe environment critical sg caller mask pe eid before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (sem_post_api_restore_pre environment critical saved_local sg caller active mask retval pe eid before acquired_2 released 51 0 )
|--
  “ (retval = retval) ” 
  &&  “ ((encode_event_cnt_value (current_2)) >= 65535) ” 
  &&  “ (0 <= (encode_event_cnt_value (current_2))) ” 
  &&  “ ((encode_event_cnt_value (current_2)) <= 65535) ” 
  &&  “ ((unsigned_last_nbits ((sem_post_group (acquired) (current))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ) ” 
  &&  “ (sem_post_api_safe environment critical sg caller mask pe eid before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (sem_post_api_restore_pre environment critical saved_local sg caller active mask retval (event_addr (sg) (eid)) eid before acquired_2 released 51 0 )
.

Definition OSSemPost_partial_solve_wit_15 := OSSemPost_partial_solve_wit_15_pure -> OSSemPost_partial_solve_wit_15_aux.

Definition OSSemPost_which_implies_wit_1 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (sem_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH5 : (event_object_layout_prop sg eid )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (sem_post_api_call_input critical sg caller pe before eid observed ) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (sem_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH5 : (event_object_layout_prop sg eid )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
).

Definition OSSemPost_which_implies_wit_1_split_goal_1 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (sem_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH5 : (event_object_layout_prop sg eid )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (valid_event_id sg eid ) ”
.

Definition OSSemPost_which_implies_wit_1_split_goal_2 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (sem_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH5 : (event_object_layout_prop sg eid )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSSemPost_which_implies_wit_1_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (sem_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH5 : (event_object_layout_prop sg eid )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
.

Definition OSSemPost_which_implies_wit_2 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (sem_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (event_object_layout_prop sg eid ) ” 
  &&  “ (sem_post_profile sg ) ”
  &&  (sem_post_api_save_pre environment critical saved_local sg caller mask before pe eid observed )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (sem_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  (sem_post_api_save_pre environment critical saved_local sg caller mask before pe eid observed )
).

Definition OSSemPost_which_implies_wit_2_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (event_object_layout_prop sg eid )) (PreH5 : (sem_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (sem_post_api_call_input critical sg caller pe before eid observed )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  (sem_post_api_save_pre environment critical saved_local sg caller mask before pe eid observed )
.

Definition OSSemPost_which_implies_wit_3 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (valid_event_id sg eid )) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (sem_post_profile sg )) ,
  (sem_post_api_save_result environment critical saved_local sg caller mask cpu_sr before eid observed )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (sem_post_api_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (acquired) (current)))
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (valid_event_id sg eid )) (PreH3 : (event_object_layout_prop sg eid )) (PreH4 : (sem_post_profile sg )) ,
  (sem_post_api_save_result environment critical saved_local sg caller mask cpu_sr before eid observed )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (sem_post_api_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (acquired) (current)))
).

Definition OSSemPost_which_implies_wit_4 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((sem_post_group (acquired_2) (current_2)) <> 0)) ,
  (sem_post_api_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (acquired_2) (current_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (sem_post_api_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current tid old )
  **  (event_task_rdy_pre sg (TskState (acquired)) eid current tid old 1 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((sem_post_group (acquired_2) (current_2)) <> 0)) ,
  (sem_post_api_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (acquired_2) (current_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (sem_post_api_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current tid old )
  **  (event_task_rdy_pre sg (TskState (acquired)) eid current tid old 1 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) )
).

Definition OSSemPost_which_implies_wit_5 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe <> 0)) ,
  (sem_post_api_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired_2)) eid current tid old 0 1 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (sem_post_api_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid before acquired released 0 1 )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe <> 0)) ,
  (sem_post_api_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired_2)) eid current tid old 0 1 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (sem_post_api_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid before acquired released 0 1 )
).

Definition OSSemPost_which_implies_wit_6 := 
(
forall (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) ,
  (sem_post_api_restore_post environment critical saved_local sg caller mask pe eid before 0 1 )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (sem_post_api_prefix_result environment critical sg caller mask pe eid before 0 1 returned restored ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
) \/
(
forall (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (sem_post_api_schedule_protocol environment critical sg caller mask pe eid before )) ,
  (sem_post_api_restore_post environment critical saved_local sg caller mask pe eid before 0 1 )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (sem_post_api_prefix_result environment critical sg caller mask pe eid before 0 1 returned restored ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
).

Definition OSSemPost_which_implies_wit_7 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((sem_post_group (acquired_2) (current_2)) = 0)) ,
  (sem_post_api_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (acquired_2) (current_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= (encode_event_cnt_value (current))) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 65535) ”
  &&  (sem_post_api_count_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((sem_post_group (acquired_2) (current_2)) = 0)) ,
  (sem_post_api_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (sem_post_group (acquired_2) (current_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= (encode_event_cnt_value (current))) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 65535) ”
  &&  (sem_post_api_count_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
).

Definition OSSemPost_which_implies_wit_8 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= (encode_event_cnt_value (current)))) (PreH4 : ((encode_event_cnt_value (current)) < 65535)) ,
  (sem_post_api_count_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((encode_event_cnt_value (current)) + 1 ))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (sem_post_api_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid before acquired released 0 0 )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= (encode_event_cnt_value (current)))) (PreH4 : ((encode_event_cnt_value (current)) < 65535)) ,
  (sem_post_api_count_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((encode_event_cnt_value (current)) + 1 ))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (sem_post_api_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid before acquired released 0 0 )
).

Definition OSSemPost_which_implies_wit_9 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((encode_event_cnt_value (current)) >= 65535)) (PreH4 : ((encode_event_cnt_value (current)) <= 65535)) ,
  (sem_post_api_count_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (sem_post_api_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid before acquired released 51 0 )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((encode_event_cnt_value (current)) >= 65535)) (PreH4 : ((encode_event_cnt_value (current)) <= 65535)) ,
  (sem_post_api_count_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (sem_post_api_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid before acquired released 51 0 )
).

Module Type VC_Correct.


Axiom proof_of_OSSemPost_safety_wit_1 : OSSemPost_safety_wit_1.
Axiom proof_of_OSSemPost_safety_wit_2 : OSSemPost_safety_wit_2.
Axiom proof_of_OSSemPost_safety_wit_3 : OSSemPost_safety_wit_3.
Axiom proof_of_OSSemPost_safety_wit_4 : OSSemPost_safety_wit_4.
Axiom proof_of_OSSemPost_safety_wit_5 : OSSemPost_safety_wit_5.
Axiom proof_of_OSSemPost_safety_wit_6 : OSSemPost_safety_wit_6.
Axiom proof_of_OSSemPost_safety_wit_7 : OSSemPost_safety_wit_7.
Axiom proof_of_OSSemPost_safety_wit_8 : OSSemPost_safety_wit_8.
Axiom proof_of_OSSemPost_entail_wit_1 : OSSemPost_entail_wit_1.
Axiom proof_of_OSSemPost_entail_wit_2 : OSSemPost_entail_wit_2.
Axiom proof_of_OSSemPost_return_wit_1 : OSSemPost_return_wit_1.
Axiom proof_of_OSSemPost_return_wit_2 : OSSemPost_return_wit_2.
Axiom proof_of_OSSemPost_return_wit_3 : OSSemPost_return_wit_3.
Axiom proof_of_OSSemPost_return_wit_4 : OSSemPost_return_wit_4.
Axiom proof_of_OSSemPost_return_wit_5 : OSSemPost_return_wit_5.
Axiom proof_of_OSSemPost_return_wit_6 : OSSemPost_return_wit_6.
Axiom proof_of_OSSemPost_partial_solve_wit_1_pure : OSSemPost_partial_solve_wit_1_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_1 : OSSemPost_partial_solve_wit_1.
Axiom proof_of_OSSemPost_partial_solve_wit_2_pure : OSSemPost_partial_solve_wit_2_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_2 : OSSemPost_partial_solve_wit_2.
Axiom proof_of_OSSemPost_partial_solve_wit_3 : OSSemPost_partial_solve_wit_3.
Axiom proof_of_OSSemPost_partial_solve_wit_4_pure : OSSemPost_partial_solve_wit_4_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_4 : OSSemPost_partial_solve_wit_4.
Axiom proof_of_OSSemPost_partial_solve_wit_5_pure : OSSemPost_partial_solve_wit_5_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_5 : OSSemPost_partial_solve_wit_5.
Axiom proof_of_OSSemPost_partial_solve_wit_6_pure : OSSemPost_partial_solve_wit_6_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_6 : OSSemPost_partial_solve_wit_6.
Axiom proof_of_OSSemPost_partial_solve_wit_7_pure : OSSemPost_partial_solve_wit_7_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_7 : OSSemPost_partial_solve_wit_7.
Axiom proof_of_OSSemPost_partial_solve_wit_8_pure : OSSemPost_partial_solve_wit_8_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_8 : OSSemPost_partial_solve_wit_8.
Axiom proof_of_OSSemPost_partial_solve_wit_9_pure : OSSemPost_partial_solve_wit_9_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_9 : OSSemPost_partial_solve_wit_9.
Axiom proof_of_OSSemPost_partial_solve_wit_10_pure : OSSemPost_partial_solve_wit_10_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_10 : OSSemPost_partial_solve_wit_10.
Axiom proof_of_OSSemPost_partial_solve_wit_11_pure : OSSemPost_partial_solve_wit_11_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_11 : OSSemPost_partial_solve_wit_11.
Axiom proof_of_OSSemPost_partial_solve_wit_12_pure : OSSemPost_partial_solve_wit_12_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_12 : OSSemPost_partial_solve_wit_12.
Axiom proof_of_OSSemPost_partial_solve_wit_13_pure : OSSemPost_partial_solve_wit_13_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_13 : OSSemPost_partial_solve_wit_13.
Axiom proof_of_OSSemPost_partial_solve_wit_14_pure : OSSemPost_partial_solve_wit_14_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_14 : OSSemPost_partial_solve_wit_14.
Axiom proof_of_OSSemPost_partial_solve_wit_15_pure : OSSemPost_partial_solve_wit_15_pure.
Axiom proof_of_OSSemPost_partial_solve_wit_15 : OSSemPost_partial_solve_wit_15.
Axiom proof_of_OSSemPost_which_implies_wit_1 : OSSemPost_which_implies_wit_1.
Axiom proof_of_OSSemPost_which_implies_wit_2 : OSSemPost_which_implies_wit_2.
Axiom proof_of_OSSemPost_which_implies_wit_3 : OSSemPost_which_implies_wit_3.
Axiom proof_of_OSSemPost_which_implies_wit_4 : OSSemPost_which_implies_wit_4.
Axiom proof_of_OSSemPost_which_implies_wit_5 : OSSemPost_which_implies_wit_5.
Axiom proof_of_OSSemPost_which_implies_wit_6 : OSSemPost_which_implies_wit_6.
Axiom proof_of_OSSemPost_which_implies_wit_7 : OSSemPost_which_implies_wit_7.
Axiom proof_of_OSSemPost_which_implies_wit_8 : OSSemPost_which_implies_wit_8.
Axiom proof_of_OSSemPost_which_implies_wit_9 : OSSemPost_which_implies_wit_9.

End VC_Correct.
