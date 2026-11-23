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
Require Import Ucos2Verify.VC.code.queue.spec.q_post_api_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSQPost -----*)

Definition OSQPost_safety_wit_1 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = pe)) (PreH2 : (pmsg_pre = message)) (PreH3 : (q_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (q_post_call_input critical sg caller pe before eid observed )) (PreH6 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH7 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPost_safety_wit_2 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (pmsg_pre = message)) (PreH19 : (q_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (q_post_call_input critical sg caller pe before eid observed )) (PreH22 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH23 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH24 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_save_result environment critical saved_local sg caller mask retval before eid observed )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPost_safety_wit_3 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH3 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 1 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPost_safety_wit_4 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (q_2: QueueFields) (PreH1 : ((queue_entries (q_2)) >= (qSize (q_2)))) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (0 <= (qSize (q_2)))) (PreH5 : ((qSize (q_2)) <= 65535)) (PreH6 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (q_post_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pe <> 0)) (PreH18 : (valid_event_id sg eid )) (PreH19 : (q_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (q_post_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message before 30 0 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPost_safety_wit_5 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q: QueueFields) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q)) < (qSize (q)))) (PreH2 : (pe <> 0)) (PreH3 : (q_post_safe environment critical sg caller mask pe eid message before X )) ,
  (q_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 0 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pq" ) )) # Ptr  |-> pq)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPost_entail_wit_1 := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : (pevent_pre <> 0)) (PreH8 : (pevent_pre = pe)) (PreH9 : (pmsg_pre = message)) (PreH10 : (q_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (q_post_call_input critical sg caller pe before eid observed )) (PreH13 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH14 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (q_post_call_input critical sg caller pe before eid observed )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (pmsg_pre = message)) (PreH12 : (q_post_profile sg )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (q_post_call_input critical sg caller pe before eid observed )) (PreH15 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH16 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ”
  &&  emp
).

Definition OSQPost_entail_wit_1_split_goal_1 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (q_post_call_input critical sg caller pe before eid observed )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (pmsg_pre = message)) (PreH12 : (q_post_profile sg )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (q_post_call_input critical sg caller pe before eid observed )) (PreH15 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH16 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((event_slot_type_value ((EventState (before))) (eid)) <= 255)
.

Definition OSQPost_entail_wit_1_split_goal_2 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (q_post_call_input critical sg caller pe before eid observed )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (pmsg_pre = message)) (PreH12 : (q_post_profile sg )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (q_post_call_input critical sg caller pe before eid observed )) (PreH15 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH16 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (0 <= (event_slot_type_value ((EventState (before))) (eid)))
.

Definition OSQPost_entail_wit_2 := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (tid_2: Z) (old_2: TaskAbstractState) (retval_2: Z) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_post_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (pmsg_pre = message)) (PreH20 : (q_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (q_post_call_input critical sg caller pe before eid observed )) (PreH23 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH24 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (event_task_rdy_post sg (TskState (acquired_3)) eid current_3 tid_2 old_2 pmsg_pre 4 0 (q_post_sched_group (acquired_3)) (q_post_sched_rows (acquired_3)) retval_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_post_wake_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 tid_2 old_2 )
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  EX (priority: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pe <> 0) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 4 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (tid_2: Z) (old_2: TaskAbstractState) (retval_2: Z) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_post_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (pmsg_pre = message)) (PreH20 : (q_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (q_post_call_input critical sg caller pe before eid observed )) (PreH23 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH24 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (event_task_rdy_post sg (TskState (acquired_3)) eid current_3 tid_2 old_2 pmsg_pre 4 0 (q_post_sched_group (acquired_3)) (q_post_sched_rows (acquired_3)) retval_2 )
  **  (q_post_wake_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 tid_2 old_2 )
|--
  EX (priority: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pmsg_pre = message) ” 
  &&  “ ((event_addr (sg) (eid)) = pe) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 4 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
).

Definition OSQPost_entail_wit_3_1 := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (q_3: QueueFields) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (q_4: QueueFields) (PreH1 : (((queue_in_addr (q_4)) + (1 * sizeof(PTR))) = (queue_end_addr (q_4)))) (PreH2 : (0 <= (queue_entries (q_4)))) (PreH3 : ((queue_entries (q_4)) < 65535)) (PreH4 : (((queue_in_addr (q_4)) + 4 ) <= (queue_end_addr (q_4)))) (PreH5 : ((queue_entries (q_3)) < (qSize (q_3)))) (PreH6 : (0 <= (queue_entries (q_3)))) (PreH7 : ((queue_entries (q_3)) <= 65535)) (PreH8 : (0 <= (qSize (q_3)))) (PreH9 : ((qSize (q_3)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) = 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (pe <> 0)) (PreH22 : (valid_event_id sg eid )) (PreH23 : (q_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (q_post_call_input critical sg caller pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (pmsg_pre = message)) (PreH29 : (q_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (q_post_call_input critical sg caller pe before eid observed )) (PreH32 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH33 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 q_4 free_2 slots_2 (qcb_addr (sg) ((qID (q)))) )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (qStart (q_4)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q_4)) + 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_4)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_4)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_4)))
  **  (q_post_qcb_readonly (qcb_addr (sg) ((qID (q)))) q_4 )
  **  (((queue_in_addr (q_4))) # Ptr  |-> pmsg_pre)
  **  (q_post_slot_frame q_4 slots_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q_2: QueueFields) ,
  “ ((queue_entries (q_2)) < (qSize (q_2))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ”
  &&  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired eid observed current q_2 free slots (qcb_addr (sg) ((qID (q)))) )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (q_post_next_in (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q_2)) + 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  (q_post_qcb_readonly (qcb_addr (sg) ((qID (q)))) q_2 )
  **  (((queue_in_addr (q_2))) # Ptr  |-> message)
  **  (q_post_slot_frame q_2 slots )
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (q_3: QueueFields) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (q_4: QueueFields) (PreH1 : (((queue_in_addr (q_4)) + (1 * sizeof(PTR))) = (queue_end_addr (q_4)))) (PreH2 : (0 <= (queue_entries (q_4)))) (PreH3 : ((queue_entries (q_4)) < 65535)) (PreH4 : (((queue_in_addr (q_4)) + 4 ) <= (queue_end_addr (q_4)))) (PreH5 : ((queue_entries (q_3)) < (qSize (q_3)))) (PreH6 : (0 <= (queue_entries (q_3)))) (PreH7 : ((queue_entries (q_3)) <= 65535)) (PreH8 : (0 <= (qSize (q_3)))) (PreH9 : ((qSize (q_3)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) = 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (pe <> 0)) (PreH22 : (valid_event_id sg eid )) (PreH23 : (q_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (q_post_call_input critical sg caller pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (pmsg_pre = message)) (PreH29 : (q_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (q_post_call_input critical sg caller pe before eid observed )) (PreH32 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH33 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 q_4 free_2 slots_2 (qcb_addr (sg) ((qID (q)))) )
  **  (q_post_qcb_readonly (qcb_addr (sg) ((qID (q)))) q_4 )
  **  (((queue_in_addr (q_4))) # Ptr  |-> pmsg_pre)
  **  (q_post_slot_frame q_4 slots_2 )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q_2: QueueFields) ,
  “ (pmsg_pre = message) ” 
  &&  “ ((event_addr (sg) (eid)) = pe) ” 
  &&  “ ((qStart (q_4)) = (qStart (q_2))) ” 
  &&  “ ((queue_end_addr (q_4)) = (queue_end_addr (q_2))) ” 
  &&  “ ((qSize (q_4)) = (qSize (q_2))) ” 
  &&  “ (((queue_entries (q_4)) + 1 ) = ((queue_entries (q_2)) + 1 )) ” 
  &&  “ ((qStart (q_4)) = (q_post_next_in (q_2))) ” 
  &&  “ ((queue_entries (q_2)) < (qSize (q_2))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ”
  &&  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired eid observed current q_2 free slots (qcb_addr (sg) ((qID (q)))) )
  **  (q_post_qcb_readonly (qcb_addr (sg) ((qID (q)))) q_2 )
  **  (((queue_in_addr (q_2))) # Ptr  |-> message)
  **  (q_post_slot_frame q_2 slots )
).

Definition OSQPost_entail_wit_3_2 := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (q_3: QueueFields) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (q_4: QueueFields) (PreH1 : (((queue_in_addr (q_4)) + (1 * sizeof(PTR))) <> (queue_end_addr (q_4)))) (PreH2 : (0 <= (queue_entries (q_4)))) (PreH3 : ((queue_entries (q_4)) < 65535)) (PreH4 : (((queue_in_addr (q_4)) + 4 ) <= (queue_end_addr (q_4)))) (PreH5 : ((queue_entries (q_3)) < (qSize (q_3)))) (PreH6 : (0 <= (queue_entries (q_3)))) (PreH7 : ((queue_entries (q_3)) <= 65535)) (PreH8 : (0 <= (qSize (q_3)))) (PreH9 : ((qSize (q_3)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) = 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (pe <> 0)) (PreH22 : (valid_event_id sg eid )) (PreH23 : (q_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (q_post_call_input critical sg caller pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (pmsg_pre = message)) (PreH29 : (q_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (q_post_call_input critical sg caller pe before eid observed )) (PreH32 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH33 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 q_4 free_2 slots_2 (qcb_addr (sg) ((qID (q)))) )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> ((queue_in_addr (q_4)) + (1 * sizeof(PTR))))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q_4)) + 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_4)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_4)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_4)))
  **  (q_post_qcb_readonly (qcb_addr (sg) ((qID (q)))) q_4 )
  **  (((queue_in_addr (q_4))) # Ptr  |-> pmsg_pre)
  **  (q_post_slot_frame q_4 slots_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q_2: QueueFields) ,
  “ ((queue_entries (q_2)) < (qSize (q_2))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ”
  &&  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired eid observed current q_2 free slots (qcb_addr (sg) ((qID (q)))) )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (q_post_next_in (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q_2)) + 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  (q_post_qcb_readonly (qcb_addr (sg) ((qID (q)))) q_2 )
  **  (((queue_in_addr (q_2))) # Ptr  |-> message)
  **  (q_post_slot_frame q_2 slots )
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (q_3: QueueFields) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (q_4: QueueFields) (PreH1 : (((queue_in_addr (q_4)) + (1 * sizeof(PTR))) <> (queue_end_addr (q_4)))) (PreH2 : (0 <= (queue_entries (q_4)))) (PreH3 : ((queue_entries (q_4)) < 65535)) (PreH4 : (((queue_in_addr (q_4)) + 4 ) <= (queue_end_addr (q_4)))) (PreH5 : ((queue_entries (q_3)) < (qSize (q_3)))) (PreH6 : (0 <= (queue_entries (q_3)))) (PreH7 : ((queue_entries (q_3)) <= 65535)) (PreH8 : (0 <= (qSize (q_3)))) (PreH9 : ((qSize (q_3)) <= 65535)) (PreH10 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) = 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (pe <> 0)) (PreH22 : (valid_event_id sg eid )) (PreH23 : (q_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (q_post_call_input critical sg caller pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (pmsg_pre = message)) (PreH29 : (q_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (q_post_call_input critical sg caller pe before eid observed )) (PreH32 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH33 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 q_4 free_2 slots_2 (qcb_addr (sg) ((qID (q)))) )
  **  (q_post_qcb_readonly (qcb_addr (sg) ((qID (q)))) q_4 )
  **  (((queue_in_addr (q_4))) # Ptr  |-> pmsg_pre)
  **  (q_post_slot_frame q_4 slots_2 )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q_2: QueueFields) ,
  “ (pmsg_pre = message) ” 
  &&  “ ((event_addr (sg) (eid)) = pe) ” 
  &&  “ ((qStart (q_4)) = (qStart (q_2))) ” 
  &&  “ ((queue_end_addr (q_4)) = (queue_end_addr (q_2))) ” 
  &&  “ ((qSize (q_4)) = (qSize (q_2))) ” 
  &&  “ (((queue_entries (q_4)) + 1 ) = ((queue_entries (q_2)) + 1 )) ” 
  &&  “ (((queue_in_addr (q_4)) + (1 * sizeof(PTR))) = (q_post_next_in (q_2))) ” 
  &&  “ ((queue_entries (q_2)) < (qSize (q_2))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ”
  &&  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired eid observed current q_2 free slots (qcb_addr (sg) ((qID (q)))) )
  **  (q_post_qcb_readonly (qcb_addr (sg) ((qID (q)))) q_2 )
  **  (((queue_in_addr (q_2))) # Ptr  |-> message)
  **  (q_post_slot_frame q_2 slots )
).

Definition OSQPost_return_wit_1 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q: QueueFields) (PreH1 : ((queue_entries (q)) < (qSize (q)))) (PreH2 : (pe <> 0)) (PreH3 : (q_post_safe environment critical sg caller mask pe eid message before X )) ,
  (q_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 0 )
|--
  (q_post_post environment critical saved_local sg caller mask pe eid message before 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q: QueueFields) (PreH1 : ((queue_entries (q)) < (qSize (q)))) (PreH2 : (pe <> 0)) (PreH3 : (q_post_safe environment critical sg caller mask pe eid message before X )) ,
  (q_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 0 )
|--
  (q_post_post environment critical saved_local sg caller mask pe eid message before 0 X )
).

Definition OSQPost_return_wit_1_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q: QueueFields) (PreH1 : ((queue_entries (q)) < (qSize (q)))) (PreH2 : (pe <> 0)) (PreH3 : (q_post_safe environment critical sg caller mask pe eid message before X )) ,
  (q_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 0 )
|--
  (q_post_post environment critical saved_local sg caller mask pe eid message before 0 X )
.

Definition OSQPost_return_wit_2 := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (PreH1 : ((queue_entries (q)) >= (qSize (q)))) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (0 <= (qSize (q)))) (PreH5 : ((qSize (q)) <= 65535)) (PreH6 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (q_post_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pe <> 0)) (PreH18 : (valid_event_id sg eid )) (PreH19 : (q_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (q_post_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message before 30 0 )
|--
  (q_post_post environment critical saved_local sg caller mask pe eid message before 30 X )
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (PreH1 : ((queue_entries (q)) >= (qSize (q)))) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (0 <= (qSize (q)))) (PreH5 : ((qSize (q)) <= 65535)) (PreH6 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (q_post_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pe <> 0)) (PreH18 : (valid_event_id sg eid )) (PreH19 : (q_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (q_post_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message before 30 0 )
|--
  (q_post_post environment critical saved_local sg caller mask pe eid message before 30 X )
).

Definition OSQPost_return_wit_2_split_goal_spatial := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (PreH1 : ((queue_entries (q)) >= (qSize (q)))) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (0 <= (qSize (q)))) (PreH5 : ((qSize (q)) <= 65535)) (PreH6 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (q_post_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pe <> 0)) (PreH18 : (valid_event_id sg eid )) (PreH19 : (q_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (q_post_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message before 30 0 )
|--
  (q_post_post environment critical saved_local sg caller mask pe eid message before 30 X )
.

Definition OSQPost_return_wit_3 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (q_post_prefix_result environment critical sg caller mask pe eid message before 0 1 returned restored )) (PreH2 : (pe <> 0)) (PreH3 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH4 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (q_post_post environment critical saved_local sg caller mask pe eid message before 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (q_post_prefix_result environment critical sg caller mask pe eid message before 0 1 returned restored )) (PreH2 : (pe <> 0)) (PreH3 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH4 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (q_post_post environment critical saved_local sg caller mask pe eid message before 0 X )
).

Definition OSQPost_return_wit_3_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (q_post_prefix_result environment critical sg caller mask pe eid message before 0 1 returned restored )) (PreH2 : (pe <> 0)) (PreH3 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH4 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (q_post_post environment critical saved_local sg caller mask pe eid message before 0 X )
.

Definition OSQPost_return_wit_4 := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_post_call_input critical sg caller pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (pmsg_pre = message)) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH19 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  (q_post_post environment critical saved_local sg caller mask pe eid message before 1 X )
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_post_call_input critical sg caller pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (pmsg_pre = message)) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH19 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  (q_post_post environment critical saved_local sg caller mask pe eid message before 1 X )
).

Definition OSQPost_return_wit_4_split_goal_spatial := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_post_call_input critical sg caller pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (pmsg_pre = message)) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH19 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  (q_post_post environment critical saved_local sg caller mask pe eid message before 1 X )
.

Definition OSQPost_return_wit_5 := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (pmsg_pre = message)) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH8 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (q_post_post environment critical saved_local sg caller mask pe eid message before 4 X )
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (pmsg_pre = message)) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH8 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (q_post_post environment critical saved_local sg caller mask pe eid message before 4 X )
).

Definition OSQPost_return_wit_5_split_goal_spatial := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (pmsg_pre = message)) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH8 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (q_post_post environment critical saved_local sg caller mask pe eid message before 4 X )
.

Definition OSQPost_partial_solve_wit_1_pure := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (pmsg_pre = message)) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH8 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ”
.

Definition OSQPost_partial_solve_wit_1_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (pmsg_pre = message)) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH8 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_closed environment critical saved_local sg caller mask before )
.

Definition OSQPost_partial_solve_wit_1 := OSQPost_partial_solve_wit_1_pure -> OSQPost_partial_solve_wit_1_aux.

Definition OSQPost_partial_solve_wit_2_pure := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_post_call_input critical sg caller pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (pmsg_pre = message)) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH19 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ”
.

Definition OSQPost_partial_solve_wit_2_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_post_call_input critical sg caller pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (pmsg_pre = message)) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH19 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
.

Definition OSQPost_partial_solve_wit_2 := OSQPost_partial_solve_wit_2_pure -> OSQPost_partial_solve_wit_2_aux.

Definition OSQPost_partial_solve_wit_3 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (pmsg_pre = message)) (PreH19 : (q_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (q_post_call_input critical sg caller pe before eid observed )) (PreH22 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH23 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH24 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_save_pre environment critical saved_local sg caller mask before pe eid observed )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_save_pre environment critical saved_local sg caller mask before (event_addr (sg) (eid)) eid observed )
.

Definition OSQPost_partial_solve_wit_4_pure := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (pmsg_pre = message)) (PreH19 : (q_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (q_post_call_input critical sg caller pe before eid observed )) (PreH22 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH23 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH24 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_save_result environment critical saved_local sg caller mask retval before eid observed )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ”
.

Definition OSQPost_partial_solve_wit_4_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (pmsg_pre = message)) (PreH19 : (q_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (q_post_call_input critical sg caller pe before eid observed )) (PreH22 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH23 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH24 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_save_result environment critical saved_local sg caller mask retval before eid observed )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_post_save_result environment critical saved_local sg caller mask retval before eid observed )
.

Definition OSQPost_partial_solve_wit_4 := OSQPost_partial_solve_wit_4_pure -> OSQPost_partial_solve_wit_4_aux.

Definition OSQPost_partial_solve_wit_5_pure := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (pmsg_pre = message)) (PreH21 : (q_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (q_post_call_input critical sg caller pe before eid observed )) (PreH24 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH25 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) <> 0) ”
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_post_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (pmsg_pre = message)) (PreH22 : (q_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_post_call_input critical sg caller pe before eid observed )) (PreH25 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH26 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((q_post_group (acquired) (current)) <> 0) ”
).

Definition OSQPost_partial_solve_wit_5_pure_split_goal_1 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_post_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (pmsg_pre = message)) (PreH22 : (q_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_post_call_input critical sg caller pe before eid observed )) (PreH25 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH26 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((q_post_group (acquired) (current)) <> 0) ”
.

Definition OSQPost_partial_solve_wit_5_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (pmsg_pre = message)) (PreH21 : (q_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (q_post_call_input critical sg caller pe before eid observed )) (PreH24 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH25 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) <> 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
.

Definition OSQPost_partial_solve_wit_5 := OSQPost_partial_solve_wit_5_pure -> OSQPost_partial_solve_wit_5_aux.

Definition OSQPost_partial_solve_wit_6_pure := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (pmsg_pre = message)) (PreH21 : (q_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (q_post_call_input critical sg caller pe before eid observed )) (PreH24 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH25 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_post_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (pmsg_pre = message)) (PreH22 : (q_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_post_call_input critical sg caller pe before eid observed )) (PreH25 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH26 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
).

Definition OSQPost_partial_solve_wit_6_pure_split_goal_1 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_post_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (pmsg_pre = message)) (PreH22 : (q_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_post_call_input critical sg caller pe before eid observed )) (PreH25 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH26 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
.

Definition OSQPost_partial_solve_wit_6_pure_split_goal_2 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_post_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (pmsg_pre = message)) (PreH22 : (q_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_post_call_input critical sg caller pe before eid observed )) (PreH25 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH26 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ”
.

Definition OSQPost_partial_solve_wit_6_pure_split_goal_3 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_post_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (pmsg_pre = message)) (PreH22 : (q_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_post_call_input critical sg caller pe before eid observed )) (PreH25 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH26 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
.

Definition OSQPost_partial_solve_wit_6_pure_split_goal_4 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_post_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (pmsg_pre = message)) (PreH22 : (q_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_post_call_input critical sg caller pe before eid observed )) (PreH25 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH26 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
.

Definition OSQPost_partial_solve_wit_6_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (pmsg_pre = message)) (PreH21 : (q_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (q_post_call_input critical sg caller pe before eid observed )) (PreH24 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH25 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
.

Definition OSQPost_partial_solve_wit_6 := OSQPost_partial_solve_wit_6_pure -> OSQPost_partial_solve_wit_6_aux.

Definition OSQPost_partial_solve_wit_7_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (priority: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH3 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 4 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
|--
  “ (pe <> 0) ”
.

Definition OSQPost_partial_solve_wit_7_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (priority: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH3 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 4 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
|--
  “ (pe <> 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 4 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
.

Definition OSQPost_partial_solve_wit_7 := OSQPost_partial_solve_wit_7_pure -> OSQPost_partial_solve_wit_7_aux.

Definition OSQPost_partial_solve_wit_8_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : (pe <> 0)) (PreH2 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH3 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 1 )
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSQPost_partial_solve_wit_8_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : (pe <> 0)) (PreH2 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH3 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 1 )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 1 )
.

Definition OSQPost_partial_solve_wit_8 := OSQPost_partial_solve_wit_8_pure -> OSQPost_partial_solve_wit_8_aux.

Definition OSQPost_partial_solve_wit_9_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH3 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 1 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ”
.

Definition OSQPost_partial_solve_wit_9_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH3 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 1 )
|--
  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 1 )
.

Definition OSQPost_partial_solve_wit_9 := OSQPost_partial_solve_wit_9_pure -> OSQPost_partial_solve_wit_9_aux.

Definition OSQPost_partial_solve_wit_10_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (q_post_prefix_result environment critical sg caller mask pe eid message before 0 1 returned restored )) (PreH2 : (pe <> 0)) (PreH3 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH4 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSQPost_partial_solve_wit_10_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (q_post_prefix_result environment critical sg caller mask pe eid message before 0 1 returned restored )) (PreH2 : (pe <> 0)) (PreH3 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH4 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_post_prefix_result environment critical sg caller mask pe eid message before 0 1 returned restored ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
.

Definition OSQPost_partial_solve_wit_10 := OSQPost_partial_solve_wit_10_pure -> OSQPost_partial_solve_wit_10_aux.

Definition OSQPost_partial_solve_wit_11_pure := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (pmsg_pre = message)) (PreH21 : (q_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (q_post_call_input critical sg caller pe before eid observed )) (PreH24 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH25 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) = 0) ”
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_post_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (pmsg_pre = message)) (PreH22 : (q_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_post_call_input critical sg caller pe before eid observed )) (PreH25 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH26 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((q_post_group (acquired) (current)) = 0) ”
).

Definition OSQPost_partial_solve_wit_11_pure_split_goal_1 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_post_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (pmsg_pre = message)) (PreH22 : (q_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_post_call_input critical sg caller pe before eid observed )) (PreH25 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH26 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((q_post_group (acquired) (current)) = 0) ”
.

Definition OSQPost_partial_solve_wit_11_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (pmsg_pre = message)) (PreH21 : (q_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (q_post_call_input critical sg caller pe before eid observed )) (PreH24 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH25 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
.

Definition OSQPost_partial_solve_wit_11 := OSQPost_partial_solve_wit_11_pure -> OSQPost_partial_solve_wit_11_aux.

Definition OSQPost_partial_solve_wit_12_pure := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (pmsg_pre = message)) (PreH21 : (q_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (q_post_call_input critical sg caller pe before eid observed )) (PreH24 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH25 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_pointer_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((qcb_addr (sg) ((qID (q)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ”
.

Definition OSQPost_partial_solve_wit_12_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (pmsg_pre = message)) (PreH21 : (q_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (q_post_call_input critical sg caller pe before eid observed )) (PreH24 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH25 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_pointer_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
|--
  “ ((qcb_addr (sg) ((qID (q)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_pointer_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
.

Definition OSQPost_partial_solve_wit_12 := OSQPost_partial_solve_wit_12_pure -> OSQPost_partial_solve_wit_12_aux.

Definition OSQPost_partial_solve_wit_13_pure := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q_2: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (PreH1 : ((queue_entries (q)) >= (qSize (q)))) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (0 <= (qSize (q)))) (PreH6 : ((qSize (q)) <= 65535)) (PreH7 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe <> 0)) (PreH10 : (valid_event_id sg eid )) (PreH11 : (q_post_profile sg )) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH14 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (pe <> 0)) (PreH19 : (valid_event_id sg eid )) (PreH20 : (q_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (q_post_call_input critical sg caller pe before eid observed )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (pmsg_pre = message)) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH30 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_post_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (pe <> 0) ” 
  &&  “ ((queue_entries (q)) >= (qSize (q))) ”
.

Definition OSQPost_partial_solve_wit_13_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q_2: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (PreH1 : ((queue_entries (q)) >= (qSize (q)))) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (0 <= (qSize (q)))) (PreH6 : ((qSize (q)) <= 65535)) (PreH7 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe <> 0)) (PreH10 : (valid_event_id sg eid )) (PreH11 : (q_post_profile sg )) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH14 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (pe <> 0)) (PreH19 : (valid_event_id sg eid )) (PreH20 : (q_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (q_post_call_input critical sg caller pe before eid observed )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (pmsg_pre = message)) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH30 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_post_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
|--
  “ (pe <> 0) ” 
  &&  “ ((queue_entries (q)) >= (qSize (q))) ” 
  &&  “ ((queue_entries (q)) >= (qSize (q))) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (0 <= (qSize (q))) ” 
  &&  “ ((qSize (q)) <= 65535) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_post_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
.

Definition OSQPost_partial_solve_wit_13 := OSQPost_partial_solve_wit_13_pure -> OSQPost_partial_solve_wit_13_aux.

Definition OSQPost_partial_solve_wit_14_pure := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (q_2: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (PreH1 : ((queue_entries (q_2)) >= (qSize (q_2)))) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (0 <= (qSize (q_2)))) (PreH5 : ((qSize (q_2)) <= 65535)) (PreH6 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (q_post_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pe <> 0)) (PreH18 : (valid_event_id sg eid )) (PreH19 : (q_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (q_post_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_restore_pre environment critical saved_local sg caller active mask retval pe eid message before acquired_2 acquired_2 30 0 )
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (retval = retval) ”
.

Definition OSQPost_partial_solve_wit_14_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q_2: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (PreH1 : ((queue_entries (q_2)) >= (qSize (q_2)))) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (0 <= (qSize (q_2)))) (PreH5 : ((qSize (q_2)) <= 65535)) (PreH6 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (q_post_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pe <> 0)) (PreH18 : (valid_event_id sg eid )) (PreH19 : (q_post_profile sg )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (q_post_call_input critical sg caller pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_restore_pre environment critical saved_local sg caller active mask retval pe eid message before acquired_2 acquired_2 30 0 )
|--
  “ (retval = retval) ” 
  &&  “ ((queue_entries (q_2)) >= (qSize (q_2))) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (0 <= (qSize (q_2))) ” 
  &&  “ ((qSize (q_2)) <= 65535) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_restore_pre environment critical saved_local sg caller active mask retval (event_addr (sg) (eid)) eid message before acquired_2 acquired_2 30 0 )
.

Definition OSQPost_partial_solve_wit_14 := OSQPost_partial_solve_wit_14_pure -> OSQPost_partial_solve_wit_14_aux.

Definition OSQPost_partial_solve_wit_15_pure := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q_2: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (PreH1 : ((queue_entries (q)) < (qSize (q)))) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (0 <= (qSize (q)))) (PreH6 : ((qSize (q)) <= 65535)) (PreH7 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe <> 0)) (PreH10 : (valid_event_id sg eid )) (PreH11 : (q_post_profile sg )) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH14 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (pe <> 0)) (PreH19 : (valid_event_id sg eid )) (PreH20 : (q_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (q_post_call_input critical sg caller pe before eid observed )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (pmsg_pre = message)) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH30 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_post_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ ((queue_entries (q)) < (qSize (q))) ”
.

Definition OSQPost_partial_solve_wit_15_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q_2: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (PreH1 : ((queue_entries (q)) < (qSize (q)))) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (0 <= (qSize (q)))) (PreH6 : ((qSize (q)) <= 65535)) (PreH7 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe <> 0)) (PreH10 : (valid_event_id sg eid )) (PreH11 : (q_post_profile sg )) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH14 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (pe <> 0)) (PreH19 : (valid_event_id sg eid )) (PreH20 : (q_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (q_post_call_input critical sg caller pe before eid observed )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (pmsg_pre = message)) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH30 : (q_post_safe environment critical sg caller mask pe eid message before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_post_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
|--
  “ ((queue_entries (q)) < (qSize (q))) ” 
  &&  “ ((queue_entries (q)) < (qSize (q))) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (0 <= (qSize (q))) ” 
  &&  “ ((qSize (q)) <= 65535) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_post_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
.

Definition OSQPost_partial_solve_wit_15 := OSQPost_partial_solve_wit_15_pure -> OSQPost_partial_solve_wit_15_aux.

Definition OSQPost_partial_solve_wit_16_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q)) < (qSize (q)))) (PreH2 : (pe <> 0)) (PreH3 : (q_post_safe environment critical sg caller mask pe eid message before X )) ,
  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> pq)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (q_post_next_in (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) + 1 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_post_qcb_readonly pq q )
  **  (((queue_in_addr (q))) # Ptr  |-> message)
  **  (q_post_slot_frame q slots )
|--
  “ (pe <> 0) ” 
  &&  “ ((queue_entries (q)) < (qSize (q))) ”
.

Definition OSQPost_partial_solve_wit_16_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q)) < (qSize (q)))) (PreH2 : (pe <> 0)) (PreH3 : (q_post_safe environment critical sg caller mask pe eid message before X )) ,
  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (q_post_next_in (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) + 1 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_post_qcb_readonly pq q )
  **  (((queue_in_addr (q))) # Ptr  |-> message)
  **  (q_post_slot_frame q slots )
|--
  “ (pe <> 0) ” 
  &&  “ ((queue_entries (q)) < (qSize (q))) ” 
  &&  “ ((queue_entries (q)) < (qSize (q))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ”
  &&  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (q_post_next_in (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) + 1 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_post_qcb_readonly pq q )
  **  (((queue_in_addr (q))) # Ptr  |-> message)
  **  (q_post_slot_frame q slots )
.

Definition OSQPost_partial_solve_wit_16 := OSQPost_partial_solve_wit_16_pure -> OSQPost_partial_solve_wit_16_aux.

Definition OSQPost_partial_solve_wit_17_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q: QueueFields) (pq: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : ((queue_entries (q)) < (qSize (q)))) (PreH2 : (pe <> 0)) (PreH3 : (q_post_safe environment critical sg caller mask pe eid message before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pq" ) )) # Ptr  |-> pq)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 0 )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSQPost_partial_solve_wit_17_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q: QueueFields) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : ((queue_entries (q)) < (qSize (q)))) (PreH2 : (pe <> 0)) (PreH3 : (q_post_safe environment critical sg caller mask pe eid message before X )) ,
  (q_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 0 )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ ((queue_entries (q)) < (qSize (q))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_post_safe environment critical sg caller mask pe eid message before X ) ”
  &&  (q_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 0 )
.

Definition OSQPost_partial_solve_wit_17 := OSQPost_partial_solve_wit_17_pure -> OSQPost_partial_solve_wit_17_aux.

Definition OSQPost_which_implies_wit_1 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (q_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (q_post_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (q_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (q_post_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
).

Definition OSQPost_which_implies_wit_1_split_goal_1 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (q_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (q_post_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (valid_event_id sg eid ) ”
.

Definition OSQPost_which_implies_wit_1_split_goal_2 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (q_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (q_post_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSQPost_which_implies_wit_1_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (q_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (q_post_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
.

Definition OSQPost_which_implies_wit_2 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ”
  &&  (q_post_save_pre environment critical saved_local sg caller mask before pe eid observed )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  (q_post_save_pre environment critical saved_local sg caller mask before pe eid observed )
).

Definition OSQPost_which_implies_wit_2_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  (q_post_save_pre environment critical saved_local sg caller mask before pe eid observed )
.

Definition OSQPost_which_implies_wit_3 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (valid_event_id sg eid )) (PreH3 : (q_post_profile sg )) ,
  (q_post_save_result environment critical saved_local sg caller mask cpu_sr before eid observed )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_post_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (valid_event_id sg eid )) (PreH3 : (q_post_profile sg )) ,
  (q_post_save_result environment critical saved_local sg caller mask cpu_sr before eid observed )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_post_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
).

Definition OSQPost_which_implies_wit_4 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (acquired_2) (current_2)) <> 0)) ,
  (q_post_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (current_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_post_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current tid old )
  **  (event_task_rdy_pre sg (TskState (acquired)) eid current tid old 4 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (acquired_2) (current_2)) <> 0)) ,
  (q_post_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (current_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_post_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current tid old )
  **  (event_task_rdy_pre sg (TskState (acquired)) eid current tid old 4 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) )
).

Definition OSQPost_which_implies_wit_5 := 
(
forall (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe <> 0)) ,
  (q_post_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired_2)) eid current tid old message 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (q_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 1 )
) \/
(
forall (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe <> 0)) ,
  (q_post_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired_2)) eid current tid old message 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (q_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 1 )
).

Definition OSQPost_which_implies_wit_6 := 
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) ,
  (q_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 1 )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (q_post_prefix_result environment critical sg caller mask pe eid message before 0 1 returned restored ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
) \/
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (q_post_schedule_protocol environment critical sg caller mask pe eid message before )) ,
  (q_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 1 )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (q_post_prefix_result environment critical sg caller mask pe eid message before 0 1 returned restored ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
).

Definition OSQPost_which_implies_wit_7 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (acquired_2) (current_2)) = 0)) ,
  (q_post_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (current_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_post_pointer_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (acquired_2) (current_2)) = 0)) ,
  (q_post_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (current_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_post_pointer_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
).

Definition OSQPost_which_implies_wit_8 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q_2: QueueFields) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (pevent: Z) (cpu_sr: Z) (PreH1 : (pq = (qcb_addr (sg) ((qID (q_2)))))) (PreH2 : (pevent = (event_addr (sg) (eid)))) ,
  (q_post_pointer_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 q_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (0 <= (qSize (q))) ” 
  &&  “ ((qSize (q)) <= 65535) ”
  &&  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_post_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q_2: QueueFields) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (pevent: Z) (cpu_sr: Z) (PreH1 : (pq = (qcb_addr (sg) ((qID (q_2)))))) (PreH2 : (pevent = (event_addr (sg) (eid)))) ,
  (q_post_pointer_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 q_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (0 <= (qSize (q))) ” 
  &&  “ ((qSize (q)) <= 65535) ”
  &&  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_post_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
).

Definition OSQPost_which_implies_wit_9 := 
(
forall (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : ((queue_entries (q)) >= (qSize (q)))) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_post_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State) ,
  (q_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired acquired 30 0 )
) \/
(
forall (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : ((queue_entries (q)) >= (qSize (q)))) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_post_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State) ,
  (q_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired acquired 30 0 )
).

Definition OSQPost_which_implies_wit_10 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q_2)) < (qSize (q_2)))) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 q_2 free_2 slots_2 pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  (q_post_qcb_readonly pq q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) < 65535) ” 
  &&  “ (((queue_in_addr (q)) + 4 ) <= (queue_end_addr (q))) ”
  &&  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_post_qcb_readonly pq q )
  **  (((queue_in_addr (q))) # Ptr  |->_)
  **  (q_post_slot_frame q slots )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q_2)) < (qSize (q_2)))) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 q_2 free_2 slots_2 pq )
  **  (q_post_qcb_readonly pq q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
|--
  EX (x: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ ((qStart (q_2)) = (qStart (q))) ” 
  &&  “ ((queue_end_addr (q_2)) = (queue_end_addr (q))) ” 
  &&  “ ((qSize (q_2)) = (qSize (q))) ” 
  &&  “ ((queue_entries (q_2)) = (queue_entries (q))) ” 
  &&  “ ((queue_in_addr (q_2)) = (queue_in_addr (q))) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) < 65535) ” 
  &&  “ (((queue_in_addr (q)) + 4 ) <= (queue_end_addr (q))) ”
  &&  (((queue_in_addr (q))) # Ptr  |-> x)
  **  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  (q_post_qcb_readonly pq q )
  **  (q_post_slot_frame q slots )
).

Definition OSQPost_which_implies_wit_11 := 
(
forall (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : ((queue_entries (q)) < (qSize (q)))) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (q_post_next_in (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) + 1 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_post_qcb_readonly pq q )
  **  (((queue_in_addr (q))) # Ptr  |-> message)
  **  (q_post_slot_frame q slots )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (q_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 0 )
) \/
(
forall (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : ((queue_entries (q)) < (qSize (q)))) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (q_post_next_in (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) + 1 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_post_qcb_readonly pq q )
  **  (((queue_in_addr (q))) # Ptr  |-> message)
  **  (q_post_slot_frame q slots )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (q_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 0 )
).

Module Type VC_Correct.


Axiom proof_of_OSQPost_safety_wit_1 : OSQPost_safety_wit_1.
Axiom proof_of_OSQPost_safety_wit_2 : OSQPost_safety_wit_2.
Axiom proof_of_OSQPost_safety_wit_3 : OSQPost_safety_wit_3.
Axiom proof_of_OSQPost_safety_wit_4 : OSQPost_safety_wit_4.
Axiom proof_of_OSQPost_safety_wit_5 : OSQPost_safety_wit_5.
Axiom proof_of_OSQPost_entail_wit_1 : OSQPost_entail_wit_1.
Axiom proof_of_OSQPost_entail_wit_2 : OSQPost_entail_wit_2.
Axiom proof_of_OSQPost_entail_wit_3_1 : OSQPost_entail_wit_3_1.
Axiom proof_of_OSQPost_entail_wit_3_2 : OSQPost_entail_wit_3_2.
Axiom proof_of_OSQPost_return_wit_1 : OSQPost_return_wit_1.
Axiom proof_of_OSQPost_return_wit_2 : OSQPost_return_wit_2.
Axiom proof_of_OSQPost_return_wit_3 : OSQPost_return_wit_3.
Axiom proof_of_OSQPost_return_wit_4 : OSQPost_return_wit_4.
Axiom proof_of_OSQPost_return_wit_5 : OSQPost_return_wit_5.
Axiom proof_of_OSQPost_partial_solve_wit_1_pure : OSQPost_partial_solve_wit_1_pure.
Axiom proof_of_OSQPost_partial_solve_wit_1 : OSQPost_partial_solve_wit_1.
Axiom proof_of_OSQPost_partial_solve_wit_2_pure : OSQPost_partial_solve_wit_2_pure.
Axiom proof_of_OSQPost_partial_solve_wit_2 : OSQPost_partial_solve_wit_2.
Axiom proof_of_OSQPost_partial_solve_wit_3 : OSQPost_partial_solve_wit_3.
Axiom proof_of_OSQPost_partial_solve_wit_4_pure : OSQPost_partial_solve_wit_4_pure.
Axiom proof_of_OSQPost_partial_solve_wit_4 : OSQPost_partial_solve_wit_4.
Axiom proof_of_OSQPost_partial_solve_wit_5_pure : OSQPost_partial_solve_wit_5_pure.
Axiom proof_of_OSQPost_partial_solve_wit_5 : OSQPost_partial_solve_wit_5.
Axiom proof_of_OSQPost_partial_solve_wit_6_pure : OSQPost_partial_solve_wit_6_pure.
Axiom proof_of_OSQPost_partial_solve_wit_6 : OSQPost_partial_solve_wit_6.
Axiom proof_of_OSQPost_partial_solve_wit_7_pure : OSQPost_partial_solve_wit_7_pure.
Axiom proof_of_OSQPost_partial_solve_wit_7 : OSQPost_partial_solve_wit_7.
Axiom proof_of_OSQPost_partial_solve_wit_8_pure : OSQPost_partial_solve_wit_8_pure.
Axiom proof_of_OSQPost_partial_solve_wit_8 : OSQPost_partial_solve_wit_8.
Axiom proof_of_OSQPost_partial_solve_wit_9_pure : OSQPost_partial_solve_wit_9_pure.
Axiom proof_of_OSQPost_partial_solve_wit_9 : OSQPost_partial_solve_wit_9.
Axiom proof_of_OSQPost_partial_solve_wit_10_pure : OSQPost_partial_solve_wit_10_pure.
Axiom proof_of_OSQPost_partial_solve_wit_10 : OSQPost_partial_solve_wit_10.
Axiom proof_of_OSQPost_partial_solve_wit_11_pure : OSQPost_partial_solve_wit_11_pure.
Axiom proof_of_OSQPost_partial_solve_wit_11 : OSQPost_partial_solve_wit_11.
Axiom proof_of_OSQPost_partial_solve_wit_12_pure : OSQPost_partial_solve_wit_12_pure.
Axiom proof_of_OSQPost_partial_solve_wit_12 : OSQPost_partial_solve_wit_12.
Axiom proof_of_OSQPost_partial_solve_wit_13_pure : OSQPost_partial_solve_wit_13_pure.
Axiom proof_of_OSQPost_partial_solve_wit_13 : OSQPost_partial_solve_wit_13.
Axiom proof_of_OSQPost_partial_solve_wit_14_pure : OSQPost_partial_solve_wit_14_pure.
Axiom proof_of_OSQPost_partial_solve_wit_14 : OSQPost_partial_solve_wit_14.
Axiom proof_of_OSQPost_partial_solve_wit_15_pure : OSQPost_partial_solve_wit_15_pure.
Axiom proof_of_OSQPost_partial_solve_wit_15 : OSQPost_partial_solve_wit_15.
Axiom proof_of_OSQPost_partial_solve_wit_16_pure : OSQPost_partial_solve_wit_16_pure.
Axiom proof_of_OSQPost_partial_solve_wit_16 : OSQPost_partial_solve_wit_16.
Axiom proof_of_OSQPost_partial_solve_wit_17_pure : OSQPost_partial_solve_wit_17_pure.
Axiom proof_of_OSQPost_partial_solve_wit_17 : OSQPost_partial_solve_wit_17.
Axiom proof_of_OSQPost_which_implies_wit_1 : OSQPost_which_implies_wit_1.
Axiom proof_of_OSQPost_which_implies_wit_2 : OSQPost_which_implies_wit_2.
Axiom proof_of_OSQPost_which_implies_wit_3 : OSQPost_which_implies_wit_3.
Axiom proof_of_OSQPost_which_implies_wit_4 : OSQPost_which_implies_wit_4.
Axiom proof_of_OSQPost_which_implies_wit_5 : OSQPost_which_implies_wit_5.
Axiom proof_of_OSQPost_which_implies_wit_6 : OSQPost_which_implies_wit_6.
Axiom proof_of_OSQPost_which_implies_wit_7 : OSQPost_which_implies_wit_7.
Axiom proof_of_OSQPost_which_implies_wit_8 : OSQPost_which_implies_wit_8.
Axiom proof_of_OSQPost_which_implies_wit_9 : OSQPost_which_implies_wit_9.
Axiom proof_of_OSQPost_which_implies_wit_10 : OSQPost_which_implies_wit_10.
Axiom proof_of_OSQPost_which_implies_wit_11 : OSQPost_which_implies_wit_11.

End VC_Correct.
