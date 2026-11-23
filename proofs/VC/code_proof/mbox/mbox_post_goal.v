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
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_post_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSMboxPost -----*)

Definition OSMboxPost_safety_wit_1 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = pe)) (PreH2 : (pmsg_pre = message)) (PreH3 : (mbox_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH6 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH7 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPost_safety_wit_2 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (pmsg_pre = message)) (PreH4 : (mbox_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH7 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH8 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPost_safety_wit_3 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (message <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH18 : (pmsg_pre <> 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (pmsg_pre = message)) (PreH22 : (mbox_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH25 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH26 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_save_result environment critical saved_local sg caller mask retval before (event_addr (sg) (eid)) message eid )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPost_safety_wit_4 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH3 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 1 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPost_safety_wit_5 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (m: MboxFields) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (mbox_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH27 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH28 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_message_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 m )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPost_safety_wit_6 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (mbox_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH27 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH28 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message before 20 0 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPost_safety_wit_7 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (cpu_sr: Z) (PreH1 : ((mbox_message_ptr (m)) = 0)) (PreH2 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) ,
  (mbox_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 0 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPost_entail_wit_1 := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH8 : (pmsg_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (pmsg_pre = message)) (PreH12 : (mbox_post_profile sg )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH15 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH16 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH10 : (pmsg_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (pmsg_pre = message)) (PreH14 : (mbox_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH17 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH18 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ”
  &&  emp
).

Definition OSMboxPost_entail_wit_1_split_goal_1 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH10 : (pmsg_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (pmsg_pre = message)) (PreH14 : (mbox_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH17 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH18 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((event_slot_type_value ((EventState (before))) (eid)) <= 255)
.

Definition OSMboxPost_entail_wit_1_split_goal_2 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH10 : (pmsg_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (pmsg_pre = message)) (PreH14 : (mbox_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH17 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH18 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (0 <= (event_slot_type_value ((EventState (before))) (eid)))
.

Definition OSMboxPost_entail_wit_2 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (observed_2: OSEventAbstractState) (current_3: OSEventAbstractState) (tid_2: Z) (old_2: TaskAbstractState) (retval_2: Z) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (message <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (mbox_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (message <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH19 : (pmsg_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (pmsg_pre = message)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH26 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH27 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (event_task_rdy_post sg (TskState (acquired_3)) eid current_3 tid_2 old_2 message 2 0 (q_post_sched_group (acquired_3)) (q_post_sched_rows (acquired_3)) retval_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_post_wake_context environment critical saved_local sg caller active_2 mask retval pe message before acquired_3 eid observed_2 current_3 tid_2 old_2 )
|--
  EX (priority: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pe <> 0) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 2 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
.

Definition OSMboxPost_entail_wit_3 := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (observed_2: OSEventAbstractState) (current_3: OSEventAbstractState) (m_2: MboxFields) (PreH1 : ((mbox_message_ptr (m_2)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (message <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH21 : (pmsg_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (mbox_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH28 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_post_message_context environment critical saved_local sg caller active_2 mask retval pe message before acquired_3 eid observed_2 current_3 m_2 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (current: OSEventAbstractState)  (m: MboxFields) ,
  “ ((mbox_message_ptr (m)) = 0) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mbox_post_message_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (observed_2: OSEventAbstractState) (current_3: OSEventAbstractState) (m_2: MboxFields) (PreH1 : ((mbox_message_ptr (m_2)) = 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (mbox_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH27 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH28 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_message_context environment critical saved_local sg caller active_2 mask retval pe message before acquired_3 eid observed_2 current_3 m_2 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (current: OSEventAbstractState)  (m: MboxFields) ,
  “ ((event_addr (sg) (eid)) = pe) ” 
  &&  “ ((mbox_message_ptr (m)) = 0) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ”
  &&  (mbox_post_message_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
).

Definition OSMboxPost_return_wit_1 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) = 0)) (PreH2 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) ,
  (mbox_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 0 )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) = 0)) (PreH2 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) ,
  (mbox_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 0 )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 0 X )
).

Definition OSMboxPost_return_wit_1_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) = 0)) (PreH2 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) ,
  (mbox_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 0 )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 0 X )
.

Definition OSMboxPost_return_wit_2 := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (mbox_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH27 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH28 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message before 20 0 )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 20 X )
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (mbox_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH27 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH28 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message before 20 0 )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 20 X )
).

Definition OSMboxPost_return_wit_2_split_goal_spatial := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (mbox_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH27 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH28 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message before 20 0 )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 20 X )
.

Definition OSMboxPost_return_wit_3 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_post_prefix_result environment critical sg caller mask pe eid message before 0 1 returned restored )) (PreH2 : (pe <> 0)) (PreH3 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH4 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_post_prefix_result environment critical sg caller mask pe eid message before 0 1 returned restored )) (PreH2 : (pe <> 0)) (PreH3 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH4 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 0 X )
).

Definition OSMboxPost_return_wit_3_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_post_prefix_result environment critical sg caller mask pe eid message before 0 1 returned restored )) (PreH2 : (pe <> 0)) (PreH3 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH4 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 0 X )
.

Definition OSMboxPost_return_wit_4 := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (message <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (mbox_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH13 : (pmsg_pre <> 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (pmsg_pre = message)) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH21 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 1 X )
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (message <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (mbox_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH13 : (pmsg_pre <> 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (pmsg_pre = message)) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH21 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 1 X )
).

Definition OSMboxPost_return_wit_4_split_goal_spatial := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (message <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (mbox_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH13 : (pmsg_pre <> 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (pmsg_pre = message)) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH21 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 1 X )
.

Definition OSMboxPost_return_wit_5 := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pmsg_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (pmsg_pre = message)) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH8 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH9 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 3 X )
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pmsg_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (pmsg_pre = message)) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH8 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH9 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 3 X )
).

Definition OSMboxPost_return_wit_5_split_goal_spatial := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pmsg_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (pmsg_pre = message)) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH8 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH9 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 3 X )
.

Definition OSMboxPost_return_wit_6 := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (pmsg_pre = message)) (PreH4 : (mbox_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH7 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH8 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 4 X )
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (pmsg_pre = message)) (PreH4 : (mbox_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH7 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH8 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 4 X )
).

Definition OSMboxPost_return_wit_6_split_goal_spatial := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (pmsg_pre = message)) (PreH4 : (mbox_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH7 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH8 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (mbox_post_post environment critical saved_local sg caller mask pe eid message before 4 X )
.

Definition OSMboxPost_partial_solve_wit_1_pure := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pmsg_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (pmsg_pre = message)) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH8 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH9 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ”
.

Definition OSMboxPost_partial_solve_wit_1_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pmsg_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (pmsg_pre = message)) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH8 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH9 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  (q_post_closed environment critical saved_local sg caller mask before )
.

Definition OSMboxPost_partial_solve_wit_1 := OSMboxPost_partial_solve_wit_1_pure -> OSMboxPost_partial_solve_wit_1_aux.

Definition OSMboxPost_partial_solve_wit_2_pure := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (message <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (mbox_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH13 : (pmsg_pre <> 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (pmsg_pre = message)) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH21 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ”
.

Definition OSMboxPost_partial_solve_wit_2_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (message <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (mbox_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH13 : (pmsg_pre <> 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (pmsg_pre = message)) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH21 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
.

Definition OSMboxPost_partial_solve_wit_2 := OSMboxPost_partial_solve_wit_2_pure -> OSMboxPost_partial_solve_wit_2_aux.

Definition OSMboxPost_partial_solve_wit_3 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (message <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH18 : (pmsg_pre <> 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (pmsg_pre = message)) (PreH22 : (mbox_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH25 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH26 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_save_pre environment critical saved_local sg caller mask before pe message eid )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_save_pre environment critical saved_local sg caller mask before (event_addr (sg) (eid)) message eid )
.

Definition OSMboxPost_partial_solve_wit_4_pure := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (message <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH18 : (pmsg_pre <> 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (pmsg_pre = message)) (PreH22 : (mbox_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH25 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH26 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_save_result environment critical saved_local sg caller mask retval before (event_addr (sg) (eid)) message eid )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ”
.

Definition OSMboxPost_partial_solve_wit_4_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (message <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH18 : (pmsg_pre <> 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (pmsg_pre = message)) (PreH22 : (mbox_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH25 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH26 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_save_result environment critical saved_local sg caller mask retval before (event_addr (sg) (eid)) message eid )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_post_save_result environment critical saved_local sg caller mask retval before pe message eid )
.

Definition OSMboxPost_partial_solve_wit_4 := OSMboxPost_partial_solve_wit_4_pure -> OSMboxPost_partial_solve_wit_4_aux.

Definition OSMboxPost_partial_solve_wit_5_pure := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (mbox_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH27 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH28 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) <> 0) ”
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (message <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH21 : (pmsg_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (mbox_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH28 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
|--
  “ ((q_post_group (acquired) (current)) <> 0) ”
).

Definition OSMboxPost_partial_solve_wit_5_pure_split_goal_1 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (message <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH21 : (pmsg_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (mbox_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH28 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
|--
  “ ((q_post_group (acquired) (current)) <> 0) ”
.

Definition OSMboxPost_partial_solve_wit_5_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (mbox_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH27 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH28 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) <> 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
.

Definition OSMboxPost_partial_solve_wit_5 := OSMboxPost_partial_solve_wit_5_pure -> OSMboxPost_partial_solve_wit_5_aux.

Definition OSMboxPost_partial_solve_wit_6_pure := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (mbox_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH27 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH28 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (message <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH21 : (pmsg_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (mbox_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH28 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
).

Definition OSMboxPost_partial_solve_wit_6_pure_split_goal_1 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (message <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH21 : (pmsg_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (mbox_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH28 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
.

Definition OSMboxPost_partial_solve_wit_6_pure_split_goal_2 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (message <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH21 : (pmsg_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (mbox_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH28 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ”
.

Definition OSMboxPost_partial_solve_wit_6_pure_split_goal_3 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (message <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH21 : (pmsg_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (mbox_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH28 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
|--
  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
.

Definition OSMboxPost_partial_solve_wit_6_pure_split_goal_4 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (message <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH21 : (pmsg_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (mbox_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH28 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
|--
  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
.

Definition OSMboxPost_partial_solve_wit_6_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (mbox_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH27 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH28 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 tid old )
.

Definition OSMboxPost_partial_solve_wit_6 := OSMboxPost_partial_solve_wit_6_pure -> OSMboxPost_partial_solve_wit_6_aux.

Definition OSMboxPost_partial_solve_wit_7_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (priority: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH3 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 2 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
|--
  “ (pe <> 0) ”
.

Definition OSMboxPost_partial_solve_wit_7_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (priority: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH3 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_wake_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 2 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
|--
  “ (pe <> 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_wake_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 2 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
.

Definition OSMboxPost_partial_solve_wit_7 := OSMboxPost_partial_solve_wit_7_pure -> OSMboxPost_partial_solve_wit_7_aux.

Definition OSMboxPost_partial_solve_wit_8_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : (pe <> 0)) (PreH2 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH3 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 1 )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSMboxPost_partial_solve_wit_8_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : (pe <> 0)) (PreH2 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH3 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 1 )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 1 )
.

Definition OSMboxPost_partial_solve_wit_8 := OSMboxPost_partial_solve_wit_8_pure -> OSMboxPost_partial_solve_wit_8_aux.

Definition OSMboxPost_partial_solve_wit_9_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH3 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 1 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ”
.

Definition OSMboxPost_partial_solve_wit_9_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH3 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 1 )
|--
  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 1 )
.

Definition OSMboxPost_partial_solve_wit_9 := OSMboxPost_partial_solve_wit_9_pure -> OSMboxPost_partial_solve_wit_9_aux.

Definition OSMboxPost_partial_solve_wit_10_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_post_prefix_result environment critical sg caller mask pe eid message before 0 1 returned restored )) (PreH2 : (pe <> 0)) (PreH3 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH4 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSMboxPost_partial_solve_wit_10_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_post_prefix_result environment critical sg caller mask pe eid message before 0 1 returned restored )) (PreH2 : (pe <> 0)) (PreH3 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH4 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_post_prefix_result environment critical sg caller mask pe eid message before 0 1 returned restored ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
.

Definition OSMboxPost_partial_solve_wit_10 := OSMboxPost_partial_solve_wit_10_pure -> OSMboxPost_partial_solve_wit_10_aux.

Definition OSMboxPost_partial_solve_wit_11_pure := 
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (mbox_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH27 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH28 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) = 0) ”
) \/
(
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (message <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH21 : (pmsg_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (mbox_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH28 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
|--
  “ ((q_post_group (acquired) (current)) = 0) ”
).

Definition OSMboxPost_partial_solve_wit_11_pure_split_goal_1 := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (message <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH21 : (pmsg_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (mbox_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH28 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
|--
  “ ((q_post_group (acquired) (current)) = 0) ”
.

Definition OSMboxPost_partial_solve_wit_11_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (mbox_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH27 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH28 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
.

Definition OSMboxPost_partial_solve_wit_11 := OSMboxPost_partial_solve_wit_11_pure -> OSMboxPost_partial_solve_wit_11_aux.

Definition OSMboxPost_partial_solve_wit_12_pure := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (message <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH21 : (pmsg_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (mbox_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH28 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_message_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 m )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
|--
  “ ((mbox_message_ptr (m)) <> 0) ”
.

Definition OSMboxPost_partial_solve_wit_12_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (message <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH21 : (pmsg_pre <> 0)) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (mbox_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH28 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH29 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_post_message_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 m )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m)))
|--
  “ ((mbox_message_ptr (m)) <> 0) ” 
  &&  “ ((mbox_message_ptr (m)) <> 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mbox_post_message_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m)))
.

Definition OSMboxPost_partial_solve_wit_12 := OSMboxPost_partial_solve_wit_12_pure -> OSMboxPost_partial_solve_wit_12_aux.

Definition OSMboxPost_partial_solve_wit_13_pure := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MboxFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (PreH1 : ((mbox_message_ptr (m)) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (mbox_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH27 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH28 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_restore_pre environment critical saved_local sg caller active mask retval pe eid message before acquired_2 acquired_2 20 0 )
|--
  “ (retval = retval) ”
.

Definition OSMboxPost_partial_solve_wit_13_aux := 
forall (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MboxFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (PreH1 : ((mbox_message_ptr (m)) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (mbox_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH27 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) (PreH28 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_restore_pre environment critical saved_local sg caller active mask retval pe eid message before acquired_2 acquired_2 20 0 )
|--
  “ (retval = retval) ” 
  &&  “ ((mbox_message_ptr (m)) <> 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_restore_pre environment critical saved_local sg caller active mask retval (event_addr (sg) (eid)) eid message before acquired_2 acquired_2 20 0 )
.

Definition OSMboxPost_partial_solve_wit_13 := OSMboxPost_partial_solve_wit_13_pure -> OSMboxPost_partial_solve_wit_13_aux.

Definition OSMboxPost_partial_solve_wit_14_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (m: MboxFields) (cpu_sr: Z) (PreH1 : ((mbox_message_ptr (m)) = 0)) (PreH2 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_message_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> message)
|--
  “ ((mbox_message_ptr (m)) = 0) ”
.

Definition OSMboxPost_partial_solve_wit_14_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (m: MboxFields) (cpu_sr: Z) (PreH1 : ((mbox_message_ptr (m)) = 0)) (PreH2 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) ,
  (mbox_post_message_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> message)
|--
  “ ((mbox_message_ptr (m)) = 0) ” 
  &&  “ ((mbox_message_ptr (m)) = 0) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ”
  &&  (mbox_post_message_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> message)
.

Definition OSMboxPost_partial_solve_wit_14 := OSMboxPost_partial_solve_wit_14_pure -> OSMboxPost_partial_solve_wit_14_aux.

Definition OSMboxPost_partial_solve_wit_15_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : ((mbox_message_ptr (m)) = 0)) (PreH2 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 0 )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSMboxPost_partial_solve_wit_15_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : ((mbox_message_ptr (m)) = 0)) (PreH2 : (mbox_post_safe environment critical sg caller mask pe eid message before X )) ,
  (mbox_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 0 )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ ((mbox_message_ptr (m)) = 0) ” 
  &&  “ (mbox_post_safe environment critical sg caller mask pe eid message before X ) ”
  &&  (mbox_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 0 )
.

Definition OSMboxPost_partial_solve_wit_15 := OSMboxPost_partial_solve_wit_15_pure -> OSMboxPost_partial_solve_wit_15_aux.

Definition OSMboxPost_which_implies_wit_1 := 
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (message <> 0)) (PreH3 : (mbox_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (mbox_post_call_input critical sg caller pe message before eid )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
) \/
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (message <> 0)) (PreH3 : (mbox_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (mbox_post_call_input critical sg caller pe message before eid )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
).

Definition OSMboxPost_which_implies_wit_1_split_goal_1 := 
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (message <> 0)) (PreH3 : (mbox_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (mbox_post_call_input critical sg caller pe message before eid )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (valid_event_id sg eid ) ”
.

Definition OSMboxPost_which_implies_wit_1_split_goal_2 := 
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (message <> 0)) (PreH3 : (mbox_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (mbox_post_call_input critical sg caller pe message before eid )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMboxPost_which_implies_wit_1_split_goal_spatial := 
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (message <> 0)) (PreH3 : (mbox_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (mbox_post_call_input critical sg caller pe message before eid )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
.

Definition OSMboxPost_which_implies_wit_2 := 
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ”
  &&  (mbox_post_save_pre environment critical saved_local sg caller mask before pe message eid )
) \/
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
|--
  (mbox_post_save_pre environment critical saved_local sg caller mask before pe message eid )
).

Definition OSMboxPost_which_implies_wit_2_split_goal_spatial := 
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
|--
  (mbox_post_save_pre environment critical saved_local sg caller mask before pe message eid )
.

Definition OSMboxPost_which_implies_wit_3 := 
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (valid_event_id sg eid )) (PreH3 : (mbox_post_profile sg )) ,
  (mbox_post_save_result environment critical saved_local sg caller mask cpu_sr before pe message eid )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (current: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_post_group_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
) \/
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (valid_event_id sg eid )) (PreH3 : (mbox_post_profile sg )) ,
  (mbox_post_save_result environment critical saved_local sg caller mask cpu_sr before pe message eid )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (current: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_post_group_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
).

Definition OSMboxPost_which_implies_wit_4 := 
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current_2: OSEventAbstractState) (observed_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (acquired_2) (current_2)) <> 0)) ,
  (mbox_post_group_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed_2 current_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (current_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_post_wake_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current tid old )
  **  (event_task_rdy_pre sg (TskState (acquired)) eid current tid old 2 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) )
) \/
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current_2: OSEventAbstractState) (observed_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (acquired_2) (current_2)) <> 0)) ,
  (mbox_post_group_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed_2 current_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (current_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_post_wake_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current tid old )
  **  (event_task_rdy_pre sg (TskState (acquired)) eid current tid old 2 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) )
).

Definition OSMboxPost_which_implies_wit_5 := 
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (observed: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe <> 0)) ,
  (mbox_post_wake_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired_2)) eid current tid old message 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (mbox_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 1 )
) \/
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (observed: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe <> 0)) ,
  (mbox_post_wake_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired_2)) eid current tid old message 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (mbox_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 1 )
).

Definition OSMboxPost_which_implies_wit_6 := 
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) ,
  (mbox_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 1 )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (mbox_post_prefix_result environment critical sg caller mask pe eid message before 0 1 returned restored ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
) \/
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (mbox_post_schedule_protocol environment critical sg caller mask pe eid message before )) ,
  (mbox_post_restore_post environment critical saved_local sg caller mask pe eid message before 0 1 )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (mbox_post_prefix_result environment critical sg caller mask pe eid message before 0 1 returned restored ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
).

Definition OSMboxPost_which_implies_wit_7 := 
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current_2: OSEventAbstractState) (observed_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (acquired_2) (current_2)) = 0)) ,
  (mbox_post_group_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed_2 current_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (current_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (current: OSEventAbstractState)  (m: MboxFields) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_post_message_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current m )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m)))
) \/
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current_2: OSEventAbstractState) (observed_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (acquired_2) (current_2)) = 0)) ,
  (mbox_post_group_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed_2 current_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (current_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (current: OSEventAbstractState)  (m: MboxFields) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_post_message_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current m )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m)))
).

Definition OSMboxPost_which_implies_wit_8 := 
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (current: OSEventAbstractState) (observed: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : ((mbox_message_ptr (m)) <> 0)) ,
  (mbox_post_message_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State) ,
  (mbox_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired acquired 20 0 )
) \/
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (current: OSEventAbstractState) (observed: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : ((mbox_message_ptr (m)) <> 0)) ,
  (mbox_post_message_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State) ,
  (mbox_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired acquired 20 0 )
).

Definition OSMboxPost_which_implies_wit_9 := 
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (current: OSEventAbstractState) (observed: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : ((mbox_message_ptr (m)) = 0)) ,
  (mbox_post_message_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> message)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (mbox_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 0 )
) \/
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (current: OSEventAbstractState) (observed: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : ((mbox_message_ptr (m)) = 0)) ,
  (mbox_post_message_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> message)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (mbox_post_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message before acquired released 0 0 )
).

Module Type VC_Correct.


Axiom proof_of_OSMboxPost_safety_wit_1 : OSMboxPost_safety_wit_1.
Axiom proof_of_OSMboxPost_safety_wit_2 : OSMboxPost_safety_wit_2.
Axiom proof_of_OSMboxPost_safety_wit_3 : OSMboxPost_safety_wit_3.
Axiom proof_of_OSMboxPost_safety_wit_4 : OSMboxPost_safety_wit_4.
Axiom proof_of_OSMboxPost_safety_wit_5 : OSMboxPost_safety_wit_5.
Axiom proof_of_OSMboxPost_safety_wit_6 : OSMboxPost_safety_wit_6.
Axiom proof_of_OSMboxPost_safety_wit_7 : OSMboxPost_safety_wit_7.
Axiom proof_of_OSMboxPost_entail_wit_1 : OSMboxPost_entail_wit_1.
Axiom proof_of_OSMboxPost_entail_wit_2 : OSMboxPost_entail_wit_2.
Axiom proof_of_OSMboxPost_entail_wit_3 : OSMboxPost_entail_wit_3.
Axiom proof_of_OSMboxPost_return_wit_1 : OSMboxPost_return_wit_1.
Axiom proof_of_OSMboxPost_return_wit_2 : OSMboxPost_return_wit_2.
Axiom proof_of_OSMboxPost_return_wit_3 : OSMboxPost_return_wit_3.
Axiom proof_of_OSMboxPost_return_wit_4 : OSMboxPost_return_wit_4.
Axiom proof_of_OSMboxPost_return_wit_5 : OSMboxPost_return_wit_5.
Axiom proof_of_OSMboxPost_return_wit_6 : OSMboxPost_return_wit_6.
Axiom proof_of_OSMboxPost_partial_solve_wit_1_pure : OSMboxPost_partial_solve_wit_1_pure.
Axiom proof_of_OSMboxPost_partial_solve_wit_1 : OSMboxPost_partial_solve_wit_1.
Axiom proof_of_OSMboxPost_partial_solve_wit_2_pure : OSMboxPost_partial_solve_wit_2_pure.
Axiom proof_of_OSMboxPost_partial_solve_wit_2 : OSMboxPost_partial_solve_wit_2.
Axiom proof_of_OSMboxPost_partial_solve_wit_3 : OSMboxPost_partial_solve_wit_3.
Axiom proof_of_OSMboxPost_partial_solve_wit_4_pure : OSMboxPost_partial_solve_wit_4_pure.
Axiom proof_of_OSMboxPost_partial_solve_wit_4 : OSMboxPost_partial_solve_wit_4.
Axiom proof_of_OSMboxPost_partial_solve_wit_5_pure : OSMboxPost_partial_solve_wit_5_pure.
Axiom proof_of_OSMboxPost_partial_solve_wit_5 : OSMboxPost_partial_solve_wit_5.
Axiom proof_of_OSMboxPost_partial_solve_wit_6_pure : OSMboxPost_partial_solve_wit_6_pure.
Axiom proof_of_OSMboxPost_partial_solve_wit_6 : OSMboxPost_partial_solve_wit_6.
Axiom proof_of_OSMboxPost_partial_solve_wit_7_pure : OSMboxPost_partial_solve_wit_7_pure.
Axiom proof_of_OSMboxPost_partial_solve_wit_7 : OSMboxPost_partial_solve_wit_7.
Axiom proof_of_OSMboxPost_partial_solve_wit_8_pure : OSMboxPost_partial_solve_wit_8_pure.
Axiom proof_of_OSMboxPost_partial_solve_wit_8 : OSMboxPost_partial_solve_wit_8.
Axiom proof_of_OSMboxPost_partial_solve_wit_9_pure : OSMboxPost_partial_solve_wit_9_pure.
Axiom proof_of_OSMboxPost_partial_solve_wit_9 : OSMboxPost_partial_solve_wit_9.
Axiom proof_of_OSMboxPost_partial_solve_wit_10_pure : OSMboxPost_partial_solve_wit_10_pure.
Axiom proof_of_OSMboxPost_partial_solve_wit_10 : OSMboxPost_partial_solve_wit_10.
Axiom proof_of_OSMboxPost_partial_solve_wit_11_pure : OSMboxPost_partial_solve_wit_11_pure.
Axiom proof_of_OSMboxPost_partial_solve_wit_11 : OSMboxPost_partial_solve_wit_11.
Axiom proof_of_OSMboxPost_partial_solve_wit_12_pure : OSMboxPost_partial_solve_wit_12_pure.
Axiom proof_of_OSMboxPost_partial_solve_wit_12 : OSMboxPost_partial_solve_wit_12.
Axiom proof_of_OSMboxPost_partial_solve_wit_13_pure : OSMboxPost_partial_solve_wit_13_pure.
Axiom proof_of_OSMboxPost_partial_solve_wit_13 : OSMboxPost_partial_solve_wit_13.
Axiom proof_of_OSMboxPost_partial_solve_wit_14_pure : OSMboxPost_partial_solve_wit_14_pure.
Axiom proof_of_OSMboxPost_partial_solve_wit_14 : OSMboxPost_partial_solve_wit_14.
Axiom proof_of_OSMboxPost_partial_solve_wit_15_pure : OSMboxPost_partial_solve_wit_15_pure.
Axiom proof_of_OSMboxPost_partial_solve_wit_15 : OSMboxPost_partial_solve_wit_15.
Axiom proof_of_OSMboxPost_which_implies_wit_1 : OSMboxPost_which_implies_wit_1.
Axiom proof_of_OSMboxPost_which_implies_wit_2 : OSMboxPost_which_implies_wit_2.
Axiom proof_of_OSMboxPost_which_implies_wit_3 : OSMboxPost_which_implies_wit_3.
Axiom proof_of_OSMboxPost_which_implies_wit_4 : OSMboxPost_which_implies_wit_4.
Axiom proof_of_OSMboxPost_which_implies_wit_5 : OSMboxPost_which_implies_wit_5.
Axiom proof_of_OSMboxPost_which_implies_wit_6 : OSMboxPost_which_implies_wit_6.
Axiom proof_of_OSMboxPost_which_implies_wit_7 : OSMboxPost_which_implies_wit_7.
Axiom proof_of_OSMboxPost_which_implies_wit_8 : OSMboxPost_which_implies_wit_8.
Axiom proof_of_OSMboxPost_which_implies_wit_9 : OSMboxPost_which_implies_wit_9.

End VC_Correct.
