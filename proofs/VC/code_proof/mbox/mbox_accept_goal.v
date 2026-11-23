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
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_accept_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OSMboxAccept -----*)

Definition OSMboxAccept_safety_wit_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH4 : (mbox_accept_safe critical sg invocation pe before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxAccept_safety_wit_2 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (mbox_accept_profile sg )) (PreH4 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH5 : (mbox_accept_safe critical sg invocation pe before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxAccept_safety_wit_3 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH3 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH4 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pe <> 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (valid_event_id sg eid )) (PreH10 : (mbox_accept_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (mbox_accept_profile sg )) (PreH16 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH17 : (mbox_accept_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxAccept_safety_wit_4 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (mbox_accept_profile sg )) (PreH5 : (mbox_accept_success_input critical sg invocation pe before eid )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe <> 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (valid_event_id sg eid )) (PreH14 : (mbox_accept_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (mbox_accept_profile sg )) (PreH20 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH21 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxAccept_safety_wit_5 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (m: MboxFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (critical_region_interval critical sg invocation before entry )) (PreH4 : (UCOS2_state_inv sg entry )) (PreH5 : (interrupt_saved_value mask retval )) (PreH6 : (mbox_accept_profile sg )) (PreH7 : (mbox_accept_success_input critical sg invocation pe before eid )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe <> 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_accept_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_accept_profile sg )) (PreH22 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH23 : (mbox_accept_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_accept_message_frame platform critical sg invocation origin pe mask retval before entry_2 eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (m)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxAccept_safety_wit_6 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (m: MboxFields) (entry_2: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation checkpoint after )) (PreH2 : (mbox_accept_taken critical sg invocation pe before entry_2 checkpoint (mbox_message_ptr (m)) )) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (mbox_accept_profile sg )) (PreH5 : (critical_region_interval critical sg invocation before entry )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (interrupt_saved_value mask retval )) (PreH8 : (mbox_accept_profile sg )) (PreH9 : (mbox_accept_success_input critical sg invocation pe before eid )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_accept_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (mbox_accept_profile sg )) (PreH24 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH25 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (m)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxAccept_entail_wit_1 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (valid_event_id sg eid )) (PreH4 : (mbox_accept_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH7 : (pevent_pre <> 0)) (PreH8 : (pevent_pre = pe)) (PreH9 : (mbox_accept_profile sg )) (PreH10 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH11 : (mbox_accept_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
|--
  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (mbox_accept_safe critical sg invocation pe before X ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (valid_event_id sg eid )) (PreH6 : (mbox_accept_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (mbox_accept_profile sg )) (PreH12 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH13 : (mbox_accept_safe critical sg invocation pe before X )) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ”
  &&  emp
).

Definition OSMboxAccept_entail_wit_1_split_goal_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (valid_event_id sg eid )) (PreH6 : (mbox_accept_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (mbox_accept_profile sg )) (PreH12 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH13 : (mbox_accept_safe critical sg invocation pe before X )) ,
  ((event_slot_type_value ((EventState (before))) (eid)) <= 255)
.

Definition OSMboxAccept_entail_wit_1_split_goal_2 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (valid_event_id sg eid )) (PreH6 : (mbox_accept_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (mbox_accept_profile sg )) (PreH12 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH13 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (0 <= (event_slot_type_value ((EventState (before))) (eid)))
.

Definition OSMboxAccept_return_wit_1 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (m: MboxFields) (entry_2: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation checkpoint after_2 )) (PreH2 : (mbox_accept_taken critical sg invocation pe before entry_2 checkpoint (mbox_message_ptr (m)) )) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (mbox_accept_profile sg )) (PreH5 : (critical_region_interval critical sg invocation before entry )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (interrupt_saved_value mask retval )) (PreH8 : (mbox_accept_profile sg )) (PreH9 : (mbox_accept_success_input critical sg invocation pe before eid )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_accept_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (mbox_accept_profile sg )) (PreH24 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH25 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask after_2 )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (mbox_accept_post critical sg invocation pe before (mbox_message_ptr (m)) after ) ” 
  &&  “ (mbox_accept_return_safe after (mbox_message_ptr (m)) X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (retval: Z) (m: MboxFields) (entry_2: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation checkpoint after_2 )) (PreH2 : (mbox_accept_taken critical sg invocation pe before entry_2 checkpoint (mbox_message_ptr (m)) )) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (mbox_accept_profile sg )) (PreH5 : (critical_region_interval critical sg invocation before entry )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (interrupt_saved_value mask retval )) (PreH8 : (mbox_accept_profile sg )) (PreH9 : (mbox_accept_success_input critical sg invocation pe before eid )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_accept_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (mbox_accept_profile sg )) (PreH24 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH25 : (mbox_accept_safe critical sg invocation pe before X )) ,
  TT && emp 
|--
  “ (mbox_accept_return_safe after_2 (mbox_message_ptr (m)) X ) ” 
  &&  “ (mbox_accept_post critical sg invocation pevent_pre before (mbox_message_ptr (m)) after_2 ) ”
  &&  emp
).

Definition OSMboxAccept_return_wit_1_split_goal_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (retval: Z) (m: MboxFields) (entry_2: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation checkpoint after_2 )) (PreH2 : (mbox_accept_taken critical sg invocation pe before entry_2 checkpoint (mbox_message_ptr (m)) )) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (mbox_accept_profile sg )) (PreH5 : (critical_region_interval critical sg invocation before entry )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (interrupt_saved_value mask retval )) (PreH8 : (mbox_accept_profile sg )) (PreH9 : (mbox_accept_success_input critical sg invocation pe before eid )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_accept_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (mbox_accept_profile sg )) (PreH24 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH25 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (mbox_accept_return_safe after_2 (mbox_message_ptr (m)) X )
.

Definition OSMboxAccept_return_wit_1_split_goal_2 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (entry: UCOS2_Verify_State) (retval: Z) (m: MboxFields) (entry_2: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation checkpoint after_2 )) (PreH2 : (mbox_accept_taken critical sg invocation pe before entry_2 checkpoint (mbox_message_ptr (m)) )) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (mbox_accept_profile sg )) (PreH5 : (critical_region_interval critical sg invocation before entry )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (interrupt_saved_value mask retval )) (PreH8 : (mbox_accept_profile sg )) (PreH9 : (mbox_accept_success_input critical sg invocation pe before eid )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe <> 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (mbox_accept_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (mbox_accept_profile sg )) (PreH24 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH25 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (mbox_accept_post critical sg invocation pevent_pre before (mbox_message_ptr (m)) after_2 )
.

Definition OSMboxAccept_return_wit_2 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH3 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH4 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pe <> 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (valid_event_id sg eid )) (PreH10 : (mbox_accept_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (mbox_accept_profile sg )) (PreH16 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH17 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (mbox_accept_post critical sg invocation pe before 0 after ) ” 
  &&  “ (mbox_accept_return_safe after 0 X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH3 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH4 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pe <> 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (valid_event_id sg eid )) (PreH10 : (mbox_accept_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (mbox_accept_profile sg )) (PreH16 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH17 : (mbox_accept_safe critical sg invocation pe before X )) ,
  TT && emp 
|--
  “ (mbox_accept_return_safe before 0 X ) ” 
  &&  “ (mbox_accept_post critical sg invocation pevent_pre before 0 before ) ”
  &&  emp
).

Definition OSMboxAccept_return_wit_2_split_goal_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH3 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH4 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pe <> 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (valid_event_id sg eid )) (PreH10 : (mbox_accept_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (mbox_accept_profile sg )) (PreH16 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH17 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (mbox_accept_return_safe before 0 X )
.

Definition OSMboxAccept_return_wit_2_split_goal_2 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH3 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH4 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pe <> 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (valid_event_id sg eid )) (PreH10 : (mbox_accept_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (mbox_accept_profile sg )) (PreH16 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH17 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (mbox_accept_post critical sg invocation pevent_pre before 0 before )
.

Definition OSMboxAccept_return_wit_3 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (mbox_accept_profile sg )) (PreH4 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH5 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (mbox_accept_post critical sg invocation pe before 0 after ) ” 
  &&  “ (mbox_accept_return_safe after 0 X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (mbox_accept_profile sg )) (PreH4 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH5 : (mbox_accept_safe critical sg invocation pe before X )) ,
  TT && emp 
|--
  “ (mbox_accept_return_safe before 0 X ) ” 
  &&  “ (mbox_accept_post critical sg invocation pevent_pre before 0 before ) ”
  &&  emp
).

Definition OSMboxAccept_return_wit_3_split_goal_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (mbox_accept_profile sg )) (PreH4 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH5 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (mbox_accept_return_safe before 0 X )
.

Definition OSMboxAccept_return_wit_3_split_goal_2 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (mbox_accept_profile sg )) (PreH4 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH5 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (mbox_accept_post critical sg invocation pevent_pre before 0 before )
.

Definition OSMboxAccept_partial_solve_wit_1_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (mbox_accept_profile sg )) (PreH4 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH5 : (mbox_accept_safe critical sg invocation pe before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ”
.

Definition OSMboxAccept_partial_solve_wit_1_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (mbox_accept_profile sg )) (PreH4 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH5 : (mbox_accept_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (mbox_accept_safe critical sg invocation pe before X ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSMboxAccept_partial_solve_wit_1 := OSMboxAccept_partial_solve_wit_1_pure -> OSMboxAccept_partial_solve_wit_1_aux.

Definition OSMboxAccept_partial_solve_wit_2_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe <> 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_accept_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (mbox_accept_profile sg )) (PreH15 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH16 : (mbox_accept_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMboxAccept_partial_solve_wit_2_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe <> 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_accept_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (mbox_accept_profile sg )) (PreH15 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH16 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <> 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (mbox_accept_safe critical sg invocation pe before X ) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSMboxAccept_partial_solve_wit_2 := OSMboxAccept_partial_solve_wit_2_pure -> OSMboxAccept_partial_solve_wit_2_aux.

Definition OSMboxAccept_partial_solve_wit_3_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe <> 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_accept_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (mbox_accept_profile sg )) (PreH15 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH16 : (mbox_accept_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ”
.

Definition OSMboxAccept_partial_solve_wit_3_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe <> 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_accept_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (mbox_accept_profile sg )) (PreH15 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH16 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
|--
  “ (pe <> 0) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (mbox_accept_safe critical sg invocation pe before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
.

Definition OSMboxAccept_partial_solve_wit_3 := OSMboxAccept_partial_solve_wit_3_pure -> OSMboxAccept_partial_solve_wit_3_aux.

Definition OSMboxAccept_partial_solve_wit_4 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mbox_accept_profile sg )) (PreH2 : (mbox_accept_success_input critical sg invocation pe before eid )) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe <> 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (valid_event_id sg eid )) (PreH11 : (mbox_accept_profile sg )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (mbox_accept_profile sg )) (PreH17 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH18 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_success_input critical sg invocation pe before eid ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (mbox_accept_safe critical sg invocation pe before X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSMboxAccept_partial_solve_wit_5_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (mbox_accept_profile sg )) (PreH5 : (mbox_accept_success_input critical sg invocation pe before eid )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe <> 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (valid_event_id sg eid )) (PreH14 : (mbox_accept_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (mbox_accept_profile sg )) (PreH20 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH21 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
|--
  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_success_input critical sg invocation pe before eid ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ”
.

Definition OSMboxAccept_partial_solve_wit_5_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (critical_region_interval critical sg invocation before entry )) (PreH2 : (UCOS2_state_inv sg entry )) (PreH3 : (interrupt_saved_value mask retval )) (PreH4 : (mbox_accept_profile sg )) (PreH5 : (mbox_accept_success_input critical sg invocation pe before eid )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe <> 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (valid_event_id sg eid )) (PreH14 : (mbox_accept_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (mbox_accept_profile sg )) (PreH20 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH21 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
|--
  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_success_input critical sg invocation pe before eid ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_success_input critical sg invocation pe before eid ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (mbox_accept_safe critical sg invocation pe before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
.

Definition OSMboxAccept_partial_solve_wit_5 := OSMboxAccept_partial_solve_wit_5_pure -> OSMboxAccept_partial_solve_wit_5_aux.

Definition OSMboxAccept_partial_solve_wit_6_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (m: MboxFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (critical_region_interval critical sg invocation before entry )) (PreH4 : (UCOS2_state_inv sg entry )) (PreH5 : (interrupt_saved_value mask retval )) (PreH6 : (mbox_accept_profile sg )) (PreH7 : (mbox_accept_success_input critical sg invocation pe before eid )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe <> 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_accept_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_accept_profile sg )) (PreH22 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH23 : (mbox_accept_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_accept_message_frame platform critical sg invocation origin pe mask retval before entry_2 eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((( &( "pmsg" ) )) # Ptr  |-> (mbox_message_ptr (m)))
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ ((mbox_message_ptr (m)) = (mbox_message_ptr (m))) ”
.

Definition OSMboxAccept_partial_solve_wit_6_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (entry_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (m: MboxFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (critical_region_interval critical sg invocation before entry )) (PreH4 : (UCOS2_state_inv sg entry )) (PreH5 : (interrupt_saved_value mask retval )) (PreH6 : (mbox_accept_profile sg )) (PreH7 : (mbox_accept_success_input critical sg invocation pe before eid )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe <> 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_accept_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_accept_profile sg )) (PreH22 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH23 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (mbox_accept_message_frame platform critical sg invocation origin pe mask retval before entry_2 eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ ((mbox_message_ptr (m)) = (mbox_message_ptr (m))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_success_input critical sg invocation pe before eid ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (mbox_accept_safe critical sg invocation pe before X ) ”
  &&  (mbox_accept_message_frame platform critical sg invocation origin pe mask retval before entry_2 eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
.

Definition OSMboxAccept_partial_solve_wit_6 := OSMboxAccept_partial_solve_wit_6_pure -> OSMboxAccept_partial_solve_wit_6_aux.

Definition OSMboxAccept_partial_solve_wit_7 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (retval: Z) (m: MboxFields) (entry_2: UCOS2_Verify_State) (checkpoint: UCOS2_Verify_State) (PreH1 : (mbox_accept_taken critical sg invocation pe before entry_2 checkpoint (mbox_message_ptr (m)) )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (mbox_accept_profile sg )) (PreH4 : (critical_region_interval critical sg invocation before entry )) (PreH5 : (UCOS2_state_inv sg entry )) (PreH6 : (interrupt_saved_value mask retval )) (PreH7 : (mbox_accept_profile sg )) (PreH8 : (mbox_accept_success_input critical sg invocation pe before eid )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe <> 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_accept_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (mbox_accept_profile sg )) (PreH23 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH24 : (mbox_accept_safe critical sg invocation pe before X )) ,
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry_2 checkpoint )
|--
  “ (mbox_accept_taken critical sg invocation pe before entry_2 checkpoint (mbox_message_ptr (m)) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (critical_region_interval critical sg invocation before entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_success_input critical sg invocation pe before eid ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ” 
  &&  “ (mbox_accept_safe critical sg invocation pe before X ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask retval entry_2 checkpoint )
.

Definition OSMboxAccept_which_implies_wit_1 := 
(
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (mbox_accept_call_input critical sg invocation pe before eid )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_accept_call_input critical sg invocation pe before eid ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
) \/
(
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (mbox_accept_call_input critical sg invocation pe before eid )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
).

Definition OSMboxAccept_which_implies_wit_1_split_goal_1 := 
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (mbox_accept_call_input critical sg invocation pe before eid )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSMboxAccept_which_implies_wit_1_split_goal_2 := 
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (mbox_accept_call_input critical sg invocation pe before eid )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (valid_event_id sg eid ) ”
.

Definition OSMboxAccept_which_implies_wit_1_split_goal_3 := 
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (mbox_accept_call_input critical sg invocation pe before eid )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMboxAccept_which_implies_wit_1_split_goal_spatial := 
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (mbox_accept_call_input critical sg invocation pe before eid )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
.

Definition OSMboxAccept_which_implies_wit_2 := 
(
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (pe = (event_addr (sg) (eid)))) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
) \/
(
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (pe = (event_addr (sg) (eid)))) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
).

Definition OSMboxAccept_which_implies_wit_2_split_goal_spatial := 
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (pe = (event_addr (sg) (eid)))) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSMboxAccept_which_implies_wit_3 := 
(
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
|--
  “ (mbox_accept_profile sg ) ” 
  &&  “ (mbox_accept_success_input critical sg invocation pe before eid ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
) \/
(
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
|--
  “ (mbox_accept_success_input critical sg invocation pe before eid ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
).

Definition OSMboxAccept_which_implies_wit_3_split_goal_1 := 
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
|--
  “ (mbox_accept_success_input critical sg invocation pe before eid ) ”
.

Definition OSMboxAccept_which_implies_wit_3_split_goal_spatial := 
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (mbox_accept_call_input critical sg invocation pe before eid )) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_accept_type_frame sg before eid )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSMboxAccept_which_implies_wit_4 := 
(
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (mbox_accept_profile sg )) (PreH2 : (mbox_accept_success_input critical sg invocation pe before eid )) (PreH3 : (critical_region_interval critical sg invocation before entry_2 )) (PreH4 : (UCOS2_state_inv sg entry_2 )) (PreH5 : (interrupt_saved_value mask cpu_sr )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (current: OSEventAbstractState)  (m: MboxFields) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (mbox_accept_profile sg ) ”
  &&  (mbox_accept_message_frame platform critical sg invocation origin pe mask cpu_sr before entry eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m)))
) \/
(
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (mbox_accept_profile sg )) (PreH2 : (mbox_accept_success_input critical sg invocation pe before eid )) (PreH3 : (critical_region_interval critical sg invocation before entry_2 )) (PreH4 : (UCOS2_state_inv sg entry_2 )) (PreH5 : (interrupt_saved_value mask cpu_sr )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (current: OSEventAbstractState)  (m: MboxFields) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (mbox_accept_profile sg ) ”
  &&  (mbox_accept_message_frame platform critical sg invocation origin pe mask cpu_sr before entry eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m)))
).

Definition OSMboxAccept_which_implies_wit_5 := 
(
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (m: MboxFields) (current: OSEventAbstractState) (observed: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pmsg: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (pmsg = (mbox_message_ptr (m)))) ,
  (mbox_accept_message_frame platform critical sg invocation origin pe mask cpu_sr before entry_2 eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
|--
  EX (entry: UCOS2_Verify_State)  (checkpoint: UCOS2_Verify_State) ,
  “ (mbox_accept_taken critical sg invocation pe before entry checkpoint pmsg ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry checkpoint )
) \/
(
forall (pe: Z) (eid: EventID) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (m: MboxFields) (current: OSEventAbstractState) (observed: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pmsg: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (mbox_accept_profile sg )) (PreH3 : (pmsg = (mbox_message_ptr (m)))) ,
  (mbox_accept_message_frame platform critical sg invocation origin pe mask cpu_sr before entry_2 eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
|--
  EX (entry: UCOS2_Verify_State)  (checkpoint: UCOS2_Verify_State) ,
  “ (mbox_accept_taken critical sg invocation pe before entry checkpoint pmsg ) ”
  &&  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask cpu_sr entry checkpoint )
).

Module Type VC_Correct.


Axiom proof_of_OSMboxAccept_safety_wit_1 : OSMboxAccept_safety_wit_1.
Axiom proof_of_OSMboxAccept_safety_wit_2 : OSMboxAccept_safety_wit_2.
Axiom proof_of_OSMboxAccept_safety_wit_3 : OSMboxAccept_safety_wit_3.
Axiom proof_of_OSMboxAccept_safety_wit_4 : OSMboxAccept_safety_wit_4.
Axiom proof_of_OSMboxAccept_safety_wit_5 : OSMboxAccept_safety_wit_5.
Axiom proof_of_OSMboxAccept_safety_wit_6 : OSMboxAccept_safety_wit_6.
Axiom proof_of_OSMboxAccept_entail_wit_1 : OSMboxAccept_entail_wit_1.
Axiom proof_of_OSMboxAccept_return_wit_1 : OSMboxAccept_return_wit_1.
Axiom proof_of_OSMboxAccept_return_wit_2 : OSMboxAccept_return_wit_2.
Axiom proof_of_OSMboxAccept_return_wit_3 : OSMboxAccept_return_wit_3.
Axiom proof_of_OSMboxAccept_partial_solve_wit_1_pure : OSMboxAccept_partial_solve_wit_1_pure.
Axiom proof_of_OSMboxAccept_partial_solve_wit_1 : OSMboxAccept_partial_solve_wit_1.
Axiom proof_of_OSMboxAccept_partial_solve_wit_2_pure : OSMboxAccept_partial_solve_wit_2_pure.
Axiom proof_of_OSMboxAccept_partial_solve_wit_2 : OSMboxAccept_partial_solve_wit_2.
Axiom proof_of_OSMboxAccept_partial_solve_wit_3_pure : OSMboxAccept_partial_solve_wit_3_pure.
Axiom proof_of_OSMboxAccept_partial_solve_wit_3 : OSMboxAccept_partial_solve_wit_3.
Axiom proof_of_OSMboxAccept_partial_solve_wit_4 : OSMboxAccept_partial_solve_wit_4.
Axiom proof_of_OSMboxAccept_partial_solve_wit_5_pure : OSMboxAccept_partial_solve_wit_5_pure.
Axiom proof_of_OSMboxAccept_partial_solve_wit_5 : OSMboxAccept_partial_solve_wit_5.
Axiom proof_of_OSMboxAccept_partial_solve_wit_6_pure : OSMboxAccept_partial_solve_wit_6_pure.
Axiom proof_of_OSMboxAccept_partial_solve_wit_6 : OSMboxAccept_partial_solve_wit_6.
Axiom proof_of_OSMboxAccept_partial_solve_wit_7 : OSMboxAccept_partial_solve_wit_7.
Axiom proof_of_OSMboxAccept_which_implies_wit_1 : OSMboxAccept_which_implies_wit_1.
Axiom proof_of_OSMboxAccept_which_implies_wit_2 : OSMboxAccept_which_implies_wit_2.
Axiom proof_of_OSMboxAccept_which_implies_wit_3 : OSMboxAccept_which_implies_wit_3.
Axiom proof_of_OSMboxAccept_which_implies_wit_4 : OSMboxAccept_which_implies_wit_4.
Axiom proof_of_OSMboxAccept_which_implies_wit_5 : OSMboxAccept_which_implies_wit_5.

End VC_Correct.
