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
Require Import Ucos2Verify.VC.code.queue.spec.q_flush_call_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSQFlush -----*)

Definition OSQFlush_safety_wit_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (q_flush_profile sg )) (PreH3 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH4 : (q_flush_api_safe critical sg invocation pe before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQFlush_safety_wit_2 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH2 : (q_flush_profile sg )) (PreH3 : (valid_event_id sg eid )) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (q_flush_profile sg )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (q_flush_public_slot before eid observed )) (PreH15 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (q_flush_profile sg )) (PreH19 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH20 : (q_flush_api_safe critical sg invocation pe before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQFlush_safety_wit_3 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (base: Z) (PreH1 : ((qcb_addr (sg) ((qID (q)))) = base)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH5 : (q_flush_profile sg )) (PreH6 : (valid_event_id sg eid )) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_flush_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_flush_public_slot before eid observed )) (PreH18 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (q_flush_profile sg )) (PreH22 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH23 : (q_flush_api_safe critical sg invocation pe before X )) ,
  (q_flush_restore_post platform critical sg invocation origin mask retval before entry_2 eid observed current_2 )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQFlush_entail_wit_1 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (valid_event_id sg eid )) (PreH3 : (q_flush_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (q_flush_public_slot before eid observed )) (PreH6 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH7 : (pevent_pre <> 0)) (PreH8 : (pevent_pre = pe)) (PreH9 : (q_flush_profile sg )) (PreH10 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH11 : (q_flush_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_flush_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_flush_public_slot before eid observed ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_flush_api_safe critical sg invocation pe before X ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_flush_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_flush_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (q_flush_public_slot before eid observed )) (PreH8 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (q_flush_profile sg )) (PreH12 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH13 : (q_flush_api_safe critical sg invocation pe before X )) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ”
  &&  emp
).

Definition OSQFlush_entail_wit_1_split_goal_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_flush_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (q_flush_public_slot before eid observed )) (PreH8 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (q_flush_profile sg )) (PreH12 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH13 : (q_flush_api_safe critical sg invocation pe before X )) ,
  ((event_slot_type_value ((EventState (before))) (eid)) <= 255)
.

Definition OSQFlush_entail_wit_1_split_goal_2 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_flush_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (q_flush_public_slot before eid observed )) (PreH8 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (q_flush_profile sg )) (PreH12 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH13 : (q_flush_api_safe critical sg invocation pe before X )) ,
  (0 <= (event_slot_type_value ((EventState (before))) (eid)))
.

Definition OSQFlush_return_wit_1 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (base: Z) (PreH1 : ((qcb_addr (sg) ((qID (q)))) = base)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH5 : (q_flush_profile sg )) (PreH6 : (valid_event_id sg eid )) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_flush_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_flush_public_slot before eid observed )) (PreH18 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (q_flush_profile sg )) (PreH22 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH23 : (q_flush_api_safe critical sg invocation pe before X )) ,
  (q_flush_restore_post platform critical sg invocation origin mask retval before entry_2 eid observed current_2 )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (q_flush_api_post critical sg invocation pe before 0 after ) ” 
  &&  “ (q_flush_return_safe after 0 X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (base: Z) (PreH1 : ((qcb_addr (sg) ((qID (q)))) = base)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH5 : (q_flush_profile sg )) (PreH6 : (valid_event_id sg eid )) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_flush_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_flush_public_slot before eid observed )) (PreH18 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (q_flush_profile sg )) (PreH22 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH23 : (q_flush_api_safe critical sg invocation pe before X )) ,
  (q_flush_restore_post platform critical sg invocation origin mask retval before entry_2 eid observed current_2 )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (q_flush_api_post critical sg invocation pe before 0 after ) ” 
  &&  “ (q_flush_return_safe after 0 X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
).

Definition OSQFlush_return_wit_2 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_flush_profile sg )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (q_flush_public_slot before eid observed )) (PreH11 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (q_flush_profile sg )) (PreH15 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH16 : (q_flush_api_safe critical sg invocation pe before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_flush_type_frame sg before eid )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (q_flush_api_post critical sg invocation pe before 1 after ) ” 
  &&  “ (q_flush_return_safe after 1 X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_flush_profile sg )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (q_flush_public_slot before eid observed )) (PreH11 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (q_flush_profile sg )) (PreH15 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH16 : (q_flush_api_safe critical sg invocation pe before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_flush_type_frame sg before eid )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (q_flush_api_post critical sg invocation pe before 1 after ) ” 
  &&  “ (q_flush_return_safe after 1 X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
).

Definition OSQFlush_return_wit_3 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (q_flush_profile sg )) (PreH4 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH5 : (q_flush_api_safe critical sg invocation pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (q_flush_api_post critical sg invocation pe before 4 after ) ” 
  &&  “ (q_flush_return_safe after 4 X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (q_flush_profile sg )) (PreH4 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH5 : (q_flush_api_safe critical sg invocation pe before X )) ,
  TT && emp 
|--
  “ (q_flush_return_safe before 4 X ) ” 
  &&  “ (q_flush_api_post critical sg invocation pevent_pre before 4 before ) ”
  &&  emp
).

Definition OSQFlush_return_wit_3_split_goal_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (q_flush_profile sg )) (PreH4 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH5 : (q_flush_api_safe critical sg invocation pe before X )) ,
  (q_flush_return_safe before 4 X )
.

Definition OSQFlush_return_wit_3_split_goal_2 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (q_flush_profile sg )) (PreH4 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH5 : (q_flush_api_safe critical sg invocation pe before X )) ,
  (q_flush_api_post critical sg invocation pevent_pre before 4 before )
.

Definition OSQFlush_partial_solve_wit_1_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (q_flush_profile sg )) (PreH4 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH5 : (q_flush_api_safe critical sg invocation pe before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ”
.

Definition OSQFlush_partial_solve_wit_1_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (q_flush_profile sg )) (PreH4 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH5 : (q_flush_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_flush_api_safe critical sg invocation pe before X ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSQFlush_partial_solve_wit_1 := OSQFlush_partial_solve_wit_1_pure -> OSQFlush_partial_solve_wit_1_aux.

Definition OSQFlush_partial_solve_wit_2_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_flush_profile sg )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (q_flush_public_slot before eid observed )) (PreH11 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (q_flush_profile sg )) (PreH15 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH16 : (q_flush_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_flush_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_flush_public_slot before eid observed ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ”
.

Definition OSQFlush_partial_solve_wit_2_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_flush_profile sg )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (q_flush_public_slot before eid observed )) (PreH11 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (q_flush_profile sg )) (PreH15 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH16 : (q_flush_api_safe critical sg invocation pe before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_flush_type_frame sg before eid )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_flush_public_slot before eid observed ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_flush_public_slot before eid observed ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_flush_api_safe critical sg invocation pe before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_flush_type_frame sg before eid )
.

Definition OSQFlush_partial_solve_wit_2 := OSQFlush_partial_solve_wit_2_pure -> OSQFlush_partial_solve_wit_2_aux.

Definition OSQFlush_partial_solve_wit_3 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (q_flush_profile sg )) (PreH2 : (valid_event_id sg eid )) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH5 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (valid_event_id sg eid )) (PreH11 : (q_flush_profile sg )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (q_flush_public_slot before eid observed )) (PreH14 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH15 : (pevent_pre <> 0)) (PreH16 : (pevent_pre = pe)) (PreH17 : (q_flush_profile sg )) (PreH18 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH19 : (q_flush_api_safe critical sg invocation pe before X )) ,
  (q_flush_save_pre platform critical sg invocation origin mask before eid observed )
|--
  “ (q_flush_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_flush_public_slot before eid observed ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_flush_api_safe critical sg invocation pe before X ) ”
  &&  (q_flush_save_pre platform critical sg invocation origin mask before eid observed )
.

Definition OSQFlush_partial_solve_wit_4_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH2 : (q_flush_profile sg )) (PreH3 : (valid_event_id sg eid )) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (q_flush_profile sg )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (q_flush_public_slot before eid observed )) (PreH15 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (q_flush_profile sg )) (PreH19 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH20 : (q_flush_api_safe critical sg invocation pe before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSQFlush_partial_solve_wit_4_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH2 : (q_flush_profile sg )) (PreH3 : (valid_event_id sg eid )) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (q_flush_profile sg )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (q_flush_public_slot before eid observed )) (PreH15 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (q_flush_profile sg )) (PreH19 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH20 : (q_flush_api_safe critical sg invocation pe before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
|--
  “ (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_flush_public_slot before eid observed ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_flush_api_safe critical sg invocation pe before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
.

Definition OSQFlush_partial_solve_wit_4 := OSQFlush_partial_solve_wit_4_pure -> OSQFlush_partial_solve_wit_4_aux.

Definition OSQFlush_partial_solve_wit_5_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH3 : (q_flush_profile sg )) (PreH4 : (valid_event_id sg eid )) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_flush_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_flush_public_slot before eid observed )) (PreH16 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (q_flush_profile sg )) (PreH20 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH21 : (q_flush_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_flush_pointer_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
|--
  “ ((qcb_addr (sg) ((qID (q)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSQFlush_partial_solve_wit_5_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH3 : (q_flush_profile sg )) (PreH4 : (valid_event_id sg eid )) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_flush_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_flush_public_slot before eid observed )) (PreH16 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (q_flush_profile sg )) (PreH20 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH21 : (q_flush_api_safe critical sg invocation pe before X )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  (q_flush_pointer_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q )
|--
  “ ((qcb_addr (sg) ((qID (q)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_flush_public_slot before eid observed ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_flush_api_safe critical sg invocation pe before X ) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  (q_flush_pointer_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q )
.

Definition OSQFlush_partial_solve_wit_5 := OSQFlush_partial_solve_wit_5_pure -> OSQFlush_partial_solve_wit_5_aux.

Definition OSQFlush_partial_solve_wit_6_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q_2: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH4 : (q_flush_profile sg )) (PreH5 : (valid_event_id sg eid )) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_flush_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_flush_public_slot before eid observed )) (PreH17 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (q_flush_profile sg )) (PreH21 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH22 : (q_flush_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (qStart (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (qStart (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_flush_store_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q_2 free slots (qcb_addr (sg) ((qID (q)))) )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSQFlush_partial_solve_wit_6_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q_2: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH4 : (q_flush_profile sg )) (PreH5 : (valid_event_id sg eid )) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_flush_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_flush_public_slot before eid observed )) (PreH17 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (q_flush_profile sg )) (PreH21 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH22 : (q_flush_api_safe critical sg invocation pe before X )) ,
  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (qStart (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (qStart (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> 0)
  **  (q_flush_store_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q_2 free slots (qcb_addr (sg) ((qID (q)))) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_flush_public_slot before eid observed ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_flush_api_safe critical sg invocation pe before X ) ”
  &&  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (qStart (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (qStart (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> 0)
  **  (q_flush_store_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q_2 free slots (qcb_addr (sg) ((qID (q)))) )
.

Definition OSQFlush_partial_solve_wit_6 := OSQFlush_partial_solve_wit_6_pure -> OSQFlush_partial_solve_wit_6_aux.

Definition OSQFlush_partial_solve_wit_7_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (base: Z) (PreH1 : ((qcb_addr (sg) ((qID (q)))) = base)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH5 : (q_flush_profile sg )) (PreH6 : (valid_event_id sg eid )) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_flush_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_flush_public_slot before eid observed )) (PreH18 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (q_flush_profile sg )) (PreH22 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH23 : (q_flush_api_safe critical sg invocation pe before X )) ,
  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_flush_restore_pre platform critical sg invocation origin mask retval before entry_2 eid observed current_2 )
|--
  “ (retval = retval) ”
.

Definition OSQFlush_partial_solve_wit_7_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (base: Z) (PreH1 : ((qcb_addr (sg) ((qID (q)))) = base)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH5 : (q_flush_profile sg )) (PreH6 : (valid_event_id sg eid )) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_flush_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_flush_public_slot before eid observed )) (PreH18 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (q_flush_profile sg )) (PreH22 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH23 : (q_flush_api_safe critical sg invocation pe before X )) ,
  (q_flush_restore_pre platform critical sg invocation origin mask retval before entry_2 eid observed current_2 )
|--
  “ (retval = retval) ” 
  &&  “ ((qcb_addr (sg) ((qID (q)))) = base) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_flush_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_flush_public_slot before eid observed ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_flush_api_safe critical sg invocation pe before X ) ”
  &&  (q_flush_restore_pre platform critical sg invocation origin mask retval before entry_2 eid observed current_2 )
.

Definition OSQFlush_partial_solve_wit_7 := OSQFlush_partial_solve_wit_7_pure -> OSQFlush_partial_solve_wit_7_aux.

Definition OSQFlush_which_implies_wit_1 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (q_flush_profile sg )) (PreH3 : (q_flush_call_input critical sg invocation pe before eid observed )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_flush_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_flush_public_slot before eid observed ) ” 
  &&  “ (q_flush_call_input critical sg invocation pe before eid observed ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_flush_type_frame sg before eid )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (q_flush_profile sg )) (PreH3 : (q_flush_call_input critical sg invocation pe before eid observed )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (q_flush_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_flush_type_frame sg before eid )
).

Definition OSQFlush_which_implies_wit_1_split_goal_1 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (q_flush_profile sg )) (PreH3 : (q_flush_call_input critical sg invocation pe before eid observed )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (q_flush_public_slot before eid observed ) ”
.

Definition OSQFlush_which_implies_wit_1_split_goal_2 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (q_flush_profile sg )) (PreH3 : (q_flush_call_input critical sg invocation pe before eid observed )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSQFlush_which_implies_wit_1_split_goal_3 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (q_flush_profile sg )) (PreH3 : (q_flush_call_input critical sg invocation pe before eid observed )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (valid_event_id sg eid ) ”
.

Definition OSQFlush_which_implies_wit_1_split_goal_4 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (q_flush_profile sg )) (PreH3 : (q_flush_call_input critical sg invocation pe before eid observed )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSQFlush_which_implies_wit_1_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (q_flush_profile sg )) (PreH3 : (q_flush_call_input critical sg invocation pe before eid observed )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_flush_type_frame sg before eid )
.

Definition OSQFlush_which_implies_wit_2 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (q_flush_public_slot before eid observed )) (PreH3 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH4 : (q_flush_profile sg )) (PreH5 : (valid_event_id sg eid )) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_flush_type_frame sg before eid )
|--
  “ (q_flush_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  (q_flush_save_pre platform critical sg invocation origin mask before eid observed )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (q_flush_public_slot before eid observed )) (PreH3 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH4 : (q_flush_profile sg )) (PreH5 : (valid_event_id sg eid )) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_flush_type_frame sg before eid )
|--
  (q_flush_save_pre platform critical sg invocation origin mask before eid observed )
).

Definition OSQFlush_which_implies_wit_2_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (q_flush_public_slot before eid observed )) (PreH3 : (q_flush_call_input critical sg invocation pe before eid observed )) (PreH4 : (q_flush_profile sg )) (PreH5 : (valid_event_id sg eid )) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_flush_type_frame sg before eid )
|--
  (q_flush_save_pre platform critical sg invocation origin mask before eid observed )
.

Definition OSQFlush_which_implies_wit_3 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (q_flush_acquire_facts critical sg invocation eid mask cpu_sr before entry_2 observed current_2 )) (PreH2 : (q_flush_profile sg )) (PreH3 : (valid_event_id sg eid )) (PreH4 : (pe = (event_addr (sg) (eid)))) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  (q_flush_pointer_context platform critical sg invocation origin mask cpu_sr before entry eid observed current q )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (q_flush_acquire_facts critical sg invocation eid mask cpu_sr before entry_2 observed current_2 )) (PreH2 : (q_flush_profile sg )) (PreH3 : (valid_event_id sg eid )) (PreH4 : (pe = (event_addr (sg) (eid)))) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  (q_flush_pointer_context platform critical sg invocation origin mask cpu_sr before entry eid observed current q )
).

Definition OSQFlush_which_implies_wit_4 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) (PreH1 : (pq = (qcb_addr (sg) ((qID (q_2)))))) (PreH2 : (pe = (event_addr (sg) (eid)))) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  (q_flush_pointer_context platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  (q_flush_store_context platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots pq )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) (PreH1 : (pq = (qcb_addr (sg) ((qID (q_2)))))) (PreH2 : (pe = (event_addr (sg) (eid)))) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  (q_flush_pointer_context platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  (q_flush_store_context platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots pq )
).

Definition OSQFlush_which_implies_wit_5 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> 0)
  **  (q_flush_store_context platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q free slots pq )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (base: Z) ,
  “ (pq = base) ”
  &&  (q_flush_restore_pre platform critical sg invocation origin mask cpu_sr before entry eid observed current )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> 0)
  **  (q_flush_store_context platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q free slots pq )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  (q_flush_restore_pre platform critical sg invocation origin mask cpu_sr before entry eid observed current )
).

Module Type VC_Correct.


Axiom proof_of_OSQFlush_safety_wit_1 : OSQFlush_safety_wit_1.
Axiom proof_of_OSQFlush_safety_wit_2 : OSQFlush_safety_wit_2.
Axiom proof_of_OSQFlush_safety_wit_3 : OSQFlush_safety_wit_3.
Axiom proof_of_OSQFlush_entail_wit_1 : OSQFlush_entail_wit_1.
Axiom proof_of_OSQFlush_return_wit_1 : OSQFlush_return_wit_1.
Axiom proof_of_OSQFlush_return_wit_2 : OSQFlush_return_wit_2.
Axiom proof_of_OSQFlush_return_wit_3 : OSQFlush_return_wit_3.
Axiom proof_of_OSQFlush_partial_solve_wit_1_pure : OSQFlush_partial_solve_wit_1_pure.
Axiom proof_of_OSQFlush_partial_solve_wit_1 : OSQFlush_partial_solve_wit_1.
Axiom proof_of_OSQFlush_partial_solve_wit_2_pure : OSQFlush_partial_solve_wit_2_pure.
Axiom proof_of_OSQFlush_partial_solve_wit_2 : OSQFlush_partial_solve_wit_2.
Axiom proof_of_OSQFlush_partial_solve_wit_3 : OSQFlush_partial_solve_wit_3.
Axiom proof_of_OSQFlush_partial_solve_wit_4_pure : OSQFlush_partial_solve_wit_4_pure.
Axiom proof_of_OSQFlush_partial_solve_wit_4 : OSQFlush_partial_solve_wit_4.
Axiom proof_of_OSQFlush_partial_solve_wit_5_pure : OSQFlush_partial_solve_wit_5_pure.
Axiom proof_of_OSQFlush_partial_solve_wit_5 : OSQFlush_partial_solve_wit_5.
Axiom proof_of_OSQFlush_partial_solve_wit_6_pure : OSQFlush_partial_solve_wit_6_pure.
Axiom proof_of_OSQFlush_partial_solve_wit_6 : OSQFlush_partial_solve_wit_6.
Axiom proof_of_OSQFlush_partial_solve_wit_7_pure : OSQFlush_partial_solve_wit_7_pure.
Axiom proof_of_OSQFlush_partial_solve_wit_7 : OSQFlush_partial_solve_wit_7.
Axiom proof_of_OSQFlush_which_implies_wit_1 : OSQFlush_which_implies_wit_1.
Axiom proof_of_OSQFlush_which_implies_wit_2 : OSQFlush_which_implies_wit_2.
Axiom proof_of_OSQFlush_which_implies_wit_3 : OSQFlush_which_implies_wit_3.
Axiom proof_of_OSQFlush_which_implies_wit_4 : OSQFlush_which_implies_wit_4.
Axiom proof_of_OSQFlush_which_implies_wit_5 : OSQFlush_which_implies_wit_5.

End VC_Correct.
