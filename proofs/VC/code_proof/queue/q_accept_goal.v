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
Require Import Ucos2Verify.VC.code.queue.spec.q_accept_api_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSQAccept -----*)

Definition OSQAccept_safety_wit_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (perr_pre = errptr)) (PreH3 : (q_accept_profile sg )) (PreH4 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH5 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQAccept_safety_wit_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = errptr)) (PreH4 : (q_accept_profile sg )) (PreH5 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH6 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 4)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQAccept_safety_wit_3 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH3 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH4 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_accept_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_query_public_slot before eid observed )) (PreH12 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (perr_pre = errptr)) (PreH16 : (q_accept_profile sg )) (PreH17 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH18 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 1)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQAccept_safety_wit_4 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_accept_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_accept_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_query_public_slot before eid observed )) (PreH16 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (perr_pre = errptr)) (PreH20 : (q_accept_profile sg )) (PreH21 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH22 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQAccept_safety_wit_5 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : ((queue_entries (q_2)) <= 0)) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_accept_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_accept_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (perr_pre = errptr)) (PreH23 : (q_accept_profile sg )) (PreH24 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH25 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_accept_restore_pre platform critical sg invocation origin mask retval before entry_2 entry_2 eid observed current_2 0 q_accept_empty )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 31)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQAccept_safety_wit_6 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (q_2: QueueFields) (message: Z) (q_3: QueueFields) (q_4: QueueFields) (message_2: Z) (entry_2: UCOS2_Verify_State) (after: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : (((queue_out_addr (q_4)) + 4 ) = (queue_end_addr (q_4)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q_4)))) (PreH4 : ((queue_entries (q_4)) <= 65535)) (PreH5 : (0 < (queue_entries (q_3)))) (PreH6 : ((queue_entries (q_3)) <= 65535)) (PreH7 : ((queue_entries (q_2)) > 0)) (PreH8 : (0 <= (queue_entries (q_2)))) (PreH9 : ((queue_entries (q_2)) <= 65535)) (PreH10 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_accept_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (q_accept_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = errptr)) (PreH29 : (q_accept_profile sg )) (PreH30 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH31 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_api_restore_post platform critical sg invocation origin mask retval before entry_2 after eid observed current_2 message_2 q_accept_success )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQAccept_safety_wit_7 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (q_2: QueueFields) (message: Z) (q_3: QueueFields) (q_4: QueueFields) (message_2: Z) (entry_2: UCOS2_Verify_State) (after: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : (((queue_out_addr (q_4)) + 4 ) <> (queue_end_addr (q_4)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q_4)))) (PreH4 : ((queue_entries (q_4)) <= 65535)) (PreH5 : (0 < (queue_entries (q_3)))) (PreH6 : ((queue_entries (q_3)) <= 65535)) (PreH7 : ((queue_entries (q_2)) > 0)) (PreH8 : (0 <= (queue_entries (q_2)))) (PreH9 : ((queue_entries (q_2)) <= 65535)) (PreH10 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_accept_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (q_accept_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = errptr)) (PreH29 : (q_accept_profile sg )) (PreH30 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH31 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_api_restore_post platform critical sg invocation origin mask retval before entry_2 after eid observed current_2 message_2 q_accept_success )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQAccept_safety_wit_8 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : ((queue_entries (q_2)) <= 0)) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_accept_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_accept_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (perr_pre = errptr)) (PreH23 : (q_accept_profile sg )) (PreH24 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH25 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_api_restore_post platform critical sg invocation origin mask retval before entry_2 entry_2 eid observed current_2 0 q_accept_empty )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 31)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQAccept_entail_wit_1 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (valid_event_id sg eid )) (PreH3 : (q_accept_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (q_query_public_slot before eid observed )) (PreH6 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH7 : (pevent_pre <> 0)) (PreH8 : (pevent_pre = pe)) (PreH9 : (perr_pre = errptr)) (PreH10 : (q_accept_profile sg )) (PreH11 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH12 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = errptr) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_accept_api_safe critical sg invocation pe before X ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_accept_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (q_query_public_slot before eid observed )) (PreH8 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (perr_pre = errptr)) (PreH12 : (q_accept_profile sg )) (PreH13 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH14 : (q_accept_api_safe critical sg invocation pe before X )) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ”
  &&  emp
).

Definition OSQAccept_entail_wit_1_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_accept_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (q_query_public_slot before eid observed )) (PreH8 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (perr_pre = errptr)) (PreH12 : (q_accept_profile sg )) (PreH13 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH14 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((event_slot_type_value ((EventState (before))) (eid)) <= 255)
.

Definition OSQAccept_entail_wit_1_split_goal_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_accept_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (q_query_public_slot before eid observed )) (PreH8 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (perr_pre = errptr)) (PreH12 : (q_accept_profile sg )) (PreH13 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH14 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (0 <= (event_slot_type_value ((EventState (before))) (eid)))
.

Definition OSQAccept_return_wit_1 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (message: Z) (q_2: QueueFields) (q_3: QueueFields) (message_2: Z) (entry_2: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : (((queue_out_addr (q_3)) + 4 ) = (queue_end_addr (q_3)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q_3)))) (PreH4 : ((queue_entries (q_3)) <= 65535)) (PreH5 : (0 < (queue_entries (q_2)))) (PreH6 : ((queue_entries (q_2)) <= 65535)) (PreH7 : ((queue_entries (q)) > 0)) (PreH8 : (0 <= (queue_entries (q)))) (PreH9 : ((queue_entries (q)) <= 65535)) (PreH10 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_accept_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (q_accept_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = errptr)) (PreH29 : (q_accept_profile sg )) (PreH30 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH31 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_api_restore_post platform critical sg invocation origin mask retval before entry_2 after_2 eid observed current_2 message_2 q_accept_success )
  **  ((perr_pre) # UChar  |-> 0)
|--
  EX (error: OSErrCode)  (after: UCOS2_Verify_State) ,
  “ (q_accept_api_post critical sg invocation pe before message error after ) ” 
  &&  “ (q_accept_return_safe after message error X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
  **  ((errptr) # UChar  |-> (encode_os_err_code (error)))
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (message: Z) (q_2: QueueFields) (q_3: QueueFields) (message_2: Z) (entry_2: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : (((queue_out_addr (q_3)) + 4 ) = (queue_end_addr (q_3)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q_3)))) (PreH4 : ((queue_entries (q_3)) <= 65535)) (PreH5 : (0 < (queue_entries (q_2)))) (PreH6 : ((queue_entries (q_2)) <= 65535)) (PreH7 : ((queue_entries (q)) > 0)) (PreH8 : (0 <= (queue_entries (q)))) (PreH9 : ((queue_entries (q)) <= 65535)) (PreH10 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_accept_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (q_accept_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = errptr)) (PreH29 : (q_accept_profile sg )) (PreH30 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH31 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_api_restore_post platform critical sg invocation origin mask retval before entry_2 after_2 eid observed current_2 message_2 q_accept_success )
|--
  EX (error: OSErrCode)  (after: UCOS2_Verify_State) ,
  “ (0 = (encode_os_err_code (error))) ” 
  &&  “ (q_accept_api_post critical sg invocation pe before message error after ) ” 
  &&  “ (q_accept_return_safe after message error X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
).

Definition OSQAccept_return_wit_2 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (message: Z) (q_2: QueueFields) (q_3: QueueFields) (message_2: Z) (entry_2: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : (((queue_out_addr (q_3)) + 4 ) <> (queue_end_addr (q_3)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q_3)))) (PreH4 : ((queue_entries (q_3)) <= 65535)) (PreH5 : (0 < (queue_entries (q_2)))) (PreH6 : ((queue_entries (q_2)) <= 65535)) (PreH7 : ((queue_entries (q)) > 0)) (PreH8 : (0 <= (queue_entries (q)))) (PreH9 : ((queue_entries (q)) <= 65535)) (PreH10 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_accept_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (q_accept_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = errptr)) (PreH29 : (q_accept_profile sg )) (PreH30 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH31 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_api_restore_post platform critical sg invocation origin mask retval before entry_2 after_2 eid observed current_2 message_2 q_accept_success )
  **  ((perr_pre) # UChar  |-> 0)
|--
  EX (error: OSErrCode)  (after: UCOS2_Verify_State) ,
  “ (q_accept_api_post critical sg invocation pe before message error after ) ” 
  &&  “ (q_accept_return_safe after message error X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
  **  ((errptr) # UChar  |-> (encode_os_err_code (error)))
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (message: Z) (q_2: QueueFields) (q_3: QueueFields) (message_2: Z) (entry_2: UCOS2_Verify_State) (after_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : (((queue_out_addr (q_3)) + 4 ) <> (queue_end_addr (q_3)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q_3)))) (PreH4 : ((queue_entries (q_3)) <= 65535)) (PreH5 : (0 < (queue_entries (q_2)))) (PreH6 : ((queue_entries (q_2)) <= 65535)) (PreH7 : ((queue_entries (q)) > 0)) (PreH8 : (0 <= (queue_entries (q)))) (PreH9 : ((queue_entries (q)) <= 65535)) (PreH10 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_accept_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (q_accept_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = errptr)) (PreH29 : (q_accept_profile sg )) (PreH30 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH31 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_api_restore_post platform critical sg invocation origin mask retval before entry_2 after_2 eid observed current_2 message_2 q_accept_success )
|--
  EX (error: OSErrCode)  (after: UCOS2_Verify_State) ,
  “ (0 = (encode_os_err_code (error))) ” 
  &&  “ (q_accept_api_post critical sg invocation pe before message error after ) ” 
  &&  “ (q_accept_return_safe after message error X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
).

Definition OSQAccept_return_wit_3 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : ((queue_entries (q)) <= 0)) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_accept_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_accept_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (perr_pre = errptr)) (PreH23 : (q_accept_profile sg )) (PreH24 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH25 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_api_restore_post platform critical sg invocation origin mask retval before entry_2 entry_2 eid observed current_2 0 q_accept_empty )
  **  ((perr_pre) # UChar  |-> 31)
|--
  EX (error: OSErrCode)  (after: UCOS2_Verify_State) ,
  “ (q_accept_api_post critical sg invocation pe before 0 error after ) ” 
  &&  “ (q_accept_return_safe after 0 error X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
  **  ((errptr) # UChar  |-> (encode_os_err_code (error)))
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : ((queue_entries (q)) <= 0)) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_accept_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_accept_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (perr_pre = errptr)) (PreH23 : (q_accept_profile sg )) (PreH24 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH25 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_api_restore_post platform critical sg invocation origin mask retval before entry_2 entry_2 eid observed current_2 0 q_accept_empty )
|--
  EX (error: OSErrCode)  (after: UCOS2_Verify_State) ,
  “ (31 = (encode_os_err_code (error))) ” 
  &&  “ (q_accept_api_post critical sg invocation pe before 0 error after ) ” 
  &&  “ (q_accept_return_safe after 0 error X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
).

Definition OSQAccept_return_wit_4 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH3 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH4 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_accept_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_query_public_slot before eid observed )) (PreH12 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (perr_pre = errptr)) (PreH16 : (q_accept_profile sg )) (PreH17 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH18 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 1)
|--
  EX (error: OSErrCode)  (after: UCOS2_Verify_State) ,
  “ (q_accept_api_post critical sg invocation pe before 0 error after ) ” 
  &&  “ (q_accept_return_safe after 0 error X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
  **  ((errptr) # UChar  |-> (encode_os_err_code (error)))
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_accept_profile sg )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (q_query_public_slot before eid observed )) (PreH11 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (perr_pre = errptr)) (PreH15 : (q_accept_profile sg )) (PreH16 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH17 : (q_accept_api_safe critical sg invocation pe before X )) ,
  TT && emp 
|--
  EX (error: OSErrCode) ,
  “ (1 = (encode_os_err_code (error))) ” 
  &&  “ (q_accept_api_post critical sg invocation (event_addr (sg) (eid)) before 0 error before ) ” 
  &&  “ (q_accept_return_safe before 0 error X ) ”
  &&  emp
).

Definition OSQAccept_return_wit_5 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = errptr)) (PreH4 : (q_accept_profile sg )) (PreH5 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH6 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |-> 4)
|--
  EX (error: OSErrCode)  (after: UCOS2_Verify_State) ,
  “ (q_accept_api_post critical sg invocation pe before 0 error after ) ” 
  &&  “ (q_accept_return_safe after 0 error X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask after )
  **  ((errptr) # UChar  |-> (encode_os_err_code (error)))
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = errptr)) (PreH4 : (q_accept_profile sg )) (PreH5 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH6 : (q_accept_api_safe critical sg invocation pe before X )) ,
  TT && emp 
|--
  EX (error: OSErrCode) ,
  “ (4 = (encode_os_err_code (error))) ” 
  &&  “ (q_accept_api_post critical sg invocation pe before 0 error before ) ” 
  &&  “ (q_accept_return_safe before 0 error X ) ”
  &&  emp
).

Definition OSQAccept_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = errptr)) (PreH4 : (q_accept_profile sg )) (PreH5 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH6 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ”
.

Definition OSQAccept_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = errptr)) (PreH4 : (q_accept_profile sg )) (PreH5 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH6 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = errptr) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_accept_api_safe critical sg invocation pe before X ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQAccept_partial_solve_wit_1 := OSQAccept_partial_solve_wit_1_pure -> OSQAccept_partial_solve_wit_1_aux.

Definition OSQAccept_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_accept_profile sg )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (q_query_public_slot before eid observed )) (PreH11 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (perr_pre = errptr)) (PreH15 : (q_accept_profile sg )) (PreH16 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH17 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ”
.

Definition OSQAccept_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_accept_profile sg )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (q_query_public_slot before eid observed )) (PreH11 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (perr_pre = errptr)) (PreH15 : (q_accept_profile sg )) (PreH16 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH17 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <> 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = errptr) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_accept_api_safe critical sg invocation pe before X ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQAccept_partial_solve_wit_2 := OSQAccept_partial_solve_wit_2_pure -> OSQAccept_partial_solve_wit_2_aux.

Definition OSQAccept_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_accept_profile sg )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (q_query_public_slot before eid observed )) (PreH11 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (perr_pre = errptr)) (PreH15 : (q_accept_profile sg )) (PreH16 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH17 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ”
.

Definition OSQAccept_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_accept_profile sg )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (q_query_public_slot before eid observed )) (PreH11 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (perr_pre = errptr)) (PreH15 : (q_accept_profile sg )) (PreH16 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH17 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = errptr) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_accept_api_safe critical sg invocation pe before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQAccept_partial_solve_wit_3 := OSQAccept_partial_solve_wit_3_pure -> OSQAccept_partial_solve_wit_3_aux.

Definition OSQAccept_partial_solve_wit_4 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_accept_profile sg )) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (valid_event_id sg eid )) (PreH12 : (q_accept_profile sg )) (PreH13 : (UCOS2_state_inv sg before )) (PreH14 : (q_query_public_slot before eid observed )) (PreH15 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (perr_pre = errptr)) (PreH19 : (q_accept_profile sg )) (PreH20 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH21 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_save_pre platform critical sg invocation origin mask before eid observed )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = errptr) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_accept_api_safe critical sg invocation pe before X ) ”
  &&  (q_accept_save_pre platform critical sg invocation origin mask before eid observed )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQAccept_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_accept_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_accept_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_query_public_slot before eid observed )) (PreH16 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (perr_pre = errptr)) (PreH20 : (q_accept_profile sg )) (PreH21 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH22 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ”
.

Definition OSQAccept_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_accept_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_accept_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_query_public_slot before eid observed )) (PreH16 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (perr_pre = errptr)) (PreH20 : (q_accept_profile sg )) (PreH21 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH22 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = errptr) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_accept_api_safe critical sg invocation pe before X ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQAccept_partial_solve_wit_5 := OSQAccept_partial_solve_wit_5_pure -> OSQAccept_partial_solve_wit_5_aux.

Definition OSQAccept_partial_solve_wit_6_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_accept_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_accept_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_query_public_slot before eid observed )) (PreH17 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (perr_pre = errptr)) (PreH21 : (q_accept_profile sg )) (PreH22 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH23 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_accept_pointer_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((qcb_addr (sg) ((qID (q)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ”
.

Definition OSQAccept_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_accept_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_accept_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_query_public_slot before eid observed )) (PreH17 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (perr_pre = errptr)) (PreH21 : (q_accept_profile sg )) (PreH22 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH23 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_pointer_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((qcb_addr (sg) ((qID (q)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = errptr) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_accept_api_safe critical sg invocation pe before X ) ”
  &&  (q_accept_pointer_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQAccept_partial_solve_wit_6 := OSQAccept_partial_solve_wit_6_pure -> OSQAccept_partial_solve_wit_6_aux.

Definition OSQAccept_partial_solve_wit_7_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q_2: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (PreH1 : ((queue_entries (q)) > 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_accept_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_accept_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (q_query_public_slot before eid observed )) (PreH20 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (perr_pre = errptr)) (PreH24 : (q_accept_profile sg )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_accept_store_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((queue_entries (q)) > 0) ”
.

Definition OSQAccept_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q_2: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (PreH1 : ((queue_entries (q)) > 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_accept_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_accept_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (q_query_public_slot before eid observed )) (PreH20 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (perr_pre = errptr)) (PreH24 : (q_accept_profile sg )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_store_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((queue_entries (q)) > 0) ” 
  &&  “ ((queue_entries (q)) > 0) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = errptr) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_accept_api_safe critical sg invocation pe before X ) ”
  &&  (q_accept_store_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQAccept_partial_solve_wit_7 := OSQAccept_partial_solve_wit_7_pure -> OSQAccept_partial_solve_wit_7_aux.

Definition OSQAccept_partial_solve_wit_8 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (message: Z) (q_3: QueueFields) (PreH1 : (0 < (queue_entries (q_3)))) (PreH2 : ((queue_entries (q_3)) <= 65535)) (PreH3 : ((queue_entries (q_2)) > 0)) (PreH4 : (0 <= (queue_entries (q_2)))) (PreH5 : ((queue_entries (q_2)) <= 65535)) (PreH6 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (q_accept_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_accept_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (q_query_public_slot before eid observed )) (PreH21 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (perr_pre = errptr)) (PreH25 : (q_accept_profile sg )) (PreH26 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH27 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_dequeue_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q_3 next free slots (qcb_addr (sg) ((qID (q)))) message )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q_3)) + (1 * sizeof(PTR))))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_3)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q)))) q_3 )
  **  (((queue_out_addr (q_3))) # Ptr  |-> message)
  **  (q_accept_head_slot q_3 slots )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 < (queue_entries (q_3))) ” 
  &&  “ ((queue_entries (q_3)) <= 65535) ” 
  &&  “ ((queue_entries (q_2)) > 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = errptr) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_accept_api_safe critical sg invocation pe before X ) ”
  &&  (q_accept_dequeue_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q_3 next free slots (qcb_addr (sg) ((qID (q)))) message )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q_3)) + 4 ))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_3)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q)))) q_3 )
  **  (((queue_out_addr (q_3))) # Ptr  |-> message)
  **  (q_accept_head_slot q_3 slots )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQAccept_partial_solve_wit_9_pure := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q_2: QueueFields) (q_3: QueueFields) (message: Z) (q_4: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (message_2: Z) (PreH1 : (((queue_out_addr (q)) + 4 ) <> (queue_end_addr (q)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (0 < (queue_entries (q_4)))) (PreH6 : ((queue_entries (q_4)) <= 65535)) (PreH7 : ((queue_entries (q_3)) > 0)) (PreH8 : (0 <= (queue_entries (q_3)))) (PreH9 : ((queue_entries (q_3)) <= 65535)) (PreH10 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_accept_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (q_accept_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = errptr)) (PreH29 : (q_accept_profile sg )) (PreH30 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH31 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_accept_dequeue_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q next free slots (qcb_addr (sg) ((qID (q_2)))) message_2 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q)) + 4 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (((queue_out_addr (q)) + 4 ) = (q_accept_next_out (q))) ”
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q_2: QueueFields) (q_3: QueueFields) (message: Z) (q_4: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (message_2: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (((queue_out_addr (q)) + 4 ) <> (queue_end_addr (q)))) (PreH4 : (message = message_2)) (PreH5 : (0 < (queue_entries (q)))) (PreH6 : ((queue_entries (q)) <= 65535)) (PreH7 : (0 < (queue_entries (q_4)))) (PreH8 : ((queue_entries (q_4)) <= 65535)) (PreH9 : ((queue_entries (q_3)) > 0)) (PreH10 : (0 <= (queue_entries (q_3)))) (PreH11 : ((queue_entries (q_3)) <= 65535)) (PreH12 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_accept_profile sg )) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (valid_event_id sg eid )) (PreH24 : (q_accept_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_query_public_slot before eid observed )) (PreH27 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (pevent_pre = pe)) (PreH30 : (perr_pre = errptr)) (PreH31 : (q_accept_profile sg )) (PreH32 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH33 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_accept_dequeue_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q next free slots (qcb_addr (sg) ((qID (q_2)))) message_2 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q)) + 4 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (((queue_out_addr (q)) + 4 ) = (q_accept_next_out (q))) ”
).

Definition OSQAccept_partial_solve_wit_9_pure_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q_2: QueueFields) (q_3: QueueFields) (message: Z) (q_4: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (message_2: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (((queue_out_addr (q)) + 4 ) <> (queue_end_addr (q)))) (PreH4 : (message = message_2)) (PreH5 : (0 < (queue_entries (q)))) (PreH6 : ((queue_entries (q)) <= 65535)) (PreH7 : (0 < (queue_entries (q_4)))) (PreH8 : ((queue_entries (q_4)) <= 65535)) (PreH9 : ((queue_entries (q_3)) > 0)) (PreH10 : (0 <= (queue_entries (q_3)))) (PreH11 : ((queue_entries (q_3)) <= 65535)) (PreH12 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_accept_profile sg )) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (valid_event_id sg eid )) (PreH24 : (q_accept_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_query_public_slot before eid observed )) (PreH27 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (pevent_pre = pe)) (PreH30 : (perr_pre = errptr)) (PreH31 : (q_accept_profile sg )) (PreH32 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH33 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_accept_dequeue_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q next free slots (qcb_addr (sg) ((qID (q_2)))) message_2 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q)) + 4 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (((queue_out_addr (q)) + 4 ) = (q_accept_next_out (q))) ”
.

Definition OSQAccept_partial_solve_wit_9_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q_2: QueueFields) (q_3: QueueFields) (message: Z) (q_4: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (message_2: Z) (PreH1 : (((queue_out_addr (q)) + 4 ) <> (queue_end_addr (q)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (0 < (queue_entries (q_4)))) (PreH6 : ((queue_entries (q_4)) <= 65535)) (PreH7 : ((queue_entries (q_3)) > 0)) (PreH8 : (0 <= (queue_entries (q_3)))) (PreH9 : ((queue_entries (q_3)) <= 65535)) (PreH10 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_accept_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (q_accept_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = errptr)) (PreH29 : (q_accept_profile sg )) (PreH30 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH31 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_dequeue_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q next free slots (qcb_addr (sg) ((qID (q_2)))) message_2 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q)) + 4 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (((queue_out_addr (q)) + 4 ) = (q_accept_next_out (q))) ” 
  &&  “ (((queue_out_addr (q)) + 4 ) <> (queue_end_addr (q))) ” 
  &&  “ (message = message_2) ” 
  &&  “ (0 < (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (0 < (queue_entries (q_4))) ” 
  &&  “ ((queue_entries (q_4)) <= 65535) ” 
  &&  “ ((queue_entries (q_3)) > 0) ” 
  &&  “ (0 <= (queue_entries (q_3))) ” 
  &&  “ ((queue_entries (q_3)) <= 65535) ” 
  &&  “ (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = errptr) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_accept_api_safe critical sg invocation pe before X ) ”
  &&  (q_accept_dequeue_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q next free slots (qcb_addr (sg) ((qID (q_2)))) message )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_accept_next_out (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQAccept_partial_solve_wit_9 := OSQAccept_partial_solve_wit_9_pure -> OSQAccept_partial_solve_wit_9_aux.

Definition OSQAccept_partial_solve_wit_10_pure := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q_2: QueueFields) (q_3: QueueFields) (message: Z) (q_4: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (message_2: Z) (PreH1 : (((queue_out_addr (q)) + 4 ) = (queue_end_addr (q)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (0 < (queue_entries (q_4)))) (PreH6 : ((queue_entries (q_4)) <= 65535)) (PreH7 : ((queue_entries (q_3)) > 0)) (PreH8 : (0 <= (queue_entries (q_3)))) (PreH9 : ((queue_entries (q_3)) <= 65535)) (PreH10 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_accept_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (q_accept_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = errptr)) (PreH29 : (q_accept_profile sg )) (PreH30 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH31 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_accept_dequeue_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q next free slots (qcb_addr (sg) ((qID (q_2)))) message_2 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((qStart (q)) = (q_accept_next_out (q))) ”
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q_2: QueueFields) (q_3: QueueFields) (message: Z) (q_4: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (message_2: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (((queue_out_addr (q)) + 4 ) = (queue_end_addr (q)))) (PreH4 : (message = message_2)) (PreH5 : (0 < (queue_entries (q)))) (PreH6 : ((queue_entries (q)) <= 65535)) (PreH7 : (0 < (queue_entries (q_4)))) (PreH8 : ((queue_entries (q_4)) <= 65535)) (PreH9 : ((queue_entries (q_3)) > 0)) (PreH10 : (0 <= (queue_entries (q_3)))) (PreH11 : ((queue_entries (q_3)) <= 65535)) (PreH12 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_accept_profile sg )) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (valid_event_id sg eid )) (PreH24 : (q_accept_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_query_public_slot before eid observed )) (PreH27 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (pevent_pre = pe)) (PreH30 : (perr_pre = errptr)) (PreH31 : (q_accept_profile sg )) (PreH32 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH33 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_accept_dequeue_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q next free slots (qcb_addr (sg) ((qID (q_2)))) message_2 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((qStart (q)) = (q_accept_next_out (q))) ”
).

Definition OSQAccept_partial_solve_wit_10_pure_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q_2: QueueFields) (q_3: QueueFields) (message: Z) (q_4: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (message_2: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (((queue_out_addr (q)) + 4 ) = (queue_end_addr (q)))) (PreH4 : (message = message_2)) (PreH5 : (0 < (queue_entries (q)))) (PreH6 : ((queue_entries (q)) <= 65535)) (PreH7 : (0 < (queue_entries (q_4)))) (PreH8 : ((queue_entries (q_4)) <= 65535)) (PreH9 : ((queue_entries (q_3)) > 0)) (PreH10 : (0 <= (queue_entries (q_3)))) (PreH11 : ((queue_entries (q_3)) <= 65535)) (PreH12 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_accept_profile sg )) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (valid_event_id sg eid )) (PreH24 : (q_accept_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_query_public_slot before eid observed )) (PreH27 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (pevent_pre = pe)) (PreH30 : (perr_pre = errptr)) (PreH31 : (q_accept_profile sg )) (PreH32 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH33 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_accept_dequeue_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q next free slots (qcb_addr (sg) ((qID (q_2)))) message_2 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((qStart (q)) = (q_accept_next_out (q))) ”
.

Definition OSQAccept_partial_solve_wit_10_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q_2: QueueFields) (q_3: QueueFields) (message: Z) (q_4: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (next: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (message_2: Z) (PreH1 : (((queue_out_addr (q)) + 4 ) = (queue_end_addr (q)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (0 < (queue_entries (q_4)))) (PreH6 : ((queue_entries (q_4)) <= 65535)) (PreH7 : ((queue_entries (q_3)) > 0)) (PreH8 : (0 <= (queue_entries (q_3)))) (PreH9 : ((queue_entries (q_3)) <= 65535)) (PreH10 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_accept_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (q_accept_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = errptr)) (PreH29 : (q_accept_profile sg )) (PreH30 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH31 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_dequeue_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q next free slots (qcb_addr (sg) ((qID (q_2)))) message_2 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((qStart (q)) = (q_accept_next_out (q))) ” 
  &&  “ (((queue_out_addr (q)) + 4 ) = (queue_end_addr (q))) ” 
  &&  “ (message = message_2) ” 
  &&  “ (0 < (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (0 < (queue_entries (q_4))) ” 
  &&  “ ((queue_entries (q_4)) <= 65535) ” 
  &&  “ ((queue_entries (q_3)) > 0) ” 
  &&  “ (0 <= (queue_entries (q_3))) ” 
  &&  “ ((queue_entries (q_3)) <= 65535) ” 
  &&  “ (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = errptr) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_accept_api_safe critical sg invocation pe before X ) ”
  &&  (q_accept_dequeue_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q next free slots (qcb_addr (sg) ((qID (q_2)))) message )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_accept_next_out (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQAccept_partial_solve_wit_10 := OSQAccept_partial_solve_wit_10_pure -> OSQAccept_partial_solve_wit_10_aux.

Definition OSQAccept_partial_solve_wit_11_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q_2: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (PreH1 : ((queue_entries (q)) <= 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_accept_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_accept_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (q_query_public_slot before eid observed )) (PreH20 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (perr_pre = errptr)) (PreH24 : (q_accept_profile sg )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_accept_store_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "pmsg" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((queue_entries (q)) <= 0) ”
.

Definition OSQAccept_partial_solve_wit_11_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q_2: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (PreH1 : ((queue_entries (q)) <= 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_accept_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_accept_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (q_query_public_slot before eid observed )) (PreH20 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (perr_pre = errptr)) (PreH24 : (q_accept_profile sg )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_store_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((queue_entries (q)) <= 0) ” 
  &&  “ ((queue_entries (q)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = errptr) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_accept_api_safe critical sg invocation pe before X ) ”
  &&  (q_accept_store_context platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly (qcb_addr (sg) ((qID (q_2)))) q )
  **  (queue_buffer_rep q slots )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQAccept_partial_solve_wit_11 := OSQAccept_partial_solve_wit_11_pure -> OSQAccept_partial_solve_wit_11_aux.

Definition OSQAccept_partial_solve_wit_12_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (q_2: QueueFields) (message: Z) (q_3: QueueFields) (q_4: QueueFields) (message_2: Z) (entry_2: UCOS2_Verify_State) (after: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : (((queue_out_addr (q_4)) + 4 ) = (queue_end_addr (q_4)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q_4)))) (PreH4 : ((queue_entries (q_4)) <= 65535)) (PreH5 : (0 < (queue_entries (q_3)))) (PreH6 : ((queue_entries (q_3)) <= 65535)) (PreH7 : ((queue_entries (q_2)) > 0)) (PreH8 : (0 <= (queue_entries (q_2)))) (PreH9 : ((queue_entries (q_2)) <= 65535)) (PreH10 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_accept_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (q_accept_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = errptr)) (PreH29 : (q_accept_profile sg )) (PreH30 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH31 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_accept_restore_pre platform critical sg invocation origin mask retval before entry_2 after eid observed current_2 message q_accept_success )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 0)
|--
  “ (retval = retval) ”
.

Definition OSQAccept_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q_2: QueueFields) (message: Z) (q_3: QueueFields) (q_4: QueueFields) (message_2: Z) (entry_2: UCOS2_Verify_State) (after: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : (((queue_out_addr (q_4)) + 4 ) = (queue_end_addr (q_4)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q_4)))) (PreH4 : ((queue_entries (q_4)) <= 65535)) (PreH5 : (0 < (queue_entries (q_3)))) (PreH6 : ((queue_entries (q_3)) <= 65535)) (PreH7 : ((queue_entries (q_2)) > 0)) (PreH8 : (0 <= (queue_entries (q_2)))) (PreH9 : ((queue_entries (q_2)) <= 65535)) (PreH10 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_accept_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (q_accept_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = errptr)) (PreH29 : (q_accept_profile sg )) (PreH30 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH31 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_restore_pre platform critical sg invocation origin mask retval before entry_2 after eid observed current_2 message q_accept_success )
  **  ((perr_pre) # UChar  |-> 0)
|--
  “ (retval = retval) ” 
  &&  “ (((queue_out_addr (q_4)) + 4 ) = (queue_end_addr (q_4))) ” 
  &&  “ (message = message_2) ” 
  &&  “ (0 < (queue_entries (q_4))) ” 
  &&  “ ((queue_entries (q_4)) <= 65535) ” 
  &&  “ (0 < (queue_entries (q_3))) ” 
  &&  “ ((queue_entries (q_3)) <= 65535) ” 
  &&  “ ((queue_entries (q_2)) > 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = errptr) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_accept_api_safe critical sg invocation pe before X ) ”
  &&  (q_accept_restore_pre platform critical sg invocation origin mask retval before entry_2 after eid observed current_2 message_2 q_accept_success )
  **  ((perr_pre) # UChar  |-> 0)
.

Definition OSQAccept_partial_solve_wit_12 := OSQAccept_partial_solve_wit_12_pure -> OSQAccept_partial_solve_wit_12_aux.

Definition OSQAccept_partial_solve_wit_13_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (q_2: QueueFields) (message: Z) (q_3: QueueFields) (q_4: QueueFields) (message_2: Z) (entry_2: UCOS2_Verify_State) (after: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : (((queue_out_addr (q_4)) + 4 ) <> (queue_end_addr (q_4)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q_4)))) (PreH4 : ((queue_entries (q_4)) <= 65535)) (PreH5 : (0 < (queue_entries (q_3)))) (PreH6 : ((queue_entries (q_3)) <= 65535)) (PreH7 : ((queue_entries (q_2)) > 0)) (PreH8 : (0 <= (queue_entries (q_2)))) (PreH9 : ((queue_entries (q_2)) <= 65535)) (PreH10 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_accept_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (q_accept_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = errptr)) (PreH29 : (q_accept_profile sg )) (PreH30 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH31 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_accept_restore_pre platform critical sg invocation origin mask retval before entry_2 after eid observed current_2 message q_accept_success )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 0)
|--
  “ (retval = retval) ”
.

Definition OSQAccept_partial_solve_wit_13_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q_2: QueueFields) (message: Z) (q_3: QueueFields) (q_4: QueueFields) (message_2: Z) (entry_2: UCOS2_Verify_State) (after: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : (((queue_out_addr (q_4)) + 4 ) <> (queue_end_addr (q_4)))) (PreH2 : (message = message_2)) (PreH3 : (0 < (queue_entries (q_4)))) (PreH4 : ((queue_entries (q_4)) <= 65535)) (PreH5 : (0 < (queue_entries (q_3)))) (PreH6 : ((queue_entries (q_3)) <= 65535)) (PreH7 : ((queue_entries (q_2)) > 0)) (PreH8 : (0 <= (queue_entries (q_2)))) (PreH9 : ((queue_entries (q_2)) <= 65535)) (PreH10 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_accept_profile sg )) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (valid_event_id sg eid )) (PreH22 : (q_accept_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_query_public_slot before eid observed )) (PreH25 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = errptr)) (PreH29 : (q_accept_profile sg )) (PreH30 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH31 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_restore_pre platform critical sg invocation origin mask retval before entry_2 after eid observed current_2 message q_accept_success )
  **  ((perr_pre) # UChar  |-> 0)
|--
  “ (retval = retval) ” 
  &&  “ (((queue_out_addr (q_4)) + 4 ) <> (queue_end_addr (q_4))) ” 
  &&  “ (message = message_2) ” 
  &&  “ (0 < (queue_entries (q_4))) ” 
  &&  “ ((queue_entries (q_4)) <= 65535) ” 
  &&  “ (0 < (queue_entries (q_3))) ” 
  &&  “ ((queue_entries (q_3)) <= 65535) ” 
  &&  “ ((queue_entries (q_2)) > 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = errptr) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_accept_api_safe critical sg invocation pe before X ) ”
  &&  (q_accept_restore_pre platform critical sg invocation origin mask retval before entry_2 after eid observed current_2 message_2 q_accept_success )
  **  ((perr_pre) # UChar  |-> 0)
.

Definition OSQAccept_partial_solve_wit_13 := OSQAccept_partial_solve_wit_13_pure -> OSQAccept_partial_solve_wit_13_aux.

Definition OSQAccept_partial_solve_wit_14_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q: QueueFields) (q_2: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : ((queue_entries (q_2)) <= 0)) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_accept_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_accept_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (perr_pre = errptr)) (PreH23 : (q_accept_profile sg )) (PreH24 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH25 : (q_accept_api_safe critical sg invocation pe before X )) ,
  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_accept_restore_pre platform critical sg invocation origin mask retval before entry_2 entry_2 eid observed current_2 0 q_accept_empty )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 31)
|--
  “ (retval = retval) ”
.

Definition OSQAccept_partial_solve_wit_14_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: ((OSErrCode * Z) -> (UCOS2_Verify_State -> Prop))) (errptr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (q_2: QueueFields) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : ((queue_entries (q_2)) <= 0)) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current )) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_accept_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (valid_event_id sg eid )) (PreH16 : (q_accept_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_query_public_slot before eid observed )) (PreH19 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (perr_pre = errptr)) (PreH23 : (q_accept_profile sg )) (PreH24 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH25 : (q_accept_api_safe critical sg invocation pe before X )) ,
  (q_accept_restore_pre platform critical sg invocation origin mask retval before entry_2 entry_2 eid observed current_2 0 q_accept_empty )
  **  ((perr_pre) # UChar  |-> 31)
|--
  “ (retval = retval) ” 
  &&  “ ((queue_entries (q_2)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (q_accept_acquire_facts critical sg invocation eid mask retval before entry observed current ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = errptr) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ” 
  &&  “ (q_accept_api_safe critical sg invocation pe before X ) ”
  &&  (q_accept_restore_pre platform critical sg invocation origin mask retval before entry_2 entry_2 eid observed current_2 0 q_accept_empty )
  **  ((perr_pre) # UChar  |-> 31)
.

Definition OSQAccept_partial_solve_wit_14 := OSQAccept_partial_solve_wit_14_pure -> OSQAccept_partial_solve_wit_14_aux.

Definition OSQAccept_which_implies_wit_1 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (q_accept_profile sg )) (PreH3 : (q_accept_call_input critical sg invocation pe before eid observed )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (q_accept_call_input critical sg invocation pe before eid observed ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (q_accept_profile sg )) (PreH3 : (q_accept_call_input critical sg invocation pe before eid observed )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (q_query_public_slot before eid observed ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
).

Definition OSQAccept_which_implies_wit_1_split_goal_1 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (q_accept_profile sg )) (PreH3 : (q_accept_call_input critical sg invocation pe before eid observed )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (q_query_public_slot before eid observed ) ”
.

Definition OSQAccept_which_implies_wit_1_split_goal_2 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (q_accept_profile sg )) (PreH3 : (q_accept_call_input critical sg invocation pe before eid observed )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSQAccept_which_implies_wit_1_split_goal_3 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (q_accept_profile sg )) (PreH3 : (q_accept_call_input critical sg invocation pe before eid observed )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (valid_event_id sg eid ) ”
.

Definition OSQAccept_which_implies_wit_1_split_goal_4 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (q_accept_profile sg )) (PreH3 : (q_accept_call_input critical sg invocation pe before eid observed )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSQAccept_which_implies_wit_1_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (q_accept_profile sg )) (PreH3 : (q_accept_call_input critical sg invocation pe before eid observed )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
.

Definition OSQAccept_which_implies_wit_2 := 
(
forall (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pevent: Z) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (q_accept_profile sg )) (PreH3 : (pevent = (event_addr (sg) (eid)))) (PreH4 : (valid_event_id sg eid )) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
) \/
(
forall (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pevent: Z) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (q_accept_profile sg )) (PreH3 : (pevent = (event_addr (sg) (eid)))) (PreH4 : (valid_event_id sg eid )) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
).

Definition OSQAccept_which_implies_wit_2_split_goal_spatial := 
forall (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (pevent: Z) (PreH1 : (UCOS2_state_inv sg before )) (PreH2 : (q_accept_profile sg )) (PreH3 : (pevent = (event_addr (sg) (eid)))) (PreH4 : (valid_event_id sg eid )) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSQAccept_which_implies_wit_3 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (q_accept_profile sg )) (PreH4 : (valid_event_id sg eid )) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (q_query_public_slot before eid observed )) (PreH7 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_accept_profile sg ) ”
  &&  (q_accept_save_pre platform critical sg invocation origin mask before eid observed )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (q_accept_profile sg )) (PreH4 : (valid_event_id sg eid )) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (q_query_public_slot before eid observed )) (PreH7 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
|--
  (q_accept_save_pre platform critical sg invocation origin mask before eid observed )
).

Definition OSQAccept_which_implies_wit_3_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (UCOS2_state_inv sg before )) (PreH3 : (q_accept_profile sg )) (PreH4 : (valid_event_id sg eid )) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (q_query_public_slot before eid observed )) (PreH7 : (q_accept_call_input critical sg invocation pe before eid observed )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_accept_type_frame sg before eid )
|--
  (q_accept_save_pre platform critical sg invocation origin mask before eid observed )
.

Definition OSQAccept_which_implies_wit_4 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (pevent: Z) (PreH1 : (q_accept_acquire_facts critical sg invocation eid mask cpu_sr before entry_2 observed current_2 )) (PreH2 : (q_accept_profile sg )) (PreH3 : (valid_event_id sg eid )) (PreH4 : (pevent = (event_addr (sg) (eid)))) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_accept_pointer_context platform critical sg invocation origin mask cpu_sr before entry eid observed current q )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (pevent: Z) (PreH1 : (q_accept_acquire_facts critical sg invocation eid mask cpu_sr before entry_2 observed current_2 )) (PreH2 : (q_accept_profile sg )) (PreH3 : (valid_event_id sg eid )) (PreH4 : (pevent = (event_addr (sg) (eid)))) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_accept_pointer_context platform critical sg invocation origin mask cpu_sr before entry eid observed current q )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
).

Definition OSQAccept_which_implies_wit_5 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (pevent: Z) (cpu_sr: Z) (PreH1 : (pq = (qcb_addr (sg) ((qID (q_2)))))) (PreH2 : (pevent = (event_addr (sg) (eid)))) ,
  (q_accept_pointer_context platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ”
  &&  (q_accept_store_context platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (pevent: Z) (cpu_sr: Z) (PreH1 : (pq = (qcb_addr (sg) ((qID (q_2)))))) (PreH2 : (pevent = (event_addr (sg) (eid)))) ,
  (q_accept_pointer_context platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ”
  &&  (q_accept_store_context platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
).

Definition OSQAccept_which_implies_wit_6 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q_2)) > 0)) ,
  (q_accept_store_context platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  (q_accept_qcb_readonly pq q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (next: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z)))  (message: Z)  (q: QueueFields) ,
  “ (0 < (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ”
  &&  (q_accept_dequeue_context platform critical sg invocation origin mask cpu_sr before entry eid observed current q next free slots pq message )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly pq q )
  **  (((queue_out_addr (q))) # Ptr  |-> message)
  **  (q_accept_head_slot q slots )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q_2)) > 0)) ,
  (q_accept_store_context platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 pq )
  **  (q_accept_qcb_readonly pq q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (next: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z)))  (message: Z)  (q: QueueFields) ,
  “ ((qStart (q_2)) = (qStart (q))) ” 
  &&  “ ((queue_end_addr (q_2)) = (queue_end_addr (q))) ” 
  &&  “ ((queue_entries (q_2)) = (queue_entries (q))) ” 
  &&  “ ((queue_out_addr (q_2)) = (queue_out_addr (q))) ” 
  &&  “ (0 < (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ”
  &&  (q_accept_dequeue_context platform critical sg invocation origin mask cpu_sr before entry eid observed current q next free slots pq message )
  **  (q_accept_qcb_readonly pq q )
  **  (((queue_out_addr (q))) # Ptr  |-> message)
  **  (q_accept_head_slot q slots )
).

Definition OSQAccept_which_implies_wit_7 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (message: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (next_2: QueueFields) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) ,
  (q_accept_dequeue_context platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 next_2 free_2 slots_2 pq message )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q_2)) + 4 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  (q_accept_qcb_readonly pq q_2 )
  **  (((queue_out_addr (q_2))) # Ptr  |-> message)
  **  (q_accept_head_slot q_2 slots_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (next: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields)  (message_2: Z) ,
  “ (message = message_2) ” 
  &&  “ (0 < (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ”
  &&  (q_accept_dequeue_context platform critical sg invocation origin mask cpu_sr before entry eid observed current q next free slots pq message_2 )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q)) + 4 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (message: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (next_2: QueueFields) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) ,
  (q_accept_dequeue_context platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 next_2 free_2 slots_2 pq message )
  **  (q_accept_qcb_readonly pq q_2 )
  **  (((queue_out_addr (q_2))) # Ptr  |-> message)
  **  (q_accept_head_slot q_2 slots_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (next: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ ((qStart (q_2)) = (qStart (q))) ” 
  &&  “ ((queue_end_addr (q_2)) = (queue_end_addr (q))) ” 
  &&  “ ((queue_entries (q_2)) = (queue_entries (q))) ” 
  &&  “ (((queue_out_addr (q_2)) + 4 ) = ((queue_out_addr (q)) + 4 )) ” 
  &&  “ (0 < (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ”
  &&  (q_accept_dequeue_context platform critical sg invocation origin mask cpu_sr before entry eid observed current q next free slots pq message )
  **  (q_accept_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
).

Definition OSQAccept_which_implies_wit_8 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (message: Z) (slots: (@list (@option Z))) (free: (@list Z)) (next: QueueFields) (q: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) ,
  (q_accept_dequeue_context platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q next free slots pq message )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_accept_next_out (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
|--
  EX (entry: UCOS2_Verify_State)  (after: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  (q_accept_restore_pre platform critical sg invocation origin mask cpu_sr before entry after eid observed current message q_accept_success )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (message: Z) (slots: (@list (@option Z))) (free: (@list Z)) (next: QueueFields) (q: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) ,
  (q_accept_dequeue_context platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q next free slots pq message )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_accept_next_out (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) - 1 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
|--
  EX (entry: UCOS2_Verify_State)  (after: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  (q_accept_restore_pre platform critical sg invocation origin mask cpu_sr before entry after eid observed current message q_accept_success )
).

Definition OSQAccept_which_implies_wit_9 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q)) <= 0)) ,
  (q_accept_store_context platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  (q_accept_restore_pre platform critical sg invocation origin mask cpu_sr before entry entry eid observed current 0 q_accept_empty )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q)) <= 0)) ,
  (q_accept_store_context platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  (q_accept_qcb_readonly pq q )
  **  (queue_buffer_rep q slots )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  (q_accept_restore_pre platform critical sg invocation origin mask cpu_sr before entry entry eid observed current 0 q_accept_empty )
).

Module Type VC_Correct.


Axiom proof_of_OSQAccept_safety_wit_1 : OSQAccept_safety_wit_1.
Axiom proof_of_OSQAccept_safety_wit_2 : OSQAccept_safety_wit_2.
Axiom proof_of_OSQAccept_safety_wit_3 : OSQAccept_safety_wit_3.
Axiom proof_of_OSQAccept_safety_wit_4 : OSQAccept_safety_wit_4.
Axiom proof_of_OSQAccept_safety_wit_5 : OSQAccept_safety_wit_5.
Axiom proof_of_OSQAccept_safety_wit_6 : OSQAccept_safety_wit_6.
Axiom proof_of_OSQAccept_safety_wit_7 : OSQAccept_safety_wit_7.
Axiom proof_of_OSQAccept_safety_wit_8 : OSQAccept_safety_wit_8.
Axiom proof_of_OSQAccept_entail_wit_1 : OSQAccept_entail_wit_1.
Axiom proof_of_OSQAccept_return_wit_1 : OSQAccept_return_wit_1.
Axiom proof_of_OSQAccept_return_wit_2 : OSQAccept_return_wit_2.
Axiom proof_of_OSQAccept_return_wit_3 : OSQAccept_return_wit_3.
Axiom proof_of_OSQAccept_return_wit_4 : OSQAccept_return_wit_4.
Axiom proof_of_OSQAccept_return_wit_5 : OSQAccept_return_wit_5.
Axiom proof_of_OSQAccept_partial_solve_wit_1_pure : OSQAccept_partial_solve_wit_1_pure.
Axiom proof_of_OSQAccept_partial_solve_wit_1 : OSQAccept_partial_solve_wit_1.
Axiom proof_of_OSQAccept_partial_solve_wit_2_pure : OSQAccept_partial_solve_wit_2_pure.
Axiom proof_of_OSQAccept_partial_solve_wit_2 : OSQAccept_partial_solve_wit_2.
Axiom proof_of_OSQAccept_partial_solve_wit_3_pure : OSQAccept_partial_solve_wit_3_pure.
Axiom proof_of_OSQAccept_partial_solve_wit_3 : OSQAccept_partial_solve_wit_3.
Axiom proof_of_OSQAccept_partial_solve_wit_4 : OSQAccept_partial_solve_wit_4.
Axiom proof_of_OSQAccept_partial_solve_wit_5_pure : OSQAccept_partial_solve_wit_5_pure.
Axiom proof_of_OSQAccept_partial_solve_wit_5 : OSQAccept_partial_solve_wit_5.
Axiom proof_of_OSQAccept_partial_solve_wit_6_pure : OSQAccept_partial_solve_wit_6_pure.
Axiom proof_of_OSQAccept_partial_solve_wit_6 : OSQAccept_partial_solve_wit_6.
Axiom proof_of_OSQAccept_partial_solve_wit_7_pure : OSQAccept_partial_solve_wit_7_pure.
Axiom proof_of_OSQAccept_partial_solve_wit_7 : OSQAccept_partial_solve_wit_7.
Axiom proof_of_OSQAccept_partial_solve_wit_8 : OSQAccept_partial_solve_wit_8.
Axiom proof_of_OSQAccept_partial_solve_wit_9_pure : OSQAccept_partial_solve_wit_9_pure.
Axiom proof_of_OSQAccept_partial_solve_wit_9 : OSQAccept_partial_solve_wit_9.
Axiom proof_of_OSQAccept_partial_solve_wit_10_pure : OSQAccept_partial_solve_wit_10_pure.
Axiom proof_of_OSQAccept_partial_solve_wit_10 : OSQAccept_partial_solve_wit_10.
Axiom proof_of_OSQAccept_partial_solve_wit_11_pure : OSQAccept_partial_solve_wit_11_pure.
Axiom proof_of_OSQAccept_partial_solve_wit_11 : OSQAccept_partial_solve_wit_11.
Axiom proof_of_OSQAccept_partial_solve_wit_12_pure : OSQAccept_partial_solve_wit_12_pure.
Axiom proof_of_OSQAccept_partial_solve_wit_12 : OSQAccept_partial_solve_wit_12.
Axiom proof_of_OSQAccept_partial_solve_wit_13_pure : OSQAccept_partial_solve_wit_13_pure.
Axiom proof_of_OSQAccept_partial_solve_wit_13 : OSQAccept_partial_solve_wit_13.
Axiom proof_of_OSQAccept_partial_solve_wit_14_pure : OSQAccept_partial_solve_wit_14_pure.
Axiom proof_of_OSQAccept_partial_solve_wit_14 : OSQAccept_partial_solve_wit_14.
Axiom proof_of_OSQAccept_which_implies_wit_1 : OSQAccept_which_implies_wit_1.
Axiom proof_of_OSQAccept_which_implies_wit_2 : OSQAccept_which_implies_wit_2.
Axiom proof_of_OSQAccept_which_implies_wit_3 : OSQAccept_which_implies_wit_3.
Axiom proof_of_OSQAccept_which_implies_wit_4 : OSQAccept_which_implies_wit_4.
Axiom proof_of_OSQAccept_which_implies_wit_5 : OSQAccept_which_implies_wit_5.
Axiom proof_of_OSQAccept_which_implies_wit_6 : OSQAccept_which_implies_wit_6.
Axiom proof_of_OSQAccept_which_implies_wit_7 : OSQAccept_which_implies_wit_7.
Axiom proof_of_OSQAccept_which_implies_wit_8 : OSQAccept_which_implies_wit_8.
Axiom proof_of_OSQAccept_which_implies_wit_9 : OSQAccept_which_implies_wit_9.

End VC_Correct.
