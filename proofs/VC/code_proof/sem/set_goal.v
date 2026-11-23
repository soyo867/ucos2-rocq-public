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
Require Import Ucos2Verify.VC.code.sem.spec.sem_set_call_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.VC.code.sem.spec.sem_set_source_api_spec.
Local Open Scope sac.

(*----- Function OSSemSet -----*)

Definition OSSemSet_safety_wit_1 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (perr_pre = pd)) (PreH3 : (cnt_pre = requested)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) ,
  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemSet_safety_wit_2 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (perr_pre = pd)) (PreH3 : (cnt_pre = requested)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemSet_safety_wit_3 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (perr_pre = pd)) (PreH3 : (cnt_pre = requested)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (pevent_pre = 0)) ,
  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemSet_safety_wit_4 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (cnt_pre = requested)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) ,
  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSSemSet_safety_wit_5 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (cnt_pre = requested)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ False ”
.

Definition OSSemSet_safety_wit_6 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (cnt_pre = requested)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (pevent_pre = 0)) ,
  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSSemSet_safety_wit_7 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = pe)) (PreH10 : (perr_pre = pd)) (PreH11 : (cnt_pre = requested)) (PreH12 : (0 <= requested)) (PreH13 : (requested <= 65535)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH17 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ False ”
.

Definition OSSemSet_safety_wit_8 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = pe)) (PreH10 : (perr_pre = pd)) (PreH11 : (cnt_pre = requested)) (PreH12 : (0 <= requested)) (PreH13 : (requested <= 65535)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  “ False ”
.

Definition OSSemSet_safety_wit_9 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH10 : (pevent_pre <> 0)) (PreH11 : (pevent_pre = pe)) (PreH12 : (perr_pre = pd)) (PreH13 : (cnt_pre = requested)) (PreH14 : (0 <= requested)) (PreH15 : (requested <= 65535)) (PreH16 : (pevent_pre <> 0)) (PreH17 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemSet_safety_wit_10 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (sem_set_checkpoint (entry) (eid) (current_2) (requested)) after )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : ((encode_event_cnt_value (current)) > 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= requested)) (PreH9 : (requested <= 65535)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH11 : (0 <= (encode_event_cnt_value (current)))) (PreH12 : ((encode_event_cnt_value (current)) <= 65535)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (perr_pre = pd)) (PreH25 : (cnt_pre = requested)) (PreH26 : (0 <= requested)) (PreH27 : (requested <= 65535)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH30 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH31 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current_2)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "cnt" ) )) # UShort  |-> requested)
  **  ((pd) # UChar  |-> (sem_set_error (entry) (current_2)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemSet_safety_wit_11 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (current_3: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (sem_set_checkpoint (entry_2) (eid) (current_3) (requested)) after )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current_2))) ((TskState (entry))))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= requested)) (PreH9 : (requested <= 65535)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH11 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH13 : ((encode_event_cnt_value (current)) <= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (0 <= requested)) (PreH16 : (requested <= 65535)) (PreH17 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH18 : (0 <= (encode_event_cnt_value (current)))) (PreH19 : ((encode_event_cnt_value (current)) <= 65535)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH22 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH23 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (0 >= 0)) (PreH27 : (pe = (event_addr (sg) (eid)))) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (perr_pre = pd)) (PreH32 : (cnt_pre = requested)) (PreH33 : (0 <= requested)) (PreH34 : (requested <= 65535)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH37 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH38 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry_2) (observed) (current_3)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "cnt" ) )) # UShort  |-> requested)
  **  ((pd) # UChar  |-> (sem_set_error (entry_2) (current_3)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemSet_safety_wit_12 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (current_3: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (sem_set_checkpoint (entry_2) (eid) (current_3) (requested)) after )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current_2))) ((TskState (entry))))) (32)) <> 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= requested)) (PreH9 : (requested <= 65535)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH11 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH13 : ((encode_event_cnt_value (current)) <= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (0 <= requested)) (PreH16 : (requested <= 65535)) (PreH17 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH18 : (0 <= (encode_event_cnt_value (current)))) (PreH19 : ((encode_event_cnt_value (current)) <= 65535)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH22 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH23 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (0 >= 0)) (PreH27 : (pe = (event_addr (sg) (eid)))) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (perr_pre = pd)) (PreH32 : (cnt_pre = requested)) (PreH33 : (0 <= requested)) (PreH34 : (requested <= 65535)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH37 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH38 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry_2) (observed) (current_3)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "cnt" ) )) # UShort  |-> requested)
  **  ((pd) # UChar  |-> (sem_set_error (entry_2) (current_3)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemSet_entail_wit_1_1 := 
(
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH3 : (pevent_pre <> 0)) (PreH4 : (pevent_pre = pe)) (PreH5 : (perr_pre = pd)) (PreH6 : (cnt_pre = requested)) (PreH7 : (0 <= requested)) (PreH8 : (requested <= 65535)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <> 3) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
) \/
(
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (requested: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH5 : (pevent_pre <> 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (perr_pre = pd)) (PreH8 : (cnt_pre = requested)) (PreH9 : (0 <= requested)) (PreH10 : (requested <= 65535)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ”
  &&  emp
).

Definition OSSemSet_entail_wit_1_1_split_goal_1 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (requested: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH5 : (pevent_pre <> 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (perr_pre = pd)) (PreH8 : (cnt_pre = requested)) (PreH9 : (0 <= requested)) (PreH10 : (requested <= 65535)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) ,
  ((event_slot_type_value ((EventState (before))) (eid)) <= 255)
.

Definition OSSemSet_entail_wit_1_1_split_goal_2 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (requested: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH5 : (pevent_pre <> 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (perr_pre = pd)) (PreH8 : (cnt_pre = requested)) (PreH9 : (0 <= requested)) (PreH10 : (requested <= 65535)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) ,
  (0 <= (event_slot_type_value ((EventState (before))) (eid)))
.

Definition OSSemSet_entail_wit_1_2 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH3 : (pevent_pre <> 0)) (PreH4 : (pevent_pre = pe)) (PreH5 : (perr_pre = pd)) (PreH6 : (cnt_pre = requested)) (PreH7 : (0 <= requested)) (PreH8 : (requested <= 65535)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
.

Definition OSSemSet_return_wit_1 := 
(
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = pe)) (PreH10 : (perr_pre = pd)) (PreH11 : (cnt_pre = requested)) (PreH12 : (0 <= requested)) (PreH13 : (requested <= 65535)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((pd) # UChar  |-> 1)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  (sem_set_source_api_post platform critical sg invocation origin mask before pe requested pd X )
) \/
(
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = pe)) (PreH10 : (perr_pre = pd)) (PreH11 : (cnt_pre = requested)) (PreH12 : (0 <= requested)) (PreH13 : (requested <= 65535)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((pd) # UChar  |-> 1)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  (sem_set_source_api_post platform critical sg invocation origin mask before pe requested pd X )
).

Definition OSSemSet_return_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = pe)) (PreH10 : (perr_pre = pd)) (PreH11 : (cnt_pre = requested)) (PreH12 : (0 <= requested)) (PreH13 : (requested <= 65535)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((pd) # UChar  |-> 1)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  (sem_set_source_api_post platform critical sg invocation origin mask before pe requested pd X )
.

Definition OSSemSet_return_wit_2 := 
(
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (cnt_pre = requested)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (pevent_pre = 0)) ,
  ((pd) # UChar  |-> 4)
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (sem_set_source_api_post platform critical sg invocation origin mask before pe requested pd X )
) \/
(
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (cnt_pre = requested)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (pevent_pre = 0)) ,
  ((pd) # UChar  |-> 4)
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (sem_set_source_api_post platform critical sg invocation origin mask before pe requested pd X )
).

Definition OSSemSet_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (cnt_pre = requested)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (pevent_pre = 0)) ,
  ((pd) # UChar  |-> 4)
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (sem_set_source_api_post platform critical sg invocation origin mask before pe requested pd X )
.

Definition OSSemSet_return_wit_3 := 
(
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (sem_set_checkpoint (entry) (eid) (current_2) (requested)) after )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : ((encode_event_cnt_value (current)) > 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= requested)) (PreH9 : (requested <= 65535)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH11 : (0 <= (encode_event_cnt_value (current)))) (PreH12 : ((encode_event_cnt_value (current)) <= 65535)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (perr_pre = pd)) (PreH25 : (cnt_pre = requested)) (PreH26 : (0 <= requested)) (PreH27 : (requested <= 65535)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH30 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH31 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current_2)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry) (current_2)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  (sem_set_source_api_post platform critical sg invocation origin mask before pe requested pd X )
) \/
(
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (sem_set_checkpoint (entry) (eid) (current_2) (requested)) after )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : ((encode_event_cnt_value (current)) > 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= requested)) (PreH9 : (requested <= 65535)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH11 : (0 <= (encode_event_cnt_value (current)))) (PreH12 : ((encode_event_cnt_value (current)) <= 65535)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (perr_pre = pd)) (PreH25 : (cnt_pre = requested)) (PreH26 : (0 <= requested)) (PreH27 : (requested <= 65535)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH30 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH31 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current_2)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry) (current_2)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  (sem_set_source_api_post platform critical sg invocation origin mask before pe requested pd X )
).

Definition OSSemSet_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (sem_set_checkpoint (entry) (eid) (current_2) (requested)) after )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : ((encode_event_cnt_value (current)) > 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= requested)) (PreH9 : (requested <= 65535)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH11 : (0 <= (encode_event_cnt_value (current)))) (PreH12 : ((encode_event_cnt_value (current)) <= 65535)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (perr_pre = pd)) (PreH25 : (cnt_pre = requested)) (PreH26 : (0 <= requested)) (PreH27 : (requested <= 65535)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH30 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH31 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current_2)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry) (current_2)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  (sem_set_source_api_post platform critical sg invocation origin mask before pe requested pd X )
.

Definition OSSemSet_return_wit_4 := 
(
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (current_3: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (sem_set_checkpoint (entry_2) (eid) (current_3) (requested)) after )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current_2))) ((TskState (entry))))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= requested)) (PreH9 : (requested <= 65535)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH11 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH13 : ((encode_event_cnt_value (current)) <= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (0 <= requested)) (PreH16 : (requested <= 65535)) (PreH17 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH18 : (0 <= (encode_event_cnt_value (current)))) (PreH19 : ((encode_event_cnt_value (current)) <= 65535)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH22 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH23 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (0 >= 0)) (PreH27 : (pe = (event_addr (sg) (eid)))) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (perr_pre = pd)) (PreH32 : (cnt_pre = requested)) (PreH33 : (0 <= requested)) (PreH34 : (requested <= 65535)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH37 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH38 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry_2) (observed) (current_3)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry_2) (current_3)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  (sem_set_source_api_post platform critical sg invocation origin mask before pe requested pd X )
) \/
(
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (current_3: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (sem_set_checkpoint (entry_2) (eid) (current_3) (requested)) after )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current_2))) ((TskState (entry))))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= requested)) (PreH9 : (requested <= 65535)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH11 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH13 : ((encode_event_cnt_value (current)) <= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (0 <= requested)) (PreH16 : (requested <= 65535)) (PreH17 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH18 : (0 <= (encode_event_cnt_value (current)))) (PreH19 : ((encode_event_cnt_value (current)) <= 65535)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH22 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH23 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (0 >= 0)) (PreH27 : (pe = (event_addr (sg) (eid)))) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (perr_pre = pd)) (PreH32 : (cnt_pre = requested)) (PreH33 : (0 <= requested)) (PreH34 : (requested <= 65535)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH37 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH38 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry_2) (observed) (current_3)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry_2) (current_3)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  (sem_set_source_api_post platform critical sg invocation origin mask before pe requested pd X )
).

Definition OSSemSet_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (current_3: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (sem_set_checkpoint (entry_2) (eid) (current_3) (requested)) after )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current_2))) ((TskState (entry))))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= requested)) (PreH9 : (requested <= 65535)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH11 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH13 : ((encode_event_cnt_value (current)) <= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (0 <= requested)) (PreH16 : (requested <= 65535)) (PreH17 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH18 : (0 <= (encode_event_cnt_value (current)))) (PreH19 : ((encode_event_cnt_value (current)) <= 65535)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH22 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH23 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (0 >= 0)) (PreH27 : (pe = (event_addr (sg) (eid)))) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (perr_pre = pd)) (PreH32 : (cnt_pre = requested)) (PreH33 : (0 <= requested)) (PreH34 : (requested <= 65535)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH37 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH38 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry_2) (observed) (current_3)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry_2) (current_3)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  (sem_set_source_api_post platform critical sg invocation origin mask before pe requested pd X )
.

Definition OSSemSet_return_wit_5 := 
(
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (current_3: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (sem_set_checkpoint (entry_2) (eid) (current_3) (requested)) after )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current_2))) ((TskState (entry))))) (32)) <> 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= requested)) (PreH9 : (requested <= 65535)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH11 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH13 : ((encode_event_cnt_value (current)) <= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (0 <= requested)) (PreH16 : (requested <= 65535)) (PreH17 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH18 : (0 <= (encode_event_cnt_value (current)))) (PreH19 : ((encode_event_cnt_value (current)) <= 65535)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH22 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH23 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (0 >= 0)) (PreH27 : (pe = (event_addr (sg) (eid)))) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (perr_pre = pd)) (PreH32 : (cnt_pre = requested)) (PreH33 : (0 <= requested)) (PreH34 : (requested <= 65535)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH37 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH38 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry_2) (observed) (current_3)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry_2) (current_3)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  (sem_set_source_api_post platform critical sg invocation origin mask before pe requested pd X )
) \/
(
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (current_3: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (sem_set_checkpoint (entry_2) (eid) (current_3) (requested)) after )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current_2))) ((TskState (entry))))) (32)) <> 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= requested)) (PreH9 : (requested <= 65535)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH11 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH13 : ((encode_event_cnt_value (current)) <= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (0 <= requested)) (PreH16 : (requested <= 65535)) (PreH17 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH18 : (0 <= (encode_event_cnt_value (current)))) (PreH19 : ((encode_event_cnt_value (current)) <= 65535)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH22 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH23 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (0 >= 0)) (PreH27 : (pe = (event_addr (sg) (eid)))) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (perr_pre = pd)) (PreH32 : (cnt_pre = requested)) (PreH33 : (0 <= requested)) (PreH34 : (requested <= 65535)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH37 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH38 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry_2) (observed) (current_3)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry_2) (current_3)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  (sem_set_source_api_post platform critical sg invocation origin mask before pe requested pd X )
).

Definition OSSemSet_return_wit_5_split_goal_spatial := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (current_3: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (sem_set_checkpoint (entry_2) (eid) (current_3) (requested)) after )) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current_2))) ((TskState (entry))))) (32)) <> 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= requested)) (PreH9 : (requested <= 65535)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH11 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH13 : ((encode_event_cnt_value (current)) <= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (0 <= requested)) (PreH16 : (requested <= 65535)) (PreH17 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH18 : (0 <= (encode_event_cnt_value (current)))) (PreH19 : ((encode_event_cnt_value (current)) <= 65535)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH22 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH23 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH25 : (0 <= UINT_MAX)) (PreH26 : (0 >= 0)) (PreH27 : (pe = (event_addr (sg) (eid)))) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (perr_pre = pd)) (PreH32 : (cnt_pre = requested)) (PreH33 : (0 <= requested)) (PreH34 : (requested <= 65535)) (PreH35 : (pevent_pre <> 0)) (PreH36 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH37 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH38 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (mutex_query_closed platform critical sg invocation origin mask after )
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry_2) (observed) (current_3)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry_2) (current_3)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  (sem_set_source_api_post platform critical sg invocation origin mask before pe requested pd X )
.

Definition OSSemSet_partial_solve_wit_1 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (perr_pre = pd)) (PreH3 : (cnt_pre = requested)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (pevent_pre = 0)) ,
  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (sem_set_error_cell pd )
|--
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre = 0) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  (sem_set_error_cell pd )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSSemSet_partial_solve_wit_2 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (perr_pre = pd)) (PreH3 : (cnt_pre = requested)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (sem_set_error_cell pd )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  (sem_set_error_cell pd )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
.

Definition OSSemSet_partial_solve_wit_3 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (perr_pre = pd)) (PreH3 : (cnt_pre = requested)) (PreH4 : (0 <= requested)) (PreH5 : (requested <= 65535)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) ,
  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (sem_set_error_cell pd )
|--
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <> 3) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  (sem_set_error_cell pd )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSSemSet_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (cnt_pre = requested)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ (pe <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
.

Definition OSSemSet_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (cnt_pre = requested)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH10 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((pd) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ (pe <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((pd) # UChar  |->_)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
.

Definition OSSemSet_partial_solve_wit_4 := OSSemSet_partial_solve_wit_4_pure -> OSSemSet_partial_solve_wit_4_aux.

Definition OSSemSet_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (cnt_pre = requested)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) ,
  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
.

Definition OSSemSet_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (cnt_pre = requested)) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <> 3)) ,
  ((pd) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <> 3) ”
  &&  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((pd) # UChar  |->_)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
.

Definition OSSemSet_partial_solve_wit_5 := OSSemSet_partial_solve_wit_5_pure -> OSSemSet_partial_solve_wit_5_aux.

Definition OSSemSet_partial_solve_wit_6_pure := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = pe)) (PreH10 : (perr_pre = pd)) (PreH11 : (cnt_pre = requested)) (PreH12 : (0 <= requested)) (PreH13 : (requested <= 65535)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH17 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ (pe <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
.

Definition OSSemSet_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = pe)) (PreH10 : (perr_pre = pd)) (PreH11 : (cnt_pre = requested)) (PreH12 : (0 <= requested)) (PreH13 : (requested <= 65535)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH17 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((pd) # UChar  |->_)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ (pe <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((pd) # UChar  |->_)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
.

Definition OSSemSet_partial_solve_wit_6 := OSSemSet_partial_solve_wit_6_pure -> OSSemSet_partial_solve_wit_6_aux.

Definition OSSemSet_partial_solve_wit_7_pure := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH10 : (pevent_pre <> 0)) (PreH11 : (pevent_pre = pe)) (PreH12 : (perr_pre = pd)) (PreH13 : (cnt_pre = requested)) (PreH14 : (0 <= requested)) (PreH15 : (requested <= 65535)) (PreH16 : (pevent_pre <> 0)) (PreH17 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ ((encode_event_type ((eventType (observed)))) = 3) ”
.

Definition OSSemSet_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH10 : (pevent_pre <> 0)) (PreH11 : (pevent_pre = pe)) (PreH12 : (perr_pre = pd)) (PreH13 : (cnt_pre = requested)) (PreH14 : (0 <= requested)) (PreH15 : (requested <= 65535)) (PreH16 : (pevent_pre <> 0)) (PreH17 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((pd) # UChar  |->_)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((pd) # UChar  |->_)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
.

Definition OSSemSet_partial_solve_wit_7 := OSSemSet_partial_solve_wit_7_pure -> OSSemSet_partial_solve_wit_7_aux.

Definition OSSemSet_partial_solve_wit_8_pure := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH10 : (pevent_pre <> 0)) (PreH11 : (pevent_pre = pe)) (PreH12 : (perr_pre = pd)) (PreH13 : (cnt_pre = requested)) (PreH14 : (0 <= requested)) (PreH15 : (requested <= 65535)) (PreH16 : (pevent_pre <> 0)) (PreH17 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
.

Definition OSSemSet_partial_solve_wit_8_aux := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH10 : (pevent_pre <> 0)) (PreH11 : (pevent_pre = pe)) (PreH12 : (perr_pre = pd)) (PreH13 : (cnt_pre = requested)) (PreH14 : (0 <= requested)) (PreH15 : (requested <= 65535)) (PreH16 : (pevent_pre <> 0)) (PreH17 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((pd) # UChar  |->_)
  **  ((( &( "cnt" ) )) # UShort  |-> cnt_pre)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "cnt" ) )) # UShort  |-> requested)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((pd) # UChar  |->_)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
.

Definition OSSemSet_partial_solve_wit_8 := OSSemSet_partial_solve_wit_8_pure -> OSSemSet_partial_solve_wit_8_aux.

Definition OSSemSet_partial_solve_wit_9_pure := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) > 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : (0 <= (encode_event_cnt_value (current)))) (PreH7 : ((encode_event_cnt_value (current)) <= 65535)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (perr_pre = pd)) (PreH20 : (cnt_pre = requested)) (PreH21 : (0 <= requested)) (PreH22 : (requested <= 65535)) (PreH23 : (pevent_pre <> 0)) (PreH24 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH25 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH26 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "cnt" ) )) # UShort  |-> requested)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> requested)
  **  (sem_set_count_frame sg entry eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((pd) # UChar  |-> 0)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((encode_event_cnt_value (current)) > 0) ”
.

Definition OSSemSet_partial_solve_wit_9_aux := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) > 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : (0 <= (encode_event_cnt_value (current)))) (PreH7 : ((encode_event_cnt_value (current)) <= 65535)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (perr_pre = pd)) (PreH20 : (cnt_pre = requested)) (PreH21 : (0 <= requested)) (PreH22 : (requested <= 65535)) (PreH23 : (pevent_pre <> 0)) (PreH24 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH25 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH26 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> requested)
  **  (sem_set_count_frame sg entry eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((pd) # UChar  |-> 0)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((encode_event_cnt_value (current)) > 0) ” 
  &&  “ ((encode_event_cnt_value (current)) > 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ (0 <= (encode_event_cnt_value (current))) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 65535) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> requested)
  **  (sem_set_count_frame sg entry eid current )
  **  ((pd) # UChar  |-> 0)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
.

Definition OSSemSet_partial_solve_wit_9 := OSSemSet_partial_solve_wit_9_pure -> OSSemSet_partial_solve_wit_9_aux.

Definition OSSemSet_partial_solve_wit_10_pure := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) <= 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : (0 <= (encode_event_cnt_value (current)))) (PreH7 : ((encode_event_cnt_value (current)) <= 65535)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (perr_pre = pd)) (PreH20 : (cnt_pre = requested)) (PreH21 : (0 <= requested)) (PreH22 : (requested <= 65535)) (PreH23 : (pevent_pre <> 0)) (PreH24 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH25 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH26 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "cnt" ) )) # UShort  |-> requested)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (sem_set_count_frame sg entry eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((pd) # UChar  |-> 0)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 0) ”
.

Definition OSSemSet_partial_solve_wit_10_aux := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) <= 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : (0 <= (encode_event_cnt_value (current)))) (PreH7 : ((encode_event_cnt_value (current)) <= 65535)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (perr_pre = pd)) (PreH20 : (cnt_pre = requested)) (PreH21 : (0 <= requested)) (PreH22 : (requested <= 65535)) (PreH23 : (pevent_pre <> 0)) (PreH24 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH25 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH26 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (sem_set_count_frame sg entry eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((pd) # UChar  |-> 0)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 0) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ (0 <= (encode_event_cnt_value (current))) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 65535) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (sem_set_count_frame sg entry eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((pd) # UChar  |-> 0)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
.

Definition OSSemSet_partial_solve_wit_10 := OSSemSet_partial_solve_wit_10_pure -> OSSemSet_partial_solve_wit_10_aux.

Definition OSSemSet_partial_solve_wit_11_pure := 
(
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current_2: OSEventAbstractState) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current))) ((TskState (entry))))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : ((encode_event_cnt_value (current)) <= 0)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH8 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (0 <= requested)) (PreH11 : (requested <= 65535)) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH13 : (0 <= (encode_event_cnt_value (current_2)))) (PreH14 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (perr_pre = pd)) (PreH27 : (cnt_pre = requested)) (PreH28 : (0 <= requested)) (PreH29 : (requested <= 65535)) (PreH30 : (pevent_pre <> 0)) (PreH31 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH32 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH33 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "cnt" ) )) # UShort  |-> requested)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> requested)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((TskState (entry)))))
  **  (sem_set_group_frame sg entry eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((pd) # UChar  |-> 0)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off )) ” 
  &&  “ ((encode_event_wait_grp ((waitList (current))) ((TskState (entry)))) = 0) ”
) \/
(
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current_2: OSEventAbstractState) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current))) ((TskState (entry))))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH8 : ((encode_event_cnt_value (current)) <= 0)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH10 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (0 <= requested)) (PreH13 : (requested <= 65535)) (PreH14 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH15 : (0 <= (encode_event_cnt_value (current_2)))) (PreH16 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = pd)) (PreH29 : (cnt_pre = requested)) (PreH30 : (0 <= requested)) (PreH31 : (requested <= 65535)) (PreH32 : (pevent_pre <> 0)) (PreH33 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH34 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH35 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "cnt" ) )) # UShort  |-> requested)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> requested)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((TskState (entry)))))
  **  (sem_set_group_frame sg entry eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((pd) # UChar  |-> 0)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  “ ((encode_event_wait_grp ((waitList (current))) ((TskState (entry)))) = 0) ”
).

Definition OSSemSet_partial_solve_wit_11_pure_split_goal_1 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current_2: OSEventAbstractState) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current))) ((TskState (entry))))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH8 : ((encode_event_cnt_value (current)) <= 0)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH10 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (0 <= requested)) (PreH13 : (requested <= 65535)) (PreH14 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH15 : (0 <= (encode_event_cnt_value (current_2)))) (PreH16 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = pd)) (PreH29 : (cnt_pre = requested)) (PreH30 : (0 <= requested)) (PreH31 : (requested <= 65535)) (PreH32 : (pevent_pre <> 0)) (PreH33 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH34 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH35 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "cnt" ) )) # UShort  |-> requested)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> requested)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((TskState (entry)))))
  **  (sem_set_group_frame sg entry eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((pd) # UChar  |-> 0)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  “ ((encode_event_wait_grp ((waitList (current))) ((TskState (entry)))) = 0) ”
.

Definition OSSemSet_partial_solve_wit_11_aux := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current_2: OSEventAbstractState) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current))) ((TskState (entry))))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : ((encode_event_cnt_value (current)) <= 0)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH8 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (0 <= requested)) (PreH11 : (requested <= 65535)) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH13 : (0 <= (encode_event_cnt_value (current_2)))) (PreH14 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (perr_pre = pd)) (PreH27 : (cnt_pre = requested)) (PreH28 : (0 <= requested)) (PreH29 : (requested <= 65535)) (PreH30 : (pevent_pre <> 0)) (PreH31 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH32 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH33 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> requested)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((TskState (entry)))))
  **  (sem_set_group_frame sg entry eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((pd) # UChar  |-> 0)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off )) ” 
  &&  “ ((encode_event_wait_grp ((waitList (current))) ((TskState (entry)))) = 0) ” 
  &&  “ ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current))) ((TskState (entry))))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off )) ” 
  &&  “ ((encode_event_cnt_value (current_2)) <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ (0 <= (encode_event_cnt_value (current_2))) ” 
  &&  “ ((encode_event_cnt_value (current_2)) <= 65535) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> requested)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((TskState (entry)))))
  **  (sem_set_group_frame sg entry eid current )
  **  ((pd) # UChar  |-> 0)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
.

Definition OSSemSet_partial_solve_wit_11 := OSSemSet_partial_solve_wit_11_pure -> OSSemSet_partial_solve_wit_11_aux.

Definition OSSemSet_partial_solve_wit_12_pure := 
(
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current_2: OSEventAbstractState) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current))) ((TskState (entry))))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : ((encode_event_cnt_value (current)) <= 0)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH8 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (0 <= requested)) (PreH11 : (requested <= 65535)) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH13 : (0 <= (encode_event_cnt_value (current_2)))) (PreH14 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (perr_pre = pd)) (PreH27 : (cnt_pre = requested)) (PreH28 : (0 <= requested)) (PreH29 : (requested <= 65535)) (PreH30 : (pevent_pre <> 0)) (PreH31 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH32 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH33 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "cnt" ) )) # UShort  |-> requested)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((TskState (entry)))))
  **  (sem_set_group_frame sg entry eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((pd) # UChar  |-> 73)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off )) ” 
  &&  “ ((encode_event_wait_grp ((waitList (current))) ((TskState (entry)))) <> 0) ”
) \/
(
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current_2: OSEventAbstractState) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current))) ((TskState (entry))))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH8 : ((encode_event_cnt_value (current)) <= 0)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH10 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (0 <= requested)) (PreH13 : (requested <= 65535)) (PreH14 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH15 : (0 <= (encode_event_cnt_value (current_2)))) (PreH16 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = pd)) (PreH29 : (cnt_pre = requested)) (PreH30 : (0 <= requested)) (PreH31 : (requested <= 65535)) (PreH32 : (pevent_pre <> 0)) (PreH33 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH34 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH35 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "cnt" ) )) # UShort  |-> requested)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((TskState (entry)))))
  **  (sem_set_group_frame sg entry eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((pd) # UChar  |-> 73)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  “ ((encode_event_wait_grp ((waitList (current))) ((TskState (entry)))) <> 0) ”
).

Definition OSSemSet_partial_solve_wit_12_pure_split_goal_1 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current_2: OSEventAbstractState) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current))) ((TskState (entry))))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (0 <= requested)) (PreH6 : (requested <= 65535)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH8 : ((encode_event_cnt_value (current)) <= 0)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH10 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (0 <= requested)) (PreH13 : (requested <= 65535)) (PreH14 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH15 : (0 <= (encode_event_cnt_value (current_2)))) (PreH16 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (pevent_pre <> 0)) (PreH27 : (pevent_pre = pe)) (PreH28 : (perr_pre = pd)) (PreH29 : (cnt_pre = requested)) (PreH30 : (0 <= requested)) (PreH31 : (requested <= 65535)) (PreH32 : (pevent_pre <> 0)) (PreH33 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH34 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH35 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "cnt" ) )) # UShort  |-> requested)
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((TskState (entry)))))
  **  (sem_set_group_frame sg entry eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((pd) # UChar  |-> 73)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  “ ((encode_event_wait_grp ((waitList (current))) ((TskState (entry)))) <> 0) ”
.

Definition OSSemSet_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current_2: OSEventAbstractState) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current))) ((TskState (entry))))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (0 <= requested)) (PreH4 : (requested <= 65535)) (PreH5 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH6 : ((encode_event_cnt_value (current)) <= 0)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH8 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (0 <= requested)) (PreH11 : (requested <= 65535)) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH13 : (0 <= (encode_event_cnt_value (current_2)))) (PreH14 : ((encode_event_cnt_value (current_2)) <= 65535)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (perr_pre = pd)) (PreH27 : (cnt_pre = requested)) (PreH28 : (0 <= requested)) (PreH29 : (requested <= 65535)) (PreH30 : (pevent_pre <> 0)) (PreH31 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH32 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH33 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((TskState (entry)))))
  **  (sem_set_group_frame sg entry eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((pd) # UChar  |-> 73)
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off )) ” 
  &&  “ ((encode_event_wait_grp ((waitList (current))) ((TskState (entry)))) <> 0) ” 
  &&  “ ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current))) ((TskState (entry))))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off )) ” 
  &&  “ ((encode_event_cnt_value (current_2)) <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ (0 <= (encode_event_cnt_value (current_2))) ” 
  &&  “ ((encode_event_cnt_value (current_2)) <= 65535) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((TskState (entry)))))
  **  (sem_set_group_frame sg entry eid current )
  **  ((pd) # UChar  |-> 73)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
.

Definition OSSemSet_partial_solve_wit_12 := OSSemSet_partial_solve_wit_12_pure -> OSSemSet_partial_solve_wit_12_aux.

Definition OSSemSet_partial_solve_wit_13 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (0 <= requested)) (PreH3 : (requested <= 65535)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH5 : ((encode_event_cnt_value (current)) > 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (0 <= requested)) (PreH8 : (requested <= 65535)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH10 : (0 <= (encode_event_cnt_value (current)))) (PreH11 : ((encode_event_cnt_value (current)) <= 65535)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH14 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH15 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (perr_pre = pd)) (PreH24 : (cnt_pre = requested)) (PreH25 : (0 <= requested)) (PreH26 : (requested <= 65535)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH29 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current_2)) )
  **  (sem_set_source_api_restore_pre platform critical sg invocation origin mask retval entry (sem_set_checkpoint (entry) (eid) (current_2) (requested)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry) (current_2)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((encode_event_cnt_value (current)) > 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ (0 <= (encode_event_cnt_value (current))) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 65535) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (sem_set_source_api_restore_pre platform critical sg invocation origin mask retval entry (sem_set_checkpoint (entry) (eid) (current_2) (requested)) )
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current_2)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry) (current_2)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
.

Definition OSSemSet_partial_solve_wit_14 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (current_3: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (0 <= requested)) (PreH3 : (requested <= 65535)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH5 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current_2))) ((TskState (entry))))) (32)) = 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (0 <= requested)) (PreH8 : (requested <= 65535)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH10 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH11 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH12 : ((encode_event_cnt_value (current)) <= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (0 <= requested)) (PreH15 : (requested <= 65535)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH17 : (0 <= (encode_event_cnt_value (current)))) (PreH18 : ((encode_event_cnt_value (current)) <= 65535)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH22 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH23 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pe = (event_addr (sg) (eid)))) (PreH27 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH28 : (pevent_pre <> 0)) (PreH29 : (pevent_pre = pe)) (PreH30 : (perr_pre = pd)) (PreH31 : (cnt_pre = requested)) (PreH32 : (0 <= requested)) (PreH33 : (requested <= 65535)) (PreH34 : (pevent_pre <> 0)) (PreH35 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH36 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH37 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry_2) (observed) (current_3)) )
  **  (sem_set_source_api_restore_pre platform critical sg invocation origin mask retval entry_2 (sem_set_checkpoint (entry_2) (eid) (current_3) (requested)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry_2) (current_3)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current_2))) ((TskState (entry))))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((encode_event_cnt_value (current_2)) <= 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off )) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ (0 <= (encode_event_cnt_value (current))) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 65535) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (sem_set_source_api_restore_pre platform critical sg invocation origin mask retval entry_2 (sem_set_checkpoint (entry_2) (eid) (current_3) (requested)) )
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry_2) (observed) (current_3)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry_2) (current_3)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
.

Definition OSSemSet_partial_solve_wit_15 := 
forall (perr_pre: Z) (cnt_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (current_3: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (0 <= requested)) (PreH3 : (requested <= 65535)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH5 : ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current_2))) ((TskState (entry))))) (32)) <> 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (0 <= requested)) (PreH8 : (requested <= 65535)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH10 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH11 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) (PreH12 : ((encode_event_cnt_value (current)) <= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (0 <= requested)) (PreH15 : (requested <= 65535)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH17 : (0 <= (encode_event_cnt_value (current)))) (PreH18 : ((encode_event_cnt_value (current)) <= 65535)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH22 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH23 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pe = (event_addr (sg) (eid)))) (PreH27 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH28 : (pevent_pre <> 0)) (PreH29 : (pevent_pre = pe)) (PreH30 : (perr_pre = pd)) (PreH31 : (cnt_pre = requested)) (PreH32 : (0 <= requested)) (PreH33 : (requested <= 65535)) (PreH34 : (pevent_pre <> 0)) (PreH35 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH36 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH37 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry_2) (observed) (current_3)) )
  **  (sem_set_source_api_restore_pre platform critical sg invocation origin mask retval entry_2 (sem_set_checkpoint (entry_2) (eid) (current_3) (requested)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry_2) (current_3)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((unsigned_last_nbits ((encode_event_wait_grp ((waitList (current_2))) ((TskState (entry))))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((encode_event_cnt_value (current_2)) <= 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off )) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ (0 <= (encode_event_cnt_value (current))) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 65535) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (cnt_pre = requested) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 3) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (sem_set_source_api_restore_pre platform critical sg invocation origin mask retval entry_2 (sem_set_checkpoint (entry_2) (eid) (current_3) (requested)) )
  **  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry_2) (observed) (current_3)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry_2) (current_3)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_set_source_api_safe (critical) (sg) (invocation) (pe) (requested) (before) (X)) )
.

Definition OSSemSet_which_implies_wit_1 := 
(
forall (pd: Z) ,
  (sem_set_error_cell pd )
|--
  ((pd) # UChar  |->_)
) \/
(
forall (pd: Z) ,
  (sem_set_error_cell pd )
|--
  EX (x: Z) ,
  ((pd) # UChar  |-> x)
).

Definition OSSemSet_which_implies_wit_2 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
).

Definition OSSemSet_which_implies_wit_2_split_goal_1 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSSemSet_which_implies_wit_2_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
.

Definition OSSemSet_which_implies_wit_3 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (UCOS2_inv sg before )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (UCOS2_inv sg before )
).

Definition OSSemSet_which_implies_wit_3_split_goal_1 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  “ ((encode_event_type ((eventType (observed)))) = 3) ”
.

Definition OSSemSet_which_implies_wit_3_split_goal_2 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSSemSet_which_implies_wit_3_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : ((event_slot_type_value ((EventState (before))) (eid)) = 3)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (sem_set_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (UCOS2_inv sg before )
.

Definition OSSemSet_which_implies_wit_4 := 
(
forall (requested: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (0 <= requested)) (PreH3 : (requested <= 65535)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ (0 <= (encode_event_cnt_value (current))) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 65535) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (sem_set_count_frame sg entry eid current )
) \/
(
forall (requested: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (0 <= requested)) (PreH3 : (requested <= 65535)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ (0 <= (encode_event_cnt_value (current))) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 65535) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (sem_set_count_frame sg entry eid current )
).

Definition OSSemSet_which_implies_wit_5 := 
(
forall (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (0 <= requested)) (PreH3 : (requested <= 65535)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH5 : ((encode_event_cnt_value (current_2)) > 0)) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> requested)
  **  (sem_set_count_frame sg entry_2 eid current_2 )
  **  ((pd) # UChar  |-> 0)
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (sem_set_source_api_restore_pre platform critical sg invocation origin mask cpu_sr entry (sem_set_checkpoint (entry) (eid) (current) (requested)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry) (current)))
) \/
(
forall (requested: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (0 <= requested)) (PreH3 : (requested <= 65535)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH5 : ((encode_event_cnt_value (current_2)) > 0)) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> requested)
  **  (sem_set_count_frame sg entry_2 eid current_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (0 = (sem_set_error (entry) (current))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (sem_set_source_api_restore_pre platform critical sg invocation origin mask cpu_sr entry (sem_set_checkpoint (entry) (eid) (current) (requested)) )
).

Definition OSSemSet_which_implies_wit_6 := 
(
forall (requested: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (0 <= requested)) (PreH3 : (requested <= 65535)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH5 : ((encode_event_cnt_value (current_2)) <= 0)) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current_2)))
  **  (sem_set_count_frame sg entry_2 eid current_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off )) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((TskState (entry)))))
  **  (sem_set_group_frame sg entry eid current )
) \/
(
forall (requested: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (0 <= requested)) (PreH3 : (requested <= 65535)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH5 : ((encode_event_cnt_value (current_2)) <= 0)) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (sem_set_group_read_layout (critical) (sg) (invocation) (before) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (sem_set_count_frame sg entry_2 eid current_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ ((encode_event_cnt_value (current_2)) = (encode_event_cnt_value (current))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off )) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((TskState (entry)))))
  **  (sem_set_group_frame sg entry eid current )
).

Definition OSSemSet_which_implies_wit_7 := 
(
forall (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (0 <= requested)) (PreH3 : (requested <= 65535)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH5 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH6 : ((encode_event_wait_grp ((waitList (current_2))) ((TskState (entry_2)))) = 0)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> requested)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current_2))) ((TskState (entry_2)))))
  **  (sem_set_group_frame sg entry_2 eid current_2 )
  **  ((pd) # UChar  |-> 0)
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (sem_set_source_api_restore_pre platform critical sg invocation origin mask cpu_sr entry (sem_set_checkpoint (entry) (eid) (current) (requested)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry) (current)))
) \/
(
forall (requested: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (0 <= requested)) (PreH3 : (requested <= 65535)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH5 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH6 : ((encode_event_wait_grp ((waitList (current_2))) ((TskState (entry_2)))) = 0)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> requested)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current_2))) ((TskState (entry_2)))))
  **  (sem_set_group_frame sg entry_2 eid current_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (0 = (sem_set_error (entry) (current))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (sem_set_source_api_restore_pre platform critical sg invocation origin mask cpu_sr entry (sem_set_checkpoint (entry) (eid) (current) (requested)) )
).

Definition OSSemSet_which_implies_wit_8 := 
(
forall (requested: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (0 <= requested)) (PreH3 : (requested <= 65535)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH5 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH6 : ((encode_event_wait_grp ((waitList (current_2))) ((TskState (entry_2)))) <> 0)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current_2)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current_2))) ((TskState (entry_2)))))
  **  (sem_set_group_frame sg entry_2 eid current_2 )
  **  ((pd) # UChar  |-> 73)
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (sem_set_source_api_restore_pre platform critical sg invocation origin mask cpu_sr entry (sem_set_checkpoint (entry) (eid) (current) (requested)) )
  **  ((pd) # UChar  |-> (sem_set_error (entry) (current)))
) \/
(
forall (requested: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (0 <= requested)) (PreH3 : (requested <= 65535)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off ))) (PreH5 : ((encode_event_cnt_value (current_2)) <= 0)) (PreH6 : ((encode_event_wait_grp ((waitList (current_2))) ((TskState (entry_2)))) <> 0)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventGrp") = ((event_addr (sg) (eid)) + OSEventGrp_off ))) ,
  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current_2)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current_2))) ((TskState (entry_2)))))
  **  (sem_set_group_frame sg entry_2 eid current_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (73 = (sem_set_error (entry) (current))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= requested) ” 
  &&  “ (requested <= 65535) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventCnt") = ((event_addr (sg) (eid)) + OSEventCnt_off )) ”
  &&  (coq_prop (sem_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (sem_set_source_api_restore_pre platform critical sg invocation origin mask cpu_sr entry (sem_set_checkpoint (entry) (eid) (current) (requested)) )
).

Module Type VC_Correct.


Axiom proof_of_OSSemSet_safety_wit_1 : OSSemSet_safety_wit_1.
Axiom proof_of_OSSemSet_safety_wit_2 : OSSemSet_safety_wit_2.
Axiom proof_of_OSSemSet_safety_wit_3 : OSSemSet_safety_wit_3.
Axiom proof_of_OSSemSet_safety_wit_4 : OSSemSet_safety_wit_4.
Axiom proof_of_OSSemSet_safety_wit_5 : OSSemSet_safety_wit_5.
Axiom proof_of_OSSemSet_safety_wit_6 : OSSemSet_safety_wit_6.
Axiom proof_of_OSSemSet_safety_wit_7 : OSSemSet_safety_wit_7.
Axiom proof_of_OSSemSet_safety_wit_8 : OSSemSet_safety_wit_8.
Axiom proof_of_OSSemSet_safety_wit_9 : OSSemSet_safety_wit_9.
Axiom proof_of_OSSemSet_safety_wit_10 : OSSemSet_safety_wit_10.
Axiom proof_of_OSSemSet_safety_wit_11 : OSSemSet_safety_wit_11.
Axiom proof_of_OSSemSet_safety_wit_12 : OSSemSet_safety_wit_12.
Axiom proof_of_OSSemSet_entail_wit_1_1 : OSSemSet_entail_wit_1_1.
Axiom proof_of_OSSemSet_entail_wit_1_2 : OSSemSet_entail_wit_1_2.
Axiom proof_of_OSSemSet_return_wit_1 : OSSemSet_return_wit_1.
Axiom proof_of_OSSemSet_return_wit_2 : OSSemSet_return_wit_2.
Axiom proof_of_OSSemSet_return_wit_3 : OSSemSet_return_wit_3.
Axiom proof_of_OSSemSet_return_wit_4 : OSSemSet_return_wit_4.
Axiom proof_of_OSSemSet_return_wit_5 : OSSemSet_return_wit_5.
Axiom proof_of_OSSemSet_partial_solve_wit_1 : OSSemSet_partial_solve_wit_1.
Axiom proof_of_OSSemSet_partial_solve_wit_2 : OSSemSet_partial_solve_wit_2.
Axiom proof_of_OSSemSet_partial_solve_wit_3 : OSSemSet_partial_solve_wit_3.
Axiom proof_of_OSSemSet_partial_solve_wit_4_pure : OSSemSet_partial_solve_wit_4_pure.
Axiom proof_of_OSSemSet_partial_solve_wit_4 : OSSemSet_partial_solve_wit_4.
Axiom proof_of_OSSemSet_partial_solve_wit_5_pure : OSSemSet_partial_solve_wit_5_pure.
Axiom proof_of_OSSemSet_partial_solve_wit_5 : OSSemSet_partial_solve_wit_5.
Axiom proof_of_OSSemSet_partial_solve_wit_6_pure : OSSemSet_partial_solve_wit_6_pure.
Axiom proof_of_OSSemSet_partial_solve_wit_6 : OSSemSet_partial_solve_wit_6.
Axiom proof_of_OSSemSet_partial_solve_wit_7_pure : OSSemSet_partial_solve_wit_7_pure.
Axiom proof_of_OSSemSet_partial_solve_wit_7 : OSSemSet_partial_solve_wit_7.
Axiom proof_of_OSSemSet_partial_solve_wit_8_pure : OSSemSet_partial_solve_wit_8_pure.
Axiom proof_of_OSSemSet_partial_solve_wit_8 : OSSemSet_partial_solve_wit_8.
Axiom proof_of_OSSemSet_partial_solve_wit_9_pure : OSSemSet_partial_solve_wit_9_pure.
Axiom proof_of_OSSemSet_partial_solve_wit_9 : OSSemSet_partial_solve_wit_9.
Axiom proof_of_OSSemSet_partial_solve_wit_10_pure : OSSemSet_partial_solve_wit_10_pure.
Axiom proof_of_OSSemSet_partial_solve_wit_10 : OSSemSet_partial_solve_wit_10.
Axiom proof_of_OSSemSet_partial_solve_wit_11_pure : OSSemSet_partial_solve_wit_11_pure.
Axiom proof_of_OSSemSet_partial_solve_wit_11 : OSSemSet_partial_solve_wit_11.
Axiom proof_of_OSSemSet_partial_solve_wit_12_pure : OSSemSet_partial_solve_wit_12_pure.
Axiom proof_of_OSSemSet_partial_solve_wit_12 : OSSemSet_partial_solve_wit_12.
Axiom proof_of_OSSemSet_partial_solve_wit_13 : OSSemSet_partial_solve_wit_13.
Axiom proof_of_OSSemSet_partial_solve_wit_14 : OSSemSet_partial_solve_wit_14.
Axiom proof_of_OSSemSet_partial_solve_wit_15 : OSSemSet_partial_solve_wit_15.
Axiom proof_of_OSSemSet_which_implies_wit_1 : OSSemSet_which_implies_wit_1.
Axiom proof_of_OSSemSet_which_implies_wit_2 : OSSemSet_which_implies_wit_2.
Axiom proof_of_OSSemSet_which_implies_wit_3 : OSSemSet_which_implies_wit_3.
Axiom proof_of_OSSemSet_which_implies_wit_4 : OSSemSet_which_implies_wit_4.
Axiom proof_of_OSSemSet_which_implies_wit_5 : OSSemSet_which_implies_wit_5.
Axiom proof_of_OSSemSet_which_implies_wit_6 : OSSemSet_which_implies_wit_6.
Axiom proof_of_OSSemSet_which_implies_wit_7 : OSSemSet_which_implies_wit_7.
Axiom proof_of_OSSemSet_which_implies_wit_8 : OSSemSet_which_implies_wit_8.

End VC_Correct.
