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
Require Import Ucos2Verify.VC.code.queue.spec.q_query_api_spec.
Require Import Ucos2Verify.lib.array_abstraction.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSQQuery -----*)

Definition OSQQuery_safety_wit_1 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_q_data_pre = pd)) (PreH3 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH4 : (pevent_pre <> 0)) (PreH5 : (p_q_data_pre <> 0)) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQQuery_safety_wit_2 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_q_data_pre = pd)) (PreH3 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH4 : (pevent_pre <> 0)) (PreH5 : (p_q_data_pre <> 0)) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQQuery_safety_wit_3 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_q_data_pre = pd)) (PreH3 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH4 : (pevent_pre <> 0)) (PreH5 : (p_q_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQQuery_safety_wit_4 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_q_data_pre = pd)) (PreH3 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH4 : (pevent_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQQuery_safety_wit_5 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_q_data_pre = pd)) (PreH4 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_q_data_pre <> 0)) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ False ”
.

Definition OSQQuery_safety_wit_6 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_q_data_pre = pd)) (PreH4 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_q_data_pre <> 0)) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSQQuery_safety_wit_7 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_q_data_pre = pd)) (PreH4 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_q_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSQQuery_safety_wit_8 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_q_data_pre = pd)) (PreH4 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSQQuery_safety_wit_9 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_q_data_pre = pd)) (PreH4 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_q_data_pre <> 0)) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQQuery_safety_wit_10 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_q_data_pre = pd)) (PreH4 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_q_data_pre <> 0)) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQQuery_safety_wit_11 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_q_data_pre = pd)) (PreH4 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_q_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQQuery_safety_wit_12 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_q_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_q_data_pre = pd)) (PreH5 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_q_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ False ”
.

Definition OSQQuery_safety_wit_13 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_q_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_q_data_pre = pd)) (PreH5 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_q_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSQQuery_safety_wit_14 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_q_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_q_data_pre = pd)) (PreH5 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_q_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSQQuery_safety_wit_15 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_q_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_q_data_pre = pd)) (PreH12 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_q_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ False ”
.

Definition OSQQuery_safety_wit_16 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_q_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_q_data_pre = pd)) (PreH12 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_q_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ False ”
.

Definition OSQQuery_safety_wit_17 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH10 : (p_q_data_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (p_q_data_pre = pd)) (PreH14 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_q_data_pre <> 0)) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH18 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQQuery_safety_wit_18 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (rows: (@list Z)) (q: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Zlength (rows)) = 8)) (PreH3 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH12 : (p_q_data_pre <> 0)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (p_q_data_pre = pd)) (PreH16 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (p_q_data_pre <> 0)) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQQuery_safety_wit_19 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (rows: (@list Z)) (q: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Zlength (rows)) = 8)) (PreH3 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH12 : (p_q_data_pre <> 0)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (p_q_data_pre = pd)) (PreH16 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (p_q_data_pre <> 0)) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |-> (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))))
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQQuery_safety_wit_20 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (pdest: Z) (psrc: Z) (q: QueueFields) (rows_3: (@list Z)) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows_3)) = 8)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH6 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : ((Zlength (rows_2)) = 8)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((Zlength (rows)) = 8)) (PreH10 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH14 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH19 : (p_q_data_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (p_q_data_pre = pd)) (PreH23 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH24 : (pevent_pre <> 0)) (PreH25 : (p_q_data_pre <> 0)) (PreH26 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH27 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows_3 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_3 )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (q_query_output_table &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_3 i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition OSQQuery_safety_wit_21 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (q: QueueFields) (rows_4: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (rows_5: (@list Z)) (q_2: QueueFields) (PreH1 : ((queue_entries (q_2)) <= 0)) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  (coq_prop (q_query_queue_at (sg) ((qcb_addr (sg) ((qID (q))))) (q_2)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q_2 free slots grp rows_5 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_5 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_5 )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_2)))
  **  (q_query_qcb_unread sg q_2 )
  **  (queue_buffer_rep q_2 slots )
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQQuery_safety_wit_22 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (q: QueueFields) (rows_4: (@list Z)) (q_2: QueueFields) (q_3: QueueFields) (snapshot: QueueQuerySnapshot) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((queue_entries (q_2)) > 0)) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (q_query_restore_post platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_critical (sg) (eid) (entry) (snapshot) (entry)) )
  **  (q_query_output_fields_rep pd snapshot )
  **  (coq_prop (q_query_queue_valid (sg) (q_3)) )
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQQuery_safety_wit_23 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (q: QueueFields) (rows_4: (@list Z)) (q_2: QueueFields) (q_3: QueueFields) (snapshot: QueueQuerySnapshot) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((queue_entries (q_2)) <= 0)) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (q_query_restore_post platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_critical (sg) (eid) (entry) (snapshot) (entry)) )
  **  (q_query_output_fields_rep pd snapshot )
  **  (coq_prop (q_query_queue_valid (sg) (q_3)) )
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQQuery_entail_wit_1_1 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH3 : (p_q_data_pre <> 0)) (PreH4 : (pevent_pre <> 0)) (PreH5 : (pevent_pre = pe)) (PreH6 : (p_q_data_pre = pd)) (PreH7 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH8 : (pevent_pre <> 0)) (PreH9 : (p_q_data_pre <> 0)) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH11 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
.

Definition OSQQuery_entail_wit_1_2 := 
(
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH3 : (p_q_data_pre <> 0)) (PreH4 : (pevent_pre <> 0)) (PreH5 : (pevent_pre = pe)) (PreH6 : (p_q_data_pre = pd)) (PreH7 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH8 : (pevent_pre <> 0)) (PreH9 : (p_q_data_pre <> 0)) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH11 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <> 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
) \/
(
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH5 : (p_q_data_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_q_data_pre = pd)) (PreH9 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (p_q_data_pre <> 0)) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH13 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ”
  &&  emp
).

Definition OSQQuery_entail_wit_1_2_split_goal_1 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH5 : (p_q_data_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_q_data_pre = pd)) (PreH9 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (p_q_data_pre <> 0)) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH13 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((event_slot_type_value ((EventState (before))) (eid)) <= 255)
.

Definition OSQQuery_entail_wit_1_2_split_goal_2 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH5 : (p_q_data_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_q_data_pre = pd)) (PreH9 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (p_q_data_pre <> 0)) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH13 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (0 <= (event_slot_type_value ((EventState (before))) (eid)))
.

Definition OSQQuery_entail_wit_2 := 
(
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (rows: (@list Z)) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q_2: QueueFields) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (grp_2: Z) (rows_2: (@list Z)) (PreH1 : ((Zlength (rows_2)) = 8)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((Zlength (rows)) = 8)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH13 : (p_q_data_pre <> 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (p_q_data_pre = pd)) (PreH17 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (p_q_data_pre <> 0)) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH21 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (q_query_copy_frame platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (used_queue_control_block sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_2 )
  **  (q_query_output_table &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_2 0 )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (grp: Z)  (q: QueueFields)  (rows_3: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ” 
  &&  “ ((Zlength (rows_3)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))) = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (rows_2)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current q free slots grp rows_3 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_3 )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (q_query_output_table &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_3 0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
) \/
(
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (rows: (@list Z)) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q_2: QueueFields) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (grp_2: Z) (rows_2: (@list Z)) (PreH1 : ((Zlength (rows_2)) = 8)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((Zlength (rows)) = 8)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH13 : (p_q_data_pre <> 0)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (p_q_data_pre = pd)) (PreH17 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (p_q_data_pre <> 0)) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH21 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (q_query_copy_frame platform critical sg invocation origin mask retval before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  (used_queue_control_block sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_2 )
  **  (q_query_output_table &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_2 0 )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields)  (rows_3: (@list Z)) ,
  “ ((qcb_addr (sg) ((qID (q_2)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ” 
  &&  “ ((Zlength (rows_3)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows_2)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current q free slots grp_2 rows_3 )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_3 )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  (q_query_output_table &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_3 0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
).

Definition OSQQuery_entail_wit_3 := 
(
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_4: (@list Z)) (i: Z) (rows_5: (@list Z)) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q_2: QueueFields) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (grp_2: Z) (rows_6: (@list Z)) (PreH1 : ((Zlength (rows_6)) = 8)) (PreH2 : ((Zlength (rows_5)) = 8)) (PreH3 : (i < 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH9 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH10 : ((Zlength (rows_2)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((Zlength (rows)) = 8)) (PreH13 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH22 : (p_q_data_pre <> 0)) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (p_q_data_pre = pd)) (PreH26 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (p_q_data_pre <> 0)) (PreH29 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_6 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (used_queue_control_block sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_6 )
  **  (q_query_output_table &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_6 (i + 1 ) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (grp: Z)  (q: QueueFields)  (rows_3: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ ((Zlength (rows_3)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR))) = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (rows_2)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows_3 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_3 )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (q_query_output_table &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_3 (i + 1 ) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
) \/
(
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_4: (@list Z)) (i: Z) (rows_5: (@list Z)) (entry_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q_2: QueueFields) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (grp_2: Z) (rows_6: (@list Z)) (PreH1 : ((Zlength (rows_6)) = 8)) (PreH2 : ((Zlength (rows_5)) = 8)) (PreH3 : (i < 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH9 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH10 : ((Zlength (rows_2)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : ((Zlength (rows)) = 8)) (PreH13 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH22 : (p_q_data_pre <> 0)) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (p_q_data_pre = pd)) (PreH26 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (p_q_data_pre <> 0)) (PreH29 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_6 )
  **  (used_queue_control_block sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_6 )
  **  (q_query_output_table &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_6 (i + 1 ) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields)  (rows_3: (@list Z)) ,
  “ ((qcb_addr (sg) ((qID (q_2)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ ((Zlength (rows_3)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows_2)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp_2 rows_3 )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_3 )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  (q_query_output_table &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_3 (i + 1 ) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
).

Definition OSQQuery_return_wit_1 := 
(
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (rows_4: (@list Z)) (q: QueueFields) (q_2: QueueFields) (snapshot: QueueQuerySnapshot) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((queue_entries (q)) > 0)) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (q_query_restore_post platform critical sg invocation origin cpu_sr entry )
  **  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_critical (sg) (eid) (entry) (snapshot) (entry)) )
  **  (q_query_output_fields_rep pd snapshot )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (q_query_api_post platform critical sg invocation origin mask before eid pe pd 0 X )
) \/
(
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (rows_4: (@list Z)) (q: QueueFields) (q_2: QueueFields) (snapshot: QueueQuerySnapshot) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((queue_entries (q)) > 0)) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (q_query_restore_post platform critical sg invocation origin cpu_sr entry )
  **  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_critical (sg) (eid) (entry) (snapshot) (entry)) )
  **  (q_query_output_fields_rep pd snapshot )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (q_query_api_post platform critical sg invocation origin mask before eid pe pd 0 X )
).

Definition OSQQuery_return_wit_1_split_goal_spatial := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (rows_4: (@list Z)) (q: QueueFields) (q_2: QueueFields) (snapshot: QueueQuerySnapshot) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((queue_entries (q)) > 0)) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (q_query_restore_post platform critical sg invocation origin cpu_sr entry )
  **  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_critical (sg) (eid) (entry) (snapshot) (entry)) )
  **  (q_query_output_fields_rep pd snapshot )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (q_query_api_post platform critical sg invocation origin mask before eid pe pd 0 X )
.

Definition OSQQuery_return_wit_2 := 
(
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (rows_4: (@list Z)) (q: QueueFields) (q_2: QueueFields) (snapshot: QueueQuerySnapshot) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((queue_entries (q)) <= 0)) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (q_query_restore_post platform critical sg invocation origin cpu_sr entry )
  **  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_critical (sg) (eid) (entry) (snapshot) (entry)) )
  **  (q_query_output_fields_rep pd snapshot )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (q_query_api_post platform critical sg invocation origin mask before eid pe pd 0 X )
) \/
(
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (rows_4: (@list Z)) (q: QueueFields) (q_2: QueueFields) (snapshot: QueueQuerySnapshot) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((queue_entries (q)) <= 0)) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (q_query_restore_post platform critical sg invocation origin cpu_sr entry )
  **  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_critical (sg) (eid) (entry) (snapshot) (entry)) )
  **  (q_query_output_fields_rep pd snapshot )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (q_query_api_post platform critical sg invocation origin mask before eid pe pd 0 X )
).

Definition OSQQuery_return_wit_2_split_goal_spatial := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (rows_4: (@list Z)) (q: QueueFields) (q_2: QueueFields) (snapshot: QueueQuerySnapshot) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((queue_entries (q)) <= 0)) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (q_query_restore_post platform critical sg invocation origin cpu_sr entry )
  **  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_critical (sg) (eid) (entry) (snapshot) (entry)) )
  **  (q_query_output_fields_rep pd snapshot )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (q_query_api_post platform critical sg invocation origin mask before eid pe pd 0 X )
.

Definition OSQQuery_return_wit_3 := 
(
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_q_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_q_data_pre = pd)) (PreH12 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_q_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
|--
  (q_query_api_post platform critical sg invocation origin mask before eid pe pd 1 X )
) \/
(
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_q_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_q_data_pre = pd)) (PreH12 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_q_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
|--
  (q_query_api_post platform critical sg invocation origin mask before eid pe pd 1 X )
).

Definition OSQQuery_return_wit_3_split_goal_spatial := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_q_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_q_data_pre = pd)) (PreH12 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_q_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
|--
  (q_query_api_post platform critical sg invocation origin mask before eid pe pd 1 X )
.

Definition OSQQuery_return_wit_4 := 
(
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_q_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_q_data_pre = pd)) (PreH5 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_q_data_pre = 0)) ,
  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (q_query_api_post platform critical sg invocation origin mask before eid pe pd 9 X )
) \/
(
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_q_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_q_data_pre = pd)) (PreH5 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_q_data_pre = 0)) ,
  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (q_query_api_post platform critical sg invocation origin mask before eid pe pd 9 X )
).

Definition OSQQuery_return_wit_4_split_goal_spatial := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_q_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_q_data_pre = pd)) (PreH5 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_q_data_pre = 0)) ,
  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (q_query_api_post platform critical sg invocation origin mask before eid pe pd 9 X )
.

Definition OSQQuery_return_wit_5 := 
(
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_q_data_pre = pd)) (PreH4 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre = 0)) ,
  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (q_query_api_post platform critical sg invocation origin mask before eid pe pd 4 X )
) \/
(
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_q_data_pre = pd)) (PreH4 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre = 0)) ,
  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (q_query_api_post platform critical sg invocation origin mask before eid pe pd 4 X )
).

Definition OSQQuery_return_wit_5_split_goal_spatial := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_q_data_pre = pd)) (PreH4 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre = 0)) ,
  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (q_query_api_post platform critical sg invocation origin mask before eid pe pd 4 X )
.

Definition OSQQuery_partial_solve_wit_1_pure := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_q_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_q_data_pre = pd)) (PreH5 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_q_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
.

Definition OSQQuery_partial_solve_wit_1_aux := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_q_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_q_data_pre = pd)) (PreH5 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_q_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <> 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSQQuery_partial_solve_wit_1 := OSQQuery_partial_solve_wit_1_pure -> OSQQuery_partial_solve_wit_1_aux.

Definition OSQQuery_partial_solve_wit_2_pure := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_q_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_q_data_pre = pd)) (PreH5 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_q_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
.

Definition OSQQuery_partial_solve_wit_2_aux := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_q_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_q_data_pre = pd)) (PreH5 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_q_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> p_q_data_pre)
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
.

Definition OSQQuery_partial_solve_wit_2 := OSQQuery_partial_solve_wit_2_pure -> OSQQuery_partial_solve_wit_2_aux.

Definition OSQQuery_partial_solve_wit_3_pure := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_q_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_q_data_pre = pd)) (PreH12 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_q_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
.

Definition OSQQuery_partial_solve_wit_3_aux := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_q_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_q_data_pre = pd)) (PreH12 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_q_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
.

Definition OSQQuery_partial_solve_wit_3 := OSQQuery_partial_solve_wit_3_pure -> OSQQuery_partial_solve_wit_3_aux.

Definition OSQQuery_partial_solve_wit_4_pure := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH10 : (p_q_data_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (p_q_data_pre = pd)) (PreH14 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_q_data_pre <> 0)) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH18 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (critical_region_outside critical sg invocation before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ ((encode_event_type ((eventType (observed)))) = 2) ”
.

Definition OSQQuery_partial_solve_wit_4_aux := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH10 : (p_q_data_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (p_q_data_pre = pd)) (PreH14 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_q_data_pre <> 0)) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH18 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (critical_region_outside critical sg invocation before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
.

Definition OSQQuery_partial_solve_wit_4 := OSQQuery_partial_solve_wit_4_pure -> OSQQuery_partial_solve_wit_4_aux.

Definition OSQQuery_partial_solve_wit_5_pure := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH10 : (p_q_data_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (p_q_data_pre = pd)) (PreH14 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_q_data_pre <> 0)) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH18 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSQQuery_partial_solve_wit_5_aux := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH10 : (p_q_data_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (p_q_data_pre = pd)) (PreH14 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_q_data_pre <> 0)) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH18 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
.

Definition OSQQuery_partial_solve_wit_5 := OSQQuery_partial_solve_wit_5_pure -> OSQQuery_partial_solve_wit_5_aux.

Definition OSQQuery_partial_solve_wit_6_pure := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (rows: (@list Z)) (q: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Zlength (rows)) = 8)) (PreH3 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH12 : (p_q_data_pre <> 0)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (p_q_data_pre = pd)) (PreH16 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (p_q_data_pre <> 0)) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pdest" ) )) # Ptr  |-> (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))))
  **  ((( &( "psrc" ) )) # Ptr  |-> (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))))
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ ((Zlength (rows)) = 8) ”
.

Definition OSQQuery_partial_solve_wit_6_aux := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (rows: (@list Z)) (q: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Zlength (rows)) = 8)) (PreH3 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH12 : (p_q_data_pre <> 0)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (p_q_data_pre = pd)) (PreH16 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (p_q_data_pre <> 0)) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  “ ((Zlength (rows)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (q_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (UCharArray.undef_full &((pd)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
.

Definition OSQQuery_partial_solve_wit_6 := OSQQuery_partial_solve_wit_6_pure -> OSQQuery_partial_solve_wit_6_aux.

Definition OSQQuery_partial_solve_wit_7_pure := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (rows_3: (@list Z)) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (pdest: Z) (psrc: Z) (q: QueueFields) (rows: (@list Z)) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : ((Zlength (rows)) = 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : ((Zlength (rows_3)) = 8)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((Zlength (rows_2)) = 8)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH14 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH20 : (p_q_data_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_q_data_pre = pd)) (PreH24 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH25 : (pevent_pre <> 0)) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (q_query_output_table &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
.

Definition OSQQuery_partial_solve_wit_7_aux := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (rows_3: (@list Z)) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (pdest: Z) (psrc: Z) (q: QueueFields) (rows: (@list Z)) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : ((Zlength (rows)) = 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : ((Zlength (rows_3)) = 8)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((Zlength (rows_2)) = 8)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH14 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH20 : (p_q_data_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_q_data_pre = pd)) (PreH24 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH25 : (pevent_pre <> 0)) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (q_query_output_table &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (rows_3)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows_2)) = 8) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  ((( &( "psrc" ) )) # Ptr  |-> (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))
  **  ((( &( "pdest" ) )) # Ptr  |-> (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (q_query_output_table &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows i )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSQQuery_partial_solve_wit_7 := OSQQuery_partial_solve_wit_7_pure -> OSQQuery_partial_solve_wit_7_aux.

Definition OSQQuery_partial_solve_wit_8_pure := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (rows_3: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_4: (@list Z)) (i: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (rows: (@list Z)) (PreH1 : ((Zlength (rows)) = 8)) (PreH2 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : ((&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH4 : (i < 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : ((Zlength (rows_4)) = 8)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH10 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH11 : ((Zlength (rows_3)) = 8)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((Zlength (rows_2)) = 8)) (PreH14 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH17 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH23 : (p_q_data_pre <> 0)) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (p_q_data_pre = pd)) (PreH27 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_q_data_pre <> 0)) (PreH30 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH31 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "psrc" ) )) # Ptr  |-> (&((pe)  # "os_event" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR))))
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pdest" ) )) # Ptr  |-> (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR))))
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (store_osprio_array_missing_i &((pe)  # "os_event" ->ₛ "OSEventTbl") rows i )
  **  (((&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (q_query_output_table_missing_i &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows i )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ ((Zlength (rows)) = 8) ”
.

Definition OSQQuery_partial_solve_wit_8_aux := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (rows_3: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_4: (@list Z)) (i: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (rows: (@list Z)) (PreH1 : ((Zlength (rows)) = 8)) (PreH2 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : ((&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH4 : (i < 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : ((Zlength (rows_4)) = 8)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH10 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH11 : ((Zlength (rows_3)) = 8)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((Zlength (rows_2)) = 8)) (PreH14 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH17 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH23 : (p_q_data_pre <> 0)) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (p_q_data_pre = pd)) (PreH27 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_q_data_pre <> 0)) (PreH30 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH31 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (store_osprio_array_missing_i &((pe)  # "os_event" ->ₛ "OSEventTbl") rows i )
  **  (((&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (q_query_output_table_missing_i &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows i )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_4)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (rows_3)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows_2)) = 8) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (store_osprio_array_missing_i &((pe)  # "os_event" ->ₛ "OSEventTbl") rows i )
  **  (((&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (q_query_output_table_missing_i &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows i )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSQQuery_partial_solve_wit_8 := OSQQuery_partial_solve_wit_8_pure -> OSQQuery_partial_solve_wit_8_aux.

Definition OSQQuery_partial_solve_wit_9_pure := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (rows_3: (@list Z)) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (pdest: Z) (psrc: Z) (q: QueueFields) (rows: (@list Z)) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : ((Zlength (rows)) = 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : ((Zlength (rows_3)) = 8)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((Zlength (rows_2)) = 8)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH14 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH20 : (p_q_data_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_q_data_pre = pd)) (PreH24 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH25 : (pevent_pre <> 0)) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (q_query_output_table &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (i >= 8) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows)) = 8) ”
.

Definition OSQQuery_partial_solve_wit_9_aux := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (rows_3: (@list Z)) (cpu_sr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (pdest: Z) (psrc: Z) (q: QueueFields) (rows: (@list Z)) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : ((Zlength (rows)) = 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH7 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH8 : ((Zlength (rows_3)) = 8)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : ((Zlength (rows_2)) = 8)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH14 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH20 : (p_q_data_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (p_q_data_pre = pd)) (PreH24 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH25 : (pevent_pre <> 0)) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH28 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (q_query_output_table &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (i >= 8) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (rows_3)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows_2)) = 8) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (q_query_output_table &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows i )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSQQuery_partial_solve_wit_9 := OSQQuery_partial_solve_wit_9_pure -> OSQQuery_partial_solve_wit_9_aux.

Definition OSQQuery_partial_solve_wit_10_pure := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (rows_4: (@list Z)) (PreH1 : (i >= 8)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows_4)) = 8)) (PreH4 : (i >= 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : ((Zlength (rows_3)) = 8)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH10 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH11 : ((Zlength (rows_2)) = 8)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((Zlength (rows)) = 8)) (PreH14 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH17 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH23 : (p_q_data_pre <> 0)) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (p_q_data_pre = pd)) (PreH27 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_q_data_pre <> 0)) (PreH30 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH31 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows_4 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_4 )
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_4 )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
|--
  “ ((qcb_addr (sg) ((qID (q)))) = (qcb_addr (sg) ((qID (q))))) ”
.

Definition OSQQuery_partial_solve_wit_10_aux := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (rows_4: (@list Z)) (PreH1 : (i >= 8)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows_4)) = 8)) (PreH4 : (i >= 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : ((Zlength (rows_3)) = 8)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH10 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH11 : ((Zlength (rows_2)) = 8)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((Zlength (rows)) = 8)) (PreH14 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH17 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH23 : (p_q_data_pre <> 0)) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (p_q_data_pre = pd)) (PreH27 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (p_q_data_pre <> 0)) (PreH30 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH31 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows_4 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_4 )
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_4 )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ ((qcb_addr (sg) ((qID (q)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ (i >= 8) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_4)) = 8) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_3)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (rows_2)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows_4 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_4 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_4 )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSQQuery_partial_solve_wit_10 := OSQQuery_partial_solve_wit_10_pure -> OSQQuery_partial_solve_wit_10_aux.

Definition OSQQuery_partial_solve_wit_11_pure := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (q_2: QueueFields) (rows_4: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (rows_5: (@list Z)) (q: QueueFields) (PreH1 : ((queue_entries (q)) > 0)) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  (coq_prop (q_query_queue_at (sg) ((qcb_addr (sg) ((qID (q_2))))) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows_5 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_5 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_5 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  (q_query_qcb_unread sg q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ ((queue_entries (q)) > 0) ”
.

Definition OSQQuery_partial_solve_wit_11_aux := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (q_2: QueueFields) (rows_4: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (rows_5: (@list Z)) (q: QueueFields) (PreH1 : ((queue_entries (q)) > 0)) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_queue_at (sg) ((qcb_addr (sg) ((qID (q_2))))) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows_5 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_5 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_5 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  (q_query_qcb_unread sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ ((queue_entries (q)) > 0) ” 
  &&  “ ((queue_entries (q)) > 0) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (i >= 8) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_4)) = 8) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_3)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (rows_2)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (q_query_queue_at (sg) ((qcb_addr (sg) ((qID (q_2))))) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows_5 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_5 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_5 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  (q_query_qcb_unread sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSQQuery_partial_solve_wit_11 := OSQQuery_partial_solve_wit_11_pure -> OSQQuery_partial_solve_wit_11_aux.

Definition OSQQuery_partial_solve_wit_12 := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (q: QueueFields) (rows_4: (@list Z)) (q_2: QueueFields) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (grp: Z) (rows_5: (@list Z)) (slots: (@list (@option Z))) (message: Z) (q_3: QueueFields) (PreH1 : ((queue_entries (q_2)) > 0)) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_queue_at (sg) ((qcb_addr (sg) ((qID (q))))) (q_3)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q_3)) )
  **  (coq_prop (q_query_read_message (q_3) (slots) (message)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q_3 free slots grp rows_5 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_3)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_5 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_5 )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_3)))
  **  (q_query_qcb_unread sg q_3 )
  **  (((queue_out_addr (q_3))) # Ptr  |-> message)
  **  (q_query_head_slot q_3 slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> message)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ ((queue_entries (q_2)) > 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (i >= 8) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_4)) = 8) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_3)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (rows_2)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (q_query_queue_at (sg) ((qcb_addr (sg) ((qID (q))))) (q_3)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q_3)) )
  **  (coq_prop (q_query_read_message (q_3) (slots) (message)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q_3 free slots grp rows_5 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_3)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_5 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_5 )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_3)))
  **  (q_query_qcb_unread sg q_3 )
  **  (((queue_out_addr (q_3))) # Ptr  |-> message)
  **  (q_query_head_slot q_3 slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> message)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSQQuery_partial_solve_wit_13_pure := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (q_2: QueueFields) (rows_4: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (rows_5: (@list Z)) (q: QueueFields) (PreH1 : ((queue_entries (q)) <= 0)) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  (coq_prop (q_query_queue_at (sg) ((qcb_addr (sg) ((qID (q_2))))) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows_5 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_5 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_5 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  (q_query_qcb_unread sg q )
  **  (queue_buffer_rep q slots )
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> 0)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ ((queue_entries (q)) <= 0) ”
.

Definition OSQQuery_partial_solve_wit_13_aux := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (q_2: QueueFields) (rows_4: (@list Z)) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (grp: Z) (rows_5: (@list Z)) (q: QueueFields) (PreH1 : ((queue_entries (q)) <= 0)) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_queue_at (sg) ((qcb_addr (sg) ((qID (q_2))))) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows_5 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_5 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_5 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  (q_query_qcb_unread sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> 0)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ ((queue_entries (q)) <= 0) ” 
  &&  “ ((queue_entries (q)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (i >= 8) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_4)) = 8) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_3)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (rows_2)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (q_query_queue_at (sg) ((qcb_addr (sg) ((qID (q_2))))) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows_5 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_5 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_5 )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  (q_query_qcb_unread sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> 0)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |->_)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |->_)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSQQuery_partial_solve_wit_13 := OSQQuery_partial_solve_wit_13_pure -> OSQQuery_partial_solve_wit_13_aux.

Definition OSQQuery_partial_solve_wit_14_pure := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (q: QueueFields) (rows_4: (@list Z)) (q_2: QueueFields) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (grp: Z) (rows_5: (@list Z)) (slots: (@list (@option Z))) (q_3: QueueFields) (PreH1 : ((queue_entries (q_2)) <= 0)) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  (coq_prop (q_query_queue_at (sg) ((qcb_addr (sg) ((qID (q))))) (q_3)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q_3)) )
  **  (coq_prop (q_query_read_message (q_3) (slots) (0)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q_3 free slots grp rows_5 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_3)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_5 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_5 )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_3)))
  **  (q_query_qcb_unread sg q_3 )
  **  (queue_buffer_rep q_3 slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> 0)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |-> (queue_entries (q_3)))
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_3)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSQQuery_partial_solve_wit_14_aux := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (q: QueueFields) (rows_4: (@list Z)) (q_2: QueueFields) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (grp: Z) (rows_5: (@list Z)) (slots: (@list (@option Z))) (q_3: QueueFields) (PreH1 : ((queue_entries (q_2)) <= 0)) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_queue_at (sg) ((qcb_addr (sg) ((qID (q))))) (q_3)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q_3)) )
  **  (coq_prop (q_query_read_message (q_3) (slots) (0)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q_3 free slots grp rows_5 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_3)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_5 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_5 )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_3)))
  **  (q_query_qcb_unread sg q_3 )
  **  (queue_buffer_rep q_3 slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> 0)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |-> (queue_entries (q_3)))
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_3)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((queue_entries (q_2)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (i >= 8) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_4)) = 8) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_3)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (rows_2)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (q_query_queue_at (sg) ((qcb_addr (sg) ((qID (q))))) (q_3)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_read_message (q_3) (slots) (0)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q_3 free slots grp rows_5 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_3)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_5 )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_3)))
  **  (q_query_qcb_unread sg q_3 )
  **  (queue_buffer_rep q_3 slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> 0)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |-> (queue_entries (q_3)))
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_3)))
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_5 )
  **  (coq_prop (q_query_queue_valid (sg) (q_3)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSQQuery_partial_solve_wit_14 := OSQQuery_partial_solve_wit_14_pure -> OSQQuery_partial_solve_wit_14_aux.

Definition OSQQuery_partial_solve_wit_15_pure := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (q: QueueFields) (rows_4: (@list Z)) (q_2: QueueFields) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (grp: Z) (rows_5: (@list Z)) (slots: (@list (@option Z))) (message: Z) (q_3: QueueFields) (PreH1 : ((queue_entries (q_2)) > 0)) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  (coq_prop (q_query_queue_at (sg) ((qcb_addr (sg) ((qID (q))))) (q_3)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q_3)) )
  **  (coq_prop (q_query_read_message (q_3) (slots) (message)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q_3 free slots grp rows_5 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_3)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_5 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_5 )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_3)))
  **  (q_query_qcb_unread sg q_3 )
  **  (queue_buffer_rep q_3 slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> message)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |-> (queue_entries (q_3)))
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_3)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSQQuery_partial_solve_wit_15_aux := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (q: QueueFields) (rows_4: (@list Z)) (q_2: QueueFields) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (free: (@list Z)) (grp: Z) (rows_5: (@list Z)) (slots: (@list (@option Z))) (message: Z) (q_3: QueueFields) (PreH1 : ((queue_entries (q_2)) > 0)) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_queue_at (sg) ((qcb_addr (sg) ((qID (q))))) (q_3)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q_3)) )
  **  (coq_prop (q_query_read_message (q_3) (slots) (message)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q_3 free slots grp rows_5 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_3)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_5 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_5 )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_3)))
  **  (q_query_qcb_unread sg q_3 )
  **  (queue_buffer_rep q_3 slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> message)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |-> (queue_entries (q_3)))
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_3)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((queue_entries (q_2)) > 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (i >= 8) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_4)) = 8) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_3)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (rows_2)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (q_query_queue_at (sg) ((qcb_addr (sg) ((qID (q))))) (q_3)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_read_message (q_3) (slots) (message)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q_3 free slots grp rows_5 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_3)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_5 )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_3)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_3)))
  **  (q_query_qcb_unread sg q_3 )
  **  (queue_buffer_rep q_3 slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> message)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |-> (queue_entries (q_3)))
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_3)))
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_5 )
  **  (coq_prop (q_query_queue_valid (sg) (q_3)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSQQuery_partial_solve_wit_15 := OSQQuery_partial_solve_wit_15_pure -> OSQQuery_partial_solve_wit_15_aux.

Definition OSQQuery_partial_solve_wit_16_pure := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (q: QueueFields) (rows_4: (@list Z)) (q_2: QueueFields) (q_3: QueueFields) (snapshot: QueueQuerySnapshot) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((queue_entries (q_2)) > 0)) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_critical (sg) (eid) (entry) (snapshot) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (q_query_output_fields_rep pd snapshot )
  **  (coq_prop (q_query_queue_valid (sg) (q_3)) )
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSQQuery_partial_solve_wit_16_aux := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (rows_4: (@list Z)) (q_2: QueueFields) (q_3: QueueFields) (snapshot: QueueQuerySnapshot) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((queue_entries (q_2)) > 0)) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_critical (sg) (eid) (entry) (snapshot) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (q_query_output_fields_rep pd snapshot )
  **  (coq_prop (q_query_queue_valid (sg) (q_3)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ ((queue_entries (q_2)) > 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (i >= 8) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_4)) = 8) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_3)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (rows_2)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_critical (sg) (eid) (entry) (snapshot) (entry)) )
  **  (q_query_output_fields_rep pd snapshot )
  **  (coq_prop (q_query_queue_valid (sg) (q_3)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSQQuery_partial_solve_wit_16 := OSQQuery_partial_solve_wit_16_pure -> OSQQuery_partial_solve_wit_16_aux.

Definition OSQQuery_partial_solve_wit_17_pure := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (q: QueueFields) (rows_4: (@list Z)) (q_2: QueueFields) (q_3: QueueFields) (snapshot: QueueQuerySnapshot) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((queue_entries (q_2)) <= 0)) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_q_data" ) )) # Ptr  |-> pd)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_critical (sg) (eid) (entry) (snapshot) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (q_query_output_fields_rep pd snapshot )
  **  (coq_prop (q_query_queue_valid (sg) (q_3)) )
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSQQuery_partial_solve_wit_17_aux := 
forall (p_q_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option QueueQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (rows_2: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (rows_3: (@list Z)) (i: Z) (rows_4: (@list Z)) (q_2: QueueFields) (q_3: QueueFields) (snapshot: QueueQuerySnapshot) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((queue_entries (q_2)) <= 0)) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (i >= 8)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows_4)) = 8)) (PreH7 : (i >= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 8)) (PreH10 : ((Zlength (rows_3)) = 8)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : ((Zlength (rows_2)) = 8)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 2)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH26 : (p_q_data_pre <> 0)) (PreH27 : (pevent_pre <> 0)) (PreH28 : (pevent_pre = pe)) (PreH29 : (p_q_data_pre = pd)) (PreH30 : (q_query_safe critical sg invocation eid pe pd before X )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (p_q_data_pre <> 0)) (PreH33 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH34 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_critical (sg) (eid) (entry) (snapshot) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (q_query_output_fields_rep pd snapshot )
  **  (coq_prop (q_query_queue_valid (sg) (q_3)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ ((queue_entries (q_2)) <= 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) <= 65535) ” 
  &&  “ (i >= 8) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_4)) = 8) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows_3)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (rows_2)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_q_data_pre = pd) ” 
  &&  “ (q_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_q_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_critical (sg) (eid) (entry) (snapshot) (entry)) )
  **  (q_query_output_fields_rep pd snapshot )
  **  (coq_prop (q_query_queue_valid (sg) (q_3)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSQQuery_partial_solve_wit_17 := OSQQuery_partial_solve_wit_17_pure -> OSQQuery_partial_solve_wit_17_aux.

Definition OSQQuery_which_implies_wit_1 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
).

Definition OSQQuery_which_implies_wit_1_split_goal_1 := 
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSQQuery_which_implies_wit_1_split_goal_spatial := 
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
.

Definition OSQQuery_which_implies_wit_2 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
|--
  “ ((encode_event_type ((eventType (observed)))) = 2) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (critical_region_outside critical sg invocation before )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 2) ”
  &&  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (critical_region_outside critical sg invocation before )
).

Definition OSQQuery_which_implies_wit_2_split_goal_1 := 
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSQQuery_which_implies_wit_2_split_goal_2 := 
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
|--
  “ ((encode_event_type ((eventType (observed)))) = 2) ”
.

Definition OSQQuery_which_implies_wit_2_split_goal_spatial := 
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (q_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (q_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_query_type_frame sg before eid )
|--
  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (critical_region_outside critical sg invocation before )
.

Definition OSQQuery_which_implies_wit_3 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (grp: Z)  (rows: (@list Z))  (q: QueueFields) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ”
  &&  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (grp: Z)  (rows: (@list Z))  (q: QueueFields) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ”
  &&  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
).

Definition OSQQuery_which_implies_wit_4 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (grp_2: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (pevent: Z) (p_q_data: Z) (PreH1 : ((Zlength (rows_2)) = 8)) ,
  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (used_queue_control_block sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows_2 )
  **  (UCharArray.undef_full &((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z)))  (grp: Z)  (rows: (@list Z)) ,
  “ ((Zlength (rows)) = 8) ”
  &&  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (q_query_output_table &((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") rows 0 )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (grp_2: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (pevent: Z) (p_q_data: Z) (PreH1 : ((Zlength (rows_2)) = 8)) ,
  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  (used_queue_control_block sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows_2 )
  **  (UCharArray.undef_full &((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") 8 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z)))  (rows: (@list Z)) ,
  “ ((qcb_addr (sg) ((qID (q_2)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ ((Zlength (rows)) = 8) ”
  &&  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp_2 rows )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (q_query_output_table &((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") rows 0 )
).

Definition OSQQuery_which_implies_wit_5 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (grp_2: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (i: Z) (psrc: Z) (pevent: Z) (pdest: Z) (p_q_data: Z) (cpu_sr: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) (PreH3 : ((Zlength (rows_2)) = 8)) (PreH4 : (psrc = (&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH5 : (pdest = (&((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) ,
  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (used_queue_control_block sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows_2 )
  **  (q_query_output_table &((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") rows_2 i )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z)))  (grp: Z)  (rows: (@list Z)) ,
  “ ((Zlength (rows)) = 8) ” 
  &&  “ (psrc = (&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
  &&  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  ((psrc) # UChar  |-> (Znth (i) (rows) (0)))
  **  (store_osprio_array_missing_i &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows i )
  **  ((pdest) # UChar  |->_)
  **  (q_query_output_table_missing_i &((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") rows i )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (grp_2: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (i: Z) (psrc: Z) (pevent: Z) (pdest: Z) (p_q_data: Z) (cpu_sr: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) (PreH3 : ((Zlength (rows_2)) = 8)) (PreH4 : (psrc = (&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH5 : (pdest = (&((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) ,
  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  (used_queue_control_block sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows_2 )
  **  (q_query_output_table &((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") rows_2 i )
|--
  EX (x: Z)  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z)))  (rows: (@list Z)) ,
  “ ((qcb_addr (sg) ((qID (q_2)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (psrc = (&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
  &&  ((pdest) # UChar  |-> x)
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp_2 rows )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  ((psrc) # UChar  |-> (Znth (i) (rows) (0)))
  **  (store_osprio_array_missing_i &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows i )
  **  (q_query_output_table_missing_i &((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") rows i )
).

Definition OSQQuery_which_implies_wit_6 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (grp_2: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (i: Z) (cpu_sr: Z) (pevent: Z) (p_q_data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) (PreH3 : ((Zlength (rows_2)) = 8)) ,
  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (used_queue_control_block sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows_2) (0)))
  **  (store_osprio_array_missing_i &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows_2 i )
  **  (((&((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows_2) (0)))
  **  (q_query_output_table_missing_i &((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") rows_2 i )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z)))  (grp: Z)  (rows: (@list Z)) ,
  “ ((Zlength (rows)) = 8) ”
  &&  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (q_query_output_table &((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") rows (i + 1 ) )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (grp_2: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (i: Z) (cpu_sr: Z) (pevent: Z) (p_q_data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) (PreH3 : ((Zlength (rows_2)) = 8)) ,
  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  (used_queue_control_block sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows_2) (0)))
  **  (store_osprio_array_missing_i &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows_2 i )
  **  (((&((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows_2) (0)))
  **  (q_query_output_table_missing_i &((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") rows_2 i )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z)))  (rows: (@list Z)) ,
  “ ((qcb_addr (sg) ((qID (q_2)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ ((Zlength (rows)) = 8) ”
  &&  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp_2 rows )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (q_query_output_table &((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") rows (i + 1 ) )
).

Definition OSQQuery_which_implies_wit_7 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (grp_2: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (i: Z) (cpu_sr: Z) (pevent: Z) (p_q_data: Z) (PreH1 : (i >= 8)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows_2)) = 8)) ,
  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (used_queue_control_block sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows_2 )
  **  (q_query_output_table &((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") rows_2 i )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z)))  (grp: Z)  (rows: (@list Z)) ,
  “ (i >= 8) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows)) = 8) ”
  &&  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (store_osprio_array &((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") rows )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (grp_2: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (i: Z) (cpu_sr: Z) (pevent: Z) (p_q_data: Z) (PreH1 : (i >= 8)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows_2)) = 8)) ,
  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  (used_queue_control_block sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows_2 )
  **  (q_query_output_table &((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") rows_2 i )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z)))  (rows: (@list Z)) ,
  “ ((qcb_addr (sg) ((qID (q_2)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ (i >= 8) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows)) = 8) ”
  &&  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp_2 rows )
  **  (used_queue_control_block sg q )
  **  (queue_buffer_rep q slots )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (store_osprio_array &((p_q_data)  # "os_q_data" ->ₛ "OSEventTbl") rows )
).

Definition OSQQuery_which_implies_wit_8 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (grp_2: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) (PreH1 : (pq = (qcb_addr (sg) ((qID (q_2)))))) ,
  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_2 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_2 )
  **  (used_queue_control_block sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (grp: Z)  (rows: (@list Z))  (q: QueueFields) ,
  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ”
  &&  (coq_prop (q_query_queue_at (sg) (pq) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  (q_query_qcb_unread sg q )
  **  (queue_buffer_rep q slots )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (grp_2: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) (PreH1 : (pq = (qcb_addr (sg) ((qID (q_2)))))) ,
  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_2 )
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_2 )
  **  (used_queue_control_block sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (rows: (@list Z))  (q: QueueFields) ,
  “ ((qcb_addr (sg) ((qID (q_2)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ”
  &&  (coq_prop (q_query_queue_at (sg) (pq) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp_2 rows )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  (q_query_qcb_unread sg q )
  **  (queue_buffer_rep q slots )
).

Definition OSQQuery_which_implies_wit_9 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (grp_2: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q_2)) > 0)) ,
  (coq_prop (q_query_queue_at (sg) (pq) (q_2)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_2 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_2 )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_2)))
  **  (q_query_qcb_unread sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (grp: Z)  (rows: (@list Z))  (slots: (@list (@option Z)))  (message: Z)  (q: QueueFields) ,
  (coq_prop (q_query_queue_at (sg) (pq) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (coq_prop (q_query_read_message (q) (slots) (message)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  (q_query_qcb_unread sg q )
  **  (((queue_out_addr (q))) # Ptr  |-> message)
  **  (q_query_head_slot q slots )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (grp_2: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q_2)) > 0)) ,
  (coq_prop (q_query_queue_at (sg) (pq) (q_2)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_2 )
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_2 )
  **  (q_query_qcb_unread sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (rows: (@list Z))  (slots: (@list (@option Z)))  (message: Z)  (q: QueueFields) ,
  “ ((qSize (q_2)) = (qSize (q))) ” 
  &&  “ ((queue_entries (q_2)) = (queue_entries (q))) ” 
  &&  “ ((queue_out_addr (q_2)) = (queue_out_addr (q))) ” 
  &&  “ ((qcb_addr (sg) ((qID (q_2)))) = (qcb_addr (sg) ((qID (q))))) ”
  &&  (coq_prop (q_query_queue_at (sg) (pq) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (coq_prop (q_query_read_message (q) (slots) (message)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp_2 rows )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows )
  **  (q_query_qcb_unread sg q )
  **  (((queue_out_addr (q))) # Ptr  |-> message)
  **  (q_query_head_slot q slots )
).

Definition OSQQuery_which_implies_wit_10 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (message_2: Z) (rows_2: (@list Z)) (grp_2: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) ,
  (coq_prop (q_query_queue_at (sg) (pq) (q_2)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (coq_prop (q_query_read_message (q_2) (slots_2) (message_2)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_2 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_2 )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_2)))
  **  (q_query_qcb_unread sg q_2 )
  **  (((queue_out_addr (q_2))) # Ptr  |-> message_2)
  **  (q_query_head_slot q_2 slots_2 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> message_2)
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (grp: Z)  (rows: (@list Z))  (slots: (@list (@option Z)))  (message: Z)  (q: QueueFields) ,
  (coq_prop (q_query_queue_at (sg) (pq) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (coq_prop (q_query_read_message (q) (slots) (message)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  (q_query_qcb_unread sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> message)
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (message_2: Z) (rows_2: (@list Z)) (grp_2: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) ,
  (coq_prop (q_query_queue_at (sg) (pq) (q_2)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (coq_prop (q_query_read_message (q_2) (slots_2) (message_2)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_2 )
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_2 )
  **  (q_query_qcb_unread sg q_2 )
  **  (((queue_out_addr (q_2))) # Ptr  |-> message_2)
  **  (q_query_head_slot q_2 slots_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (rows: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ ((qSize (q_2)) = (qSize (q))) ” 
  &&  “ ((queue_entries (q_2)) = (queue_entries (q))) ” 
  &&  “ ((queue_out_addr (q_2)) = (queue_out_addr (q))) ” 
  &&  “ ((qcb_addr (sg) ((qID (q_2)))) = (qcb_addr (sg) ((qID (q))))) ”
  &&  (coq_prop (q_query_queue_at (sg) (pq) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (coq_prop (q_query_read_message (q) (slots) (message_2)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp_2 rows )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows )
  **  (q_query_qcb_unread sg q )
  **  (queue_buffer_rep q slots )
).

Definition OSQQuery_which_implies_wit_11 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (grp_2: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q_2)) <= 0)) ,
  (coq_prop (q_query_queue_at (sg) (pq) (q_2)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_2 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_2)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_2 )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_2)))
  **  (q_query_qcb_unread sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> 0)
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (grp: Z)  (rows: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  (coq_prop (q_query_queue_at (sg) (pq) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (coq_prop (q_query_read_message (q) (slots) (0)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  (q_query_qcb_unread sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> 0)
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows_2: (@list Z)) (grp_2: Z) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q_2)) <= 0)) ,
  (coq_prop (q_query_queue_at (sg) (pq) (q_2)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q_2)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q_2 free_2 slots_2 grp_2 rows_2 )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows_2 )
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows_2 )
  **  (q_query_qcb_unread sg q_2 )
  **  (queue_buffer_rep q_2 slots_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (rows: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ ((qSize (q_2)) = (qSize (q))) ” 
  &&  “ ((queue_entries (q_2)) = (queue_entries (q))) ” 
  &&  “ ((queue_out_addr (q_2)) = (queue_out_addr (q))) ” 
  &&  “ ((qcb_addr (sg) ((qID (q_2)))) = (qcb_addr (sg) ((qID (q))))) ”
  &&  (coq_prop (q_query_queue_at (sg) (pq) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_queue_valid (sg) (q)) )
  **  (coq_prop (q_query_read_message (q) (slots) (0)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current q free slots grp_2 rows )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows )
  **  (q_query_qcb_unread sg q )
  **  (queue_buffer_rep q slots )
).

Definition OSQQuery_which_implies_wit_12 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (message: Z) (grp: Z) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (q_query_queue_at (sg) (pq) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_read_message (q) (slots) (message)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  (q_query_qcb_unread sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> message)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |-> (queue_entries (q)))
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows )
|--
  EX (snapshot: QueueQuerySnapshot)  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_critical (sg) (eid) (entry) (snapshot) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (q_query_output_fields_rep pd snapshot )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (rows: (@list Z)) (message: Z) (grp: Z) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (pq: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (q_query_queue_at (sg) (pq) (q)) )
  **  (coq_prop (q_query_layout (sg) (eid)) )
  **  (coq_prop (q_query_read_message (q) (slots) (message)) )
  **  (q_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry_2 eid observed current_2 q free slots grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  (q_query_qcb_unread sg q )
  **  (queue_buffer_rep q slots )
  **  ((&((pd)  # "os_q_data" ->ₛ "OSMsg")) # Ptr  |-> message)
  **  ((&((pd)  # "os_q_data" ->ₛ "OSNMsgs")) # UShort  |-> (queue_entries (q)))
  **  ((&((pd)  # "os_q_data" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pd)  # "os_q_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_q_data" ->ₛ "OSEventTbl") rows )
|--
  EX (snapshot: QueueQuerySnapshot)  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  (coq_prop (q_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (q_query_critical (sg) (eid) (entry) (snapshot) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (q_query_output_fields_rep pd snapshot )
).

Module Type VC_Correct.


Axiom proof_of_OSQQuery_safety_wit_1 : OSQQuery_safety_wit_1.
Axiom proof_of_OSQQuery_safety_wit_2 : OSQQuery_safety_wit_2.
Axiom proof_of_OSQQuery_safety_wit_3 : OSQQuery_safety_wit_3.
Axiom proof_of_OSQQuery_safety_wit_4 : OSQQuery_safety_wit_4.
Axiom proof_of_OSQQuery_safety_wit_5 : OSQQuery_safety_wit_5.
Axiom proof_of_OSQQuery_safety_wit_6 : OSQQuery_safety_wit_6.
Axiom proof_of_OSQQuery_safety_wit_7 : OSQQuery_safety_wit_7.
Axiom proof_of_OSQQuery_safety_wit_8 : OSQQuery_safety_wit_8.
Axiom proof_of_OSQQuery_safety_wit_9 : OSQQuery_safety_wit_9.
Axiom proof_of_OSQQuery_safety_wit_10 : OSQQuery_safety_wit_10.
Axiom proof_of_OSQQuery_safety_wit_11 : OSQQuery_safety_wit_11.
Axiom proof_of_OSQQuery_safety_wit_12 : OSQQuery_safety_wit_12.
Axiom proof_of_OSQQuery_safety_wit_13 : OSQQuery_safety_wit_13.
Axiom proof_of_OSQQuery_safety_wit_14 : OSQQuery_safety_wit_14.
Axiom proof_of_OSQQuery_safety_wit_15 : OSQQuery_safety_wit_15.
Axiom proof_of_OSQQuery_safety_wit_16 : OSQQuery_safety_wit_16.
Axiom proof_of_OSQQuery_safety_wit_17 : OSQQuery_safety_wit_17.
Axiom proof_of_OSQQuery_safety_wit_18 : OSQQuery_safety_wit_18.
Axiom proof_of_OSQQuery_safety_wit_19 : OSQQuery_safety_wit_19.
Axiom proof_of_OSQQuery_safety_wit_20 : OSQQuery_safety_wit_20.
Axiom proof_of_OSQQuery_safety_wit_21 : OSQQuery_safety_wit_21.
Axiom proof_of_OSQQuery_safety_wit_22 : OSQQuery_safety_wit_22.
Axiom proof_of_OSQQuery_safety_wit_23 : OSQQuery_safety_wit_23.
Axiom proof_of_OSQQuery_entail_wit_1_1 : OSQQuery_entail_wit_1_1.
Axiom proof_of_OSQQuery_entail_wit_1_2 : OSQQuery_entail_wit_1_2.
Axiom proof_of_OSQQuery_entail_wit_2 : OSQQuery_entail_wit_2.
Axiom proof_of_OSQQuery_entail_wit_3 : OSQQuery_entail_wit_3.
Axiom proof_of_OSQQuery_return_wit_1 : OSQQuery_return_wit_1.
Axiom proof_of_OSQQuery_return_wit_2 : OSQQuery_return_wit_2.
Axiom proof_of_OSQQuery_return_wit_3 : OSQQuery_return_wit_3.
Axiom proof_of_OSQQuery_return_wit_4 : OSQQuery_return_wit_4.
Axiom proof_of_OSQQuery_return_wit_5 : OSQQuery_return_wit_5.
Axiom proof_of_OSQQuery_partial_solve_wit_1_pure : OSQQuery_partial_solve_wit_1_pure.
Axiom proof_of_OSQQuery_partial_solve_wit_1 : OSQQuery_partial_solve_wit_1.
Axiom proof_of_OSQQuery_partial_solve_wit_2_pure : OSQQuery_partial_solve_wit_2_pure.
Axiom proof_of_OSQQuery_partial_solve_wit_2 : OSQQuery_partial_solve_wit_2.
Axiom proof_of_OSQQuery_partial_solve_wit_3_pure : OSQQuery_partial_solve_wit_3_pure.
Axiom proof_of_OSQQuery_partial_solve_wit_3 : OSQQuery_partial_solve_wit_3.
Axiom proof_of_OSQQuery_partial_solve_wit_4_pure : OSQQuery_partial_solve_wit_4_pure.
Axiom proof_of_OSQQuery_partial_solve_wit_4 : OSQQuery_partial_solve_wit_4.
Axiom proof_of_OSQQuery_partial_solve_wit_5_pure : OSQQuery_partial_solve_wit_5_pure.
Axiom proof_of_OSQQuery_partial_solve_wit_5 : OSQQuery_partial_solve_wit_5.
Axiom proof_of_OSQQuery_partial_solve_wit_6_pure : OSQQuery_partial_solve_wit_6_pure.
Axiom proof_of_OSQQuery_partial_solve_wit_6 : OSQQuery_partial_solve_wit_6.
Axiom proof_of_OSQQuery_partial_solve_wit_7_pure : OSQQuery_partial_solve_wit_7_pure.
Axiom proof_of_OSQQuery_partial_solve_wit_7 : OSQQuery_partial_solve_wit_7.
Axiom proof_of_OSQQuery_partial_solve_wit_8_pure : OSQQuery_partial_solve_wit_8_pure.
Axiom proof_of_OSQQuery_partial_solve_wit_8 : OSQQuery_partial_solve_wit_8.
Axiom proof_of_OSQQuery_partial_solve_wit_9_pure : OSQQuery_partial_solve_wit_9_pure.
Axiom proof_of_OSQQuery_partial_solve_wit_9 : OSQQuery_partial_solve_wit_9.
Axiom proof_of_OSQQuery_partial_solve_wit_10_pure : OSQQuery_partial_solve_wit_10_pure.
Axiom proof_of_OSQQuery_partial_solve_wit_10 : OSQQuery_partial_solve_wit_10.
Axiom proof_of_OSQQuery_partial_solve_wit_11_pure : OSQQuery_partial_solve_wit_11_pure.
Axiom proof_of_OSQQuery_partial_solve_wit_11 : OSQQuery_partial_solve_wit_11.
Axiom proof_of_OSQQuery_partial_solve_wit_12 : OSQQuery_partial_solve_wit_12.
Axiom proof_of_OSQQuery_partial_solve_wit_13_pure : OSQQuery_partial_solve_wit_13_pure.
Axiom proof_of_OSQQuery_partial_solve_wit_13 : OSQQuery_partial_solve_wit_13.
Axiom proof_of_OSQQuery_partial_solve_wit_14_pure : OSQQuery_partial_solve_wit_14_pure.
Axiom proof_of_OSQQuery_partial_solve_wit_14 : OSQQuery_partial_solve_wit_14.
Axiom proof_of_OSQQuery_partial_solve_wit_15_pure : OSQQuery_partial_solve_wit_15_pure.
Axiom proof_of_OSQQuery_partial_solve_wit_15 : OSQQuery_partial_solve_wit_15.
Axiom proof_of_OSQQuery_partial_solve_wit_16_pure : OSQQuery_partial_solve_wit_16_pure.
Axiom proof_of_OSQQuery_partial_solve_wit_16 : OSQQuery_partial_solve_wit_16.
Axiom proof_of_OSQQuery_partial_solve_wit_17_pure : OSQQuery_partial_solve_wit_17_pure.
Axiom proof_of_OSQQuery_partial_solve_wit_17 : OSQQuery_partial_solve_wit_17.
Axiom proof_of_OSQQuery_which_implies_wit_1 : OSQQuery_which_implies_wit_1.
Axiom proof_of_OSQQuery_which_implies_wit_2 : OSQQuery_which_implies_wit_2.
Axiom proof_of_OSQQuery_which_implies_wit_3 : OSQQuery_which_implies_wit_3.
Axiom proof_of_OSQQuery_which_implies_wit_4 : OSQQuery_which_implies_wit_4.
Axiom proof_of_OSQQuery_which_implies_wit_5 : OSQQuery_which_implies_wit_5.
Axiom proof_of_OSQQuery_which_implies_wit_6 : OSQQuery_which_implies_wit_6.
Axiom proof_of_OSQQuery_which_implies_wit_7 : OSQQuery_which_implies_wit_7.
Axiom proof_of_OSQQuery_which_implies_wit_8 : OSQQuery_which_implies_wit_8.
Axiom proof_of_OSQQuery_which_implies_wit_9 : OSQQuery_which_implies_wit_9.
Axiom proof_of_OSQQuery_which_implies_wit_10 : OSQQuery_which_implies_wit_10.
Axiom proof_of_OSQQuery_which_implies_wit_11 : OSQQuery_which_implies_wit_11.
Axiom proof_of_OSQQuery_which_implies_wit_12 : OSQQuery_which_implies_wit_12.

End VC_Correct.
