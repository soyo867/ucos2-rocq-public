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
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_query_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSMboxQuery -----*)

Definition OSMboxQuery_safety_wit_1 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_mbox_data_pre = pd)) (PreH3 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH4 : (pevent_pre <> 0)) (PreH5 : (p_mbox_data_pre <> 0)) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxQuery_safety_wit_2 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_mbox_data_pre = pd)) (PreH3 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH4 : (pevent_pre <> 0)) (PreH5 : (p_mbox_data_pre <> 0)) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxQuery_safety_wit_3 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_mbox_data_pre = pd)) (PreH3 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH4 : (pevent_pre <> 0)) (PreH5 : (p_mbox_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxQuery_safety_wit_4 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (p_mbox_data_pre = pd)) (PreH3 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH4 : (pevent_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxQuery_safety_wit_5 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_mbox_data_pre = pd)) (PreH4 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_mbox_data_pre <> 0)) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  “ False ”
.

Definition OSMboxQuery_safety_wit_6 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_mbox_data_pre = pd)) (PreH4 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_mbox_data_pre <> 0)) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  “ False ”
.

Definition OSMboxQuery_safety_wit_7 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_mbox_data_pre = pd)) (PreH4 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_mbox_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  “ False ”
.

Definition OSMboxQuery_safety_wit_8 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_mbox_data_pre = pd)) (PreH4 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  “ False ”
.

Definition OSMboxQuery_safety_wit_9 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_mbox_data_pre = pd)) (PreH4 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_mbox_data_pre <> 0)) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxQuery_safety_wit_10 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_mbox_data_pre = pd)) (PreH4 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_mbox_data_pre <> 0)) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH8 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxQuery_safety_wit_11 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_mbox_data_pre = pd)) (PreH4 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre <> 0)) (PreH6 : (p_mbox_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxQuery_safety_wit_12 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mbox_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_mbox_data_pre = pd)) (PreH5 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_mbox_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  “ False ”
.

Definition OSMboxQuery_safety_wit_13 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mbox_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_mbox_data_pre = pd)) (PreH5 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_mbox_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  “ False ”
.

Definition OSMboxQuery_safety_wit_14 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mbox_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_mbox_data_pre = pd)) (PreH5 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_mbox_data_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  “ False ”
.

Definition OSMboxQuery_safety_wit_15 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_mbox_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_mbox_data_pre = pd)) (PreH12 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_mbox_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (caller_frame )
|--
  “ False ”
.

Definition OSMboxQuery_safety_wit_16 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_mbox_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_mbox_data_pre = pd)) (PreH12 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_mbox_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  “ False ”
.

Definition OSMboxQuery_safety_wit_17 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH10 : (p_mbox_data_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (p_mbox_data_pre = pd)) (PreH14 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_mbox_data_pre <> 0)) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH18 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mbox_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxQuery_safety_wit_18 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Zlength (rows)) = 8)) (PreH3 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH4 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH5 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH6 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH16 : (p_mbox_data_pre <> 0)) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (p_mbox_data_pre = pd)) (PreH20 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (p_mbox_data_pre <> 0)) (PreH23 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH24 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (caller_frame )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxQuery_safety_wit_19 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Zlength (rows)) = 8)) (PreH3 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH4 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH5 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH6 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH16 : (p_mbox_data_pre <> 0)) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (p_mbox_data_pre = pd)) (PreH20 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (p_mbox_data_pre <> 0)) (PreH23 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH24 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |-> (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))))
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (caller_frame )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxQuery_safety_wit_20 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows)) = 8)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH6 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH8 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH10 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH11 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : ((Zlength (rows)) = 8)) (PreH14 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH15 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH16 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH17 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH18 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH21 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH22 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pe = (event_addr (sg) (eid)))) (PreH26 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH27 : (p_mbox_data_pre <> 0)) (PreH28 : (pevent_pre <> 0)) (PreH29 : (pevent_pre = pe)) (PreH30 : (p_mbox_data_pre = pd)) (PreH31 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH32 : (pevent_pre <> 0)) (PreH33 : (p_mbox_data_pre <> 0)) (PreH34 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH35 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition OSMboxQuery_safety_wit_21 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (snapshot: MboxQuerySnapshot) (PreH1 : (i >= 8)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows)) = 8)) (PreH4 : (i >= 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH10 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH12 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH13 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH15 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : ((Zlength (rows)) = 8)) (PreH18 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH19 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH20 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH21 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH22 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH25 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH26 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (0 >= 0)) (PreH29 : (pe = (event_addr (sg) (eid)))) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH31 : (p_mbox_data_pre <> 0)) (PreH32 : (pevent_pre <> 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (p_mbox_data_pre = pd)) (PreH35 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH36 : (pevent_pre <> 0)) (PreH37 : (p_mbox_data_pre <> 0)) (PreH38 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH39 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (mbox_query_restore_post platform critical sg invocation origin cpu_sr entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (mbox_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mbox_query_critical (eid) (entry) (snapshot) (entry)) )
  **  (mbox_query_output_fields_rep pd snapshot )
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxQuery_entail_wit_1_1 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH3 : (p_mbox_data_pre <> 0)) (PreH4 : (pevent_pre <> 0)) (PreH5 : (pevent_pre = pe)) (PreH6 : (p_mbox_data_pre = pd)) (PreH7 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH8 : (pevent_pre <> 0)) (PreH9 : (p_mbox_data_pre <> 0)) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH11 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mbox_data_pre = pd) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
.

Definition OSMboxQuery_entail_wit_1_2 := 
(
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH3 : (p_mbox_data_pre <> 0)) (PreH4 : (pevent_pre <> 0)) (PreH5 : (pevent_pre = pe)) (PreH6 : (p_mbox_data_pre = pd)) (PreH7 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH8 : (pevent_pre <> 0)) (PreH9 : (p_mbox_data_pre <> 0)) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH11 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (caller_frame )
|--
  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mbox_data_pre = pd) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <> 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (caller_frame )
) \/
(
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH5 : (p_mbox_data_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_mbox_data_pre = pd)) (PreH9 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (p_mbox_data_pre <> 0)) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH13 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ”
  &&  emp
).

Definition OSMboxQuery_entail_wit_1_2_split_goal_1 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH5 : (p_mbox_data_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_mbox_data_pre = pd)) (PreH9 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (p_mbox_data_pre <> 0)) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH13 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((event_slot_type_value ((EventState (before))) (eid)) <= 255)
.

Definition OSMboxQuery_entail_wit_1_2_split_goal_2 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH5 : (p_mbox_data_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (pevent_pre = pe)) (PreH8 : (p_mbox_data_pre = pd)) (PreH9 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (p_mbox_data_pre <> 0)) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH13 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (0 <= (event_slot_type_value ((EventState (before))) (eid)))
.

Definition OSMboxQuery_entail_wit_2 := 
(
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Zlength (rows)) = 8)) (PreH3 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH4 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH5 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH6 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH16 : (p_mbox_data_pre <> 0)) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (p_mbox_data_pre = pd)) (PreH20 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (p_mbox_data_pre <> 0)) (PreH23 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH24 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows 0 )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (caller_frame )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR))) = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 1) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mbox_data_pre = pd) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows 0 )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
) \/
(
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Zlength (rows)) = 8)) (PreH3 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH4 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH5 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH6 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH16 : (p_mbox_data_pre <> 0)) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (p_mbox_data_pre = pd)) (PreH20 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (p_mbox_data_pre <> 0)) (PreH23 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH24 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows 0 )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current message pointer grp rows )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (caller_frame )
|--
  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current message pointer grp rows )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows 0 )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
).

Definition OSMboxQuery_entail_wit_2_split_goal_spatial := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Zlength (rows)) = 8)) (PreH3 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH4 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH5 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH6 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH16 : (p_mbox_data_pre <> 0)) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (p_mbox_data_pre = pd)) (PreH20 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (p_mbox_data_pre <> 0)) (PreH23 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH24 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows 0 )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current message pointer grp rows )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (caller_frame )
|--
  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current message pointer grp rows )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows 0 )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMboxQuery_entail_wit_3 := 
(
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : ((Zlength (rows)) = 8)) (PreH2 : ((Zlength (rows)) = 8)) (PreH3 : (i < 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows)) = 8)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH9 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH11 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH18 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH19 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH20 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH21 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH24 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH25 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (0 >= 0)) (PreH28 : (pe = (event_addr (sg) (eid)))) (PreH29 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH30 : (p_mbox_data_pre <> 0)) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (p_mbox_data_pre = pd)) (PreH34 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH35 : (pevent_pre <> 0)) (PreH36 : (p_mbox_data_pre <> 0)) (PreH37 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH38 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows (i + 1 ) )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR))) = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR)))) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 1) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mbox_data_pre = pd) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows (i + 1 ) )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
) \/
(
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : ((Zlength (rows)) = 8)) (PreH2 : ((Zlength (rows)) = 8)) (PreH3 : (i < 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows)) = 8)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH9 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH11 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH18 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH19 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH20 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH21 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH24 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH25 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (0 >= 0)) (PreH28 : (pe = (event_addr (sg) (eid)))) (PreH29 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH30 : (p_mbox_data_pre <> 0)) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (p_mbox_data_pre = pd)) (PreH34 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH35 : (pevent_pre <> 0)) (PreH36 : (p_mbox_data_pre <> 0)) (PreH37 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH38 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows (i + 1 ) )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows (i + 1 ) )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
).

Definition OSMboxQuery_entail_wit_3_split_goal_spatial := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : ((Zlength (rows)) = 8)) (PreH2 : ((Zlength (rows)) = 8)) (PreH3 : (i < 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= 8)) (PreH6 : ((Zlength (rows)) = 8)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH9 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH11 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH13 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH18 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH19 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH20 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH21 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH24 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH25 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH26 : (0 <= UINT_MAX)) (PreH27 : (0 >= 0)) (PreH28 : (pe = (event_addr (sg) (eid)))) (PreH29 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH30 : (p_mbox_data_pre <> 0)) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (p_mbox_data_pre = pd)) (PreH34 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH35 : (pevent_pre <> 0)) (PreH36 : (p_mbox_data_pre <> 0)) (PreH37 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH38 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows (i + 1 ) )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows (i + 1 ) )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMboxQuery_return_wit_1 := 
(
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (snapshot: MboxQuerySnapshot) (PreH1 : (i >= 8)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows)) = 8)) (PreH4 : (i >= 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH10 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH12 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH13 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH15 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : ((Zlength (rows)) = 8)) (PreH18 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH19 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH20 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH21 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH22 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH25 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH26 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (0 >= 0)) (PreH29 : (pe = (event_addr (sg) (eid)))) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH31 : (p_mbox_data_pre <> 0)) (PreH32 : (pevent_pre <> 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (p_mbox_data_pre = pd)) (PreH35 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH36 : (pevent_pre <> 0)) (PreH37 : (p_mbox_data_pre <> 0)) (PreH38 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH39 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (mbox_query_restore_post platform critical sg invocation origin cpu_sr entry )
  **  (coq_prop (mbox_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mbox_query_critical (eid) (entry) (snapshot) (entry)) )
  **  (mbox_query_output_fields_rep pd snapshot )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (mbox_query_api_post platform critical sg invocation origin mask before eid pe pd 0 X )
  **  (caller_frame )
) \/
(
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (snapshot: MboxQuerySnapshot) (PreH1 : (i >= 8)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows)) = 8)) (PreH4 : (i >= 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH10 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH12 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH13 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH15 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : ((Zlength (rows)) = 8)) (PreH18 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH19 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH20 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH21 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH22 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH25 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH26 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (0 >= 0)) (PreH29 : (pe = (event_addr (sg) (eid)))) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH31 : (p_mbox_data_pre <> 0)) (PreH32 : (pevent_pre <> 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (p_mbox_data_pre = pd)) (PreH35 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH36 : (pevent_pre <> 0)) (PreH37 : (p_mbox_data_pre <> 0)) (PreH38 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH39 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (mbox_query_restore_post platform critical sg invocation origin cpu_sr entry )
  **  (coq_prop (mbox_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mbox_query_critical (eid) (entry) (snapshot) (entry)) )
  **  (mbox_query_output_fields_rep pd snapshot )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (mbox_query_api_post platform critical sg invocation origin mask before eid pe pd 0 X )
  **  (caller_frame )
).

Definition OSMboxQuery_return_wit_1_split_goal_spatial := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (snapshot: MboxQuerySnapshot) (PreH1 : (i >= 8)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows)) = 8)) (PreH4 : (i >= 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH10 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH12 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH13 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH15 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : ((Zlength (rows)) = 8)) (PreH18 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH19 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH20 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH21 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH22 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH25 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH26 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (0 >= 0)) (PreH29 : (pe = (event_addr (sg) (eid)))) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH31 : (p_mbox_data_pre <> 0)) (PreH32 : (pevent_pre <> 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (p_mbox_data_pre = pd)) (PreH35 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH36 : (pevent_pre <> 0)) (PreH37 : (p_mbox_data_pre <> 0)) (PreH38 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH39 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (mbox_query_restore_post platform critical sg invocation origin cpu_sr entry )
  **  (coq_prop (mbox_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mbox_query_critical (eid) (entry) (snapshot) (entry)) )
  **  (mbox_query_output_fields_rep pd snapshot )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (mbox_query_api_post platform critical sg invocation origin mask before eid pe pd 0 X )
  **  (caller_frame )
.

Definition OSMboxQuery_return_wit_2 := 
(
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_mbox_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_mbox_data_pre = pd)) (PreH12 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_mbox_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
  **  (caller_frame )
|--
  (mbox_query_api_post platform critical sg invocation origin mask before eid pe pd 1 X )
  **  (caller_frame )
) \/
(
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_mbox_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_mbox_data_pre = pd)) (PreH12 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_mbox_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
  **  (caller_frame )
|--
  (mbox_query_api_post platform critical sg invocation origin mask before eid pe pd 1 X )
  **  (caller_frame )
).

Definition OSMboxQuery_return_wit_2_split_goal_spatial := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_mbox_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_mbox_data_pre = pd)) (PreH12 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_mbox_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
  **  (caller_frame )
|--
  (mbox_query_api_post platform critical sg invocation origin mask before eid pe pd 1 X )
  **  (caller_frame )
.

Definition OSMboxQuery_return_wit_3 := 
(
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mbox_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_mbox_data_pre = pd)) (PreH5 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_mbox_data_pre = 0)) ,
  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  (mbox_query_api_post platform critical sg invocation origin mask before eid pe pd 9 X )
  **  (caller_frame )
) \/
(
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mbox_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_mbox_data_pre = pd)) (PreH5 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_mbox_data_pre = 0)) ,
  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  (mbox_query_api_post platform critical sg invocation origin mask before eid pe pd 9 X )
  **  (caller_frame )
).

Definition OSMboxQuery_return_wit_3_split_goal_spatial := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mbox_data_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_mbox_data_pre = pd)) (PreH5 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_mbox_data_pre = 0)) ,
  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  (mbox_query_api_post platform critical sg invocation origin mask before eid pe pd 9 X )
  **  (caller_frame )
.

Definition OSMboxQuery_return_wit_4 := 
(
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_mbox_data_pre = pd)) (PreH4 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre = 0)) ,
  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  (mbox_query_api_post platform critical sg invocation origin mask before eid pe pd 4 X )
  **  (caller_frame )
) \/
(
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_mbox_data_pre = pd)) (PreH4 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre = 0)) ,
  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  (mbox_query_api_post platform critical sg invocation origin mask before eid pe pd 4 X )
  **  (caller_frame )
).

Definition OSMboxQuery_return_wit_4_split_goal_spatial := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (p_mbox_data_pre = pd)) (PreH4 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH5 : (pevent_pre = 0)) ,
  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  (mbox_query_api_post platform critical sg invocation origin mask before eid pe pd 4 X )
  **  (caller_frame )
.

Definition OSMboxQuery_partial_solve_wit_1_pure := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mbox_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_mbox_data_pre = pd)) (PreH5 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_mbox_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
.

Definition OSMboxQuery_partial_solve_wit_1_aux := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mbox_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_mbox_data_pre = pd)) (PreH5 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_mbox_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mbox_data_pre = pd) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <> 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
.

Definition OSMboxQuery_partial_solve_wit_1 := OSMboxQuery_partial_solve_wit_1_pure -> OSMboxQuery_partial_solve_wit_1_aux.

Definition OSMboxQuery_partial_solve_wit_2_pure := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mbox_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_mbox_data_pre = pd)) (PreH5 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_mbox_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
.

Definition OSMboxQuery_partial_solve_wit_2_aux := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (p_mbox_data_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (p_mbox_data_pre = pd)) (PreH5 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH6 : (pevent_pre <> 0)) (PreH7 : (p_mbox_data_pre <> 0)) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> p_mbox_data_pre)
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mbox_data_pre = pd) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
.

Definition OSMboxQuery_partial_solve_wit_2 := OSMboxQuery_partial_solve_wit_2_pure -> OSMboxQuery_partial_solve_wit_2_aux.

Definition OSMboxQuery_partial_solve_wit_3_pure := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_mbox_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_mbox_data_pre = pd)) (PreH12 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_mbox_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
.

Definition OSMboxQuery_partial_solve_wit_3_aux := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH8 : (p_mbox_data_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (p_mbox_data_pre = pd)) (PreH12 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (p_mbox_data_pre <> 0)) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH16 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe <> 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mbox_data_pre = pd) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
.

Definition OSMboxQuery_partial_solve_wit_3 := OSMboxQuery_partial_solve_wit_3_pure -> OSMboxQuery_partial_solve_wit_3_aux.

Definition OSMboxQuery_partial_solve_wit_4_pure := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH10 : (p_mbox_data_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (p_mbox_data_pre = pd)) (PreH14 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_mbox_data_pre <> 0)) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH18 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (critical_region_outside critical sg invocation before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  “ ((encode_event_type ((eventType (observed)))) = 1) ”
.

Definition OSMboxQuery_partial_solve_wit_4_aux := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH10 : (p_mbox_data_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (p_mbox_data_pre = pd)) (PreH14 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_mbox_data_pre <> 0)) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH18 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (critical_region_outside critical sg invocation before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  “ ((encode_event_type ((eventType (observed)))) = 1) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 1) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mbox_data_pre = pd) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (critical_region_outside critical sg invocation before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
.

Definition OSMboxQuery_partial_solve_wit_4 := OSMboxQuery_partial_solve_wit_4_pure -> OSMboxQuery_partial_solve_wit_4_aux.

Definition OSMboxQuery_partial_solve_wit_5_pure := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH10 : (p_mbox_data_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (p_mbox_data_pre = pd)) (PreH14 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_mbox_data_pre <> 0)) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH18 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mbox_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pdest" ) )) # Ptr  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMboxQuery_partial_solve_wit_5_aux := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH10 : (p_mbox_data_pre <> 0)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (p_mbox_data_pre = pd)) (PreH14 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH15 : (pevent_pre <> 0)) (PreH16 : (p_mbox_data_pre <> 0)) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH18 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mbox_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (caller_frame )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 1) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mbox_data_pre = pd) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (mbox_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (caller_frame )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
.

Definition OSMboxQuery_partial_solve_wit_5 := OSMboxQuery_partial_solve_wit_5_pure -> OSMboxQuery_partial_solve_wit_5_aux.

Definition OSMboxQuery_partial_solve_wit_6 := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Zlength (rows)) = 8)) (PreH3 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH4 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH5 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH6 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH16 : (p_mbox_data_pre <> 0)) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (p_mbox_data_pre = pd)) (PreH20 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (p_mbox_data_pre <> 0)) (PreH23 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH24 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (caller_frame )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 1) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mbox_data_pre = pd) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (caller_frame )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
.

Definition OSMboxQuery_partial_solve_wit_7_pure := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : ((Zlength (rows)) = 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH7 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH8 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH9 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH11 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH12 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((Zlength (rows)) = 8)) (PreH15 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH16 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH17 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH18 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH19 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH22 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH23 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pe = (event_addr (sg) (eid)))) (PreH27 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH28 : (p_mbox_data_pre <> 0)) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (p_mbox_data_pre = pd)) (PreH32 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH33 : (pevent_pre <> 0)) (PreH34 : (p_mbox_data_pre <> 0)) (PreH35 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH36 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
.

Definition OSMboxQuery_partial_solve_wit_7_aux := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : ((Zlength (rows)) = 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH7 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH8 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH9 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH11 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH12 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((Zlength (rows)) = 8)) (PreH15 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH16 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH17 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH18 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH19 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH22 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH23 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pe = (event_addr (sg) (eid)))) (PreH27 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH28 : (p_mbox_data_pre <> 0)) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (p_mbox_data_pre = pd)) (PreH32 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH33 : (pevent_pre <> 0)) (PreH34 : (p_mbox_data_pre <> 0)) (PreH35 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH36 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 1) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mbox_data_pre = pd) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  ((( &( "psrc" ) )) # Ptr  |-> (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))
  **  ((( &( "pdest" ) )) # Ptr  |-> (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMboxQuery_partial_solve_wit_7 := OSMboxQuery_partial_solve_wit_7_pure -> OSMboxQuery_partial_solve_wit_7_aux.

Definition OSMboxQuery_partial_solve_wit_8_pure := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : ((Zlength (rows)) = 8)) (PreH2 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH4 : (i < 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH10 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH12 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH13 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH15 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : ((Zlength (rows)) = 8)) (PreH18 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH19 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH20 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH21 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH22 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH25 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH26 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (0 >= 0)) (PreH29 : (pe = (event_addr (sg) (eid)))) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH31 : (p_mbox_data_pre <> 0)) (PreH32 : (pevent_pre <> 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (p_mbox_data_pre = pd)) (PreH35 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH36 : (pevent_pre <> 0)) (PreH37 : (p_mbox_data_pre <> 0)) (PreH38 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH39 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "psrc" ) )) # Ptr  |-> (&((pe)  # "os_event" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR))))
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pdest" ) )) # Ptr  |-> (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + ((i + 1 ) * sizeof(UCHAR))))
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  (((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (store_osprio_array_missing_i &((pe)  # "os_event" ->ₛ "OSEventTbl") rows i )
  **  (((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (mbox_query_output_table_missing_i &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ ((Zlength (rows)) = 8) ”
.

Definition OSMboxQuery_partial_solve_wit_8_aux := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : ((Zlength (rows)) = 8)) (PreH2 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH3 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH4 : (i < 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH10 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH12 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH13 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH15 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : ((Zlength (rows)) = 8)) (PreH18 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH19 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH20 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH21 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH22 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH25 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH26 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (0 >= 0)) (PreH29 : (pe = (event_addr (sg) (eid)))) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH31 : (p_mbox_data_pre <> 0)) (PreH32 : (pevent_pre <> 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (p_mbox_data_pre = pd)) (PreH35 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH36 : (pevent_pre <> 0)) (PreH37 : (p_mbox_data_pre <> 0)) (PreH38 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH39 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (store_osprio_array_missing_i &((pe)  # "os_event" ->ₛ "OSEventTbl") rows i )
  **  (((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (mbox_query_output_table_missing_i &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (caller_frame )
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
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 1) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mbox_data_pre = pd) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (store_osprio_array_missing_i &((pe)  # "os_event" ->ₛ "OSEventTbl") rows i )
  **  (((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (mbox_query_output_table_missing_i &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMboxQuery_partial_solve_wit_8 := OSMboxQuery_partial_solve_wit_8_pure -> OSMboxQuery_partial_solve_wit_8_aux.

Definition OSMboxQuery_partial_solve_wit_9_pure := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : ((Zlength (rows)) = 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH7 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH8 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH9 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH11 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH12 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((Zlength (rows)) = 8)) (PreH15 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH16 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH17 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH18 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH19 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH22 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH23 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pe = (event_addr (sg) (eid)))) (PreH27 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH28 : (p_mbox_data_pre <> 0)) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (p_mbox_data_pre = pd)) (PreH32 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH33 : (pevent_pre <> 0)) (PreH34 : (p_mbox_data_pre <> 0)) (PreH35 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH36 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (i >= 8) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows)) = 8) ”
.

Definition OSMboxQuery_partial_solve_wit_9_aux := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) (PreH4 : ((Zlength (rows)) = 8)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH7 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH8 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH9 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH11 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH12 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : ((Zlength (rows)) = 8)) (PreH15 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH16 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH17 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH18 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH19 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH22 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH23 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pe = (event_addr (sg) (eid)))) (PreH27 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH28 : (p_mbox_data_pre <> 0)) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (p_mbox_data_pre = pd)) (PreH32 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH33 : (pevent_pre <> 0)) (PreH34 : (p_mbox_data_pre <> 0)) (PreH35 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH36 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
  **  (caller_frame )
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
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 1) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mbox_data_pre = pd) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (mbox_query_output_table &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |->_)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMboxQuery_partial_solve_wit_9 := OSMboxQuery_partial_solve_wit_9_pure -> OSMboxQuery_partial_solve_wit_9_aux.

Definition OSMboxQuery_partial_solve_wit_10_pure := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows)) = 8)) (PreH4 : (i >= 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH10 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH12 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH13 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH15 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : ((Zlength (rows)) = 8)) (PreH18 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH19 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH20 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH21 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH22 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH25 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH26 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (0 >= 0)) (PreH29 : (pe = (event_addr (sg) (eid)))) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH31 : (p_mbox_data_pre <> 0)) (PreH32 : (pevent_pre <> 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (p_mbox_data_pre = pd)) (PreH35 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH36 : (pevent_pre <> 0)) (PreH37 : (p_mbox_data_pre <> 0)) (PreH38 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH39 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  (store_osprio_array &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |-> pointer)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMboxQuery_partial_solve_wit_10_aux := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows)) = 8)) (PreH4 : (i >= 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH10 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH12 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH13 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH15 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : ((Zlength (rows)) = 8)) (PreH18 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH19 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH20 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH21 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH22 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH25 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH26 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (0 >= 0)) (PreH29 : (pe = (event_addr (sg) (eid)))) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH31 : (p_mbox_data_pre <> 0)) (PreH32 : (pevent_pre <> 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (p_mbox_data_pre = pd)) (PreH35 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH36 : (pevent_pre <> 0)) (PreH37 : (p_mbox_data_pre <> 0)) (PreH38 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH39 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (store_osprio_array &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |-> pointer)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (i >= 8) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 1) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mbox_data_pre = pd) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |-> pointer)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMboxQuery_partial_solve_wit_10 := OSMboxQuery_partial_solve_wit_10_pure -> OSMboxQuery_partial_solve_wit_10_aux.

Definition OSMboxQuery_partial_solve_wit_11_pure := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (snapshot: MboxQuerySnapshot) (PreH1 : (i >= 8)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows)) = 8)) (PreH4 : (i >= 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH10 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH12 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH13 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH15 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : ((Zlength (rows)) = 8)) (PreH18 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH19 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH20 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH21 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH22 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH25 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH26 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (0 >= 0)) (PreH29 : (pe = (event_addr (sg) (eid)))) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH31 : (p_mbox_data_pre <> 0)) (PreH32 : (pevent_pre <> 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (p_mbox_data_pre = pd)) (PreH35 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH36 : (pevent_pre <> 0)) (PreH37 : (p_mbox_data_pre <> 0)) (PreH38 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH39 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mbox_data" ) )) # Ptr  |-> pd)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (mbox_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mbox_query_critical (eid) (entry) (snapshot) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (mbox_query_output_fields_rep pd snapshot )
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSMboxQuery_partial_solve_wit_11_aux := 
forall (p_mbox_data_pre: Z) (pevent_pre: Z) (X: (Z -> ((@option MboxQuerySnapshot) -> (UCOS2_Verify_State -> Prop)))) (caller_frame: Assertion) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (rows: (@list Z)) (cpu_sr: Z) (pdest: Z) (psrc: Z) (i: Z) (snapshot: MboxQuerySnapshot) (PreH1 : (i >= 8)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows)) = 8)) (PreH4 : (i >= 8)) (PreH5 : (0 <= i)) (PreH6 : (i <= 8)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH10 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH12 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH13 : (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH14 : (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH15 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : ((Zlength (rows)) = 8)) (PreH18 : (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl"))) (PreH19 : ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH20 : (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl"))) (PreH21 : ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX)) (PreH22 : ((encode_event_type ((eventType (observed)))) = 1)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH25 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH26 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH27 : (0 <= UINT_MAX)) (PreH28 : (0 >= 0)) (PreH29 : (pe = (event_addr (sg) (eid)))) (PreH30 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) (PreH31 : (p_mbox_data_pre <> 0)) (PreH32 : (pevent_pre <> 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (p_mbox_data_pre = pd)) (PreH35 : (mbox_query_safe critical sg invocation eid pe pd before X )) (PreH36 : (pevent_pre <> 0)) (PreH37 : (p_mbox_data_pre <> 0)) (PreH38 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH39 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mbox_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mbox_query_critical (eid) (entry) (snapshot) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (mbox_query_output_fields_rep pd snapshot )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (i >= 8) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (psrc = (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 1) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (p_mbox_data_pre = pd) ” 
  &&  “ (mbox_query_safe critical sg invocation eid pe pd before X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (p_mbox_data_pre <> 0) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (mbox_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mbox_query_critical (eid) (entry) (snapshot) (entry)) )
  **  (mbox_query_output_fields_rep pd snapshot )
  **  (caller_frame )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMboxQuery_partial_solve_wit_11 := OSMboxQuery_partial_solve_wit_11_pure -> OSMboxQuery_partial_solve_wit_11_aux.

Definition OSMboxQuery_which_implies_wit_1 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off )) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
).

Definition OSMboxQuery_which_implies_wit_1_split_goal_1 := 
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMboxQuery_which_implies_wit_1_split_goal_spatial := 
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
.

Definition OSMboxQuery_which_implies_wit_2 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
|--
  “ ((encode_event_type ((eventType (observed)))) = 1) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (critical_region_outside critical sg invocation before )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 1) ”
  &&  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (critical_region_outside critical sg invocation before )
).

Definition OSMboxQuery_which_implies_wit_2_split_goal_1 := 
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMboxQuery_which_implies_wit_2_split_goal_2 := 
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
|--
  “ ((encode_event_type ((eventType (observed)))) = 1) ”
.

Definition OSMboxQuery_which_implies_wit_2_split_goal_spatial := 
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : (pd <> 0)) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH4 : (&((pe)  # "os_event" ->ₛ "OSEventType") = ((event_addr (sg) (eid)) + OSEventType_off ))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mbox_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mbox_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_query_type_frame sg before eid )
|--
  (coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (critical_region_outside critical sg invocation before )
.

Definition OSMboxQuery_which_implies_wit_3 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (mbox_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (message: MboxFields)  (pointer: Z)  (grp: Z)  (rows: (@list Z)) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ”
  &&  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (UCharArray.undef_full &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (mbox_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState)  (message: MboxFields)  (pointer: Z)  (grp: Z)  (rows: (@list Z)) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= &((pe)  # "os_event" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl")) ” 
  &&  “ ((&((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") + (8 * sizeof(UCHAR))) <= UINT_MAX) ”
  &&  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
).

Definition OSMboxQuery_which_implies_wit_4 := 
(
forall (rows: (@list Z)) (p_mbox_data: Z) ,
  (UCharArray.undef_full &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  (mbox_query_output_table &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows 0 )
) \/
(
forall (rows: (@list Z)) (p_mbox_data: Z) ,
  (UCharArray.undef_full &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  (mbox_query_output_table &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows 0 )
).

Definition OSMboxQuery_which_implies_wit_4_split_goal_spatial := 
forall (rows: (@list Z)) (p_mbox_data: Z) ,
  (UCharArray.undef_full &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") 8 )
|--
  (mbox_query_output_table &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows 0 )
.

Definition OSMboxQuery_which_implies_wit_5 := 
(
forall (rows: (@list Z)) (i: Z) (psrc: Z) (pevent: Z) (pdest: Z) (p_mbox_data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) (PreH3 : ((Zlength (rows)) = 8)) (PreH4 : (psrc = (&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH5 : (pdest = (&((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) ,
  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (mbox_query_output_table &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
|--
  “ ((Zlength (rows)) = 8) ” 
  &&  “ (psrc = (&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
  &&  ((psrc) # UChar  |-> (Znth (i) (rows) (0)))
  **  (store_osprio_array_missing_i &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows i )
  **  ((pdest) # UChar  |->_)
  **  (mbox_query_output_table_missing_i &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
) \/
(
forall (rows: (@list Z)) (i: Z) (psrc: Z) (pevent: Z) (pdest: Z) (p_mbox_data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) (PreH3 : ((Zlength (rows)) = 8)) (PreH4 : (psrc = (&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) (PreH5 : (pdest = (&((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))) ,
  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (mbox_query_output_table &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
|--
  EX (x: Z) ,
  “ ((Zlength (rows)) = 8) ” 
  &&  “ (psrc = (&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ” 
  &&  “ (pdest = (&((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) ”
  &&  ((pdest) # UChar  |-> x)
  **  ((psrc) # UChar  |-> (Znth (i) (rows) (0)))
  **  (store_osprio_array_missing_i &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows i )
  **  (mbox_query_output_table_missing_i &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
).

Definition OSMboxQuery_which_implies_wit_6 := 
(
forall (rows: (@list Z)) (i: Z) (pevent: Z) (p_mbox_data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) (PreH3 : ((Zlength (rows)) = 8)) ,
  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (store_osprio_array_missing_i &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows i )
  **  (((&((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (mbox_query_output_table_missing_i &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
|--
  “ ((Zlength (rows)) = 8) ”
  &&  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (mbox_query_output_table &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows (i + 1 ) )
) \/
(
forall (rows: (@list Z)) (i: Z) (pevent: Z) (p_mbox_data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) (PreH3 : ((Zlength (rows)) = 8)) ,
  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (store_osprio_array_missing_i &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows i )
  **  (((&((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (mbox_query_output_table_missing_i &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
|--
  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (mbox_query_output_table &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows (i + 1 ) )
).

Definition OSMboxQuery_which_implies_wit_6_split_goal_spatial := 
forall (rows: (@list Z)) (i: Z) (pevent: Z) (p_mbox_data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) (PreH3 : ((Zlength (rows)) = 8)) ,
  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (store_osprio_array_missing_i &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows i )
  **  (((&((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (rows) (0)))
  **  (mbox_query_output_table_missing_i &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
|--
  (store_osprio_array &((pevent)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  (mbox_query_output_table &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows (i + 1 ) )
.

Definition OSMboxQuery_which_implies_wit_7 := 
(
forall (rows: (@list Z)) (i: Z) (p_mbox_data: Z) (PreH1 : (i >= 8)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows)) = 8)) ,
  (mbox_query_output_table &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
|--
  “ (i >= 8) ” 
  &&  “ (i <= 8) ” 
  &&  “ ((Zlength (rows)) = 8) ”
  &&  (store_osprio_array &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows )
) \/
(
forall (rows: (@list Z)) (i: Z) (p_mbox_data: Z) (PreH1 : (i >= 8)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows)) = 8)) ,
  (mbox_query_output_table &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
|--
  (store_osprio_array &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows )
).

Definition OSMboxQuery_which_implies_wit_7_split_goal_spatial := 
forall (rows: (@list Z)) (i: Z) (p_mbox_data: Z) (PreH1 : (i >= 8)) (PreH2 : (i <= 8)) (PreH3 : ((Zlength (rows)) = 8)) ,
  (mbox_query_output_table &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows i )
|--
  (store_osprio_array &((p_mbox_data)  # "os_mbox_data" ->ₛ "OSEventTbl") rows )
.

Definition OSMboxQuery_which_implies_wit_8 := 
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |-> pointer)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows )
|--
  EX (snapshot: MboxQuerySnapshot) ,
  (coq_prop (mbox_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mbox_query_critical (eid) (entry) (snapshot) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (mbox_query_output_fields_rep pd snapshot )
) \/
(
forall (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (message: MboxFields) (pointer: Z) (grp: Z) (rows: (@list Z)) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (mbox_query_layout (sg) (eid) (pd)) )
  **  (mbox_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current message pointer grp rows )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pe)  # "os_event" ->ₛ "OSEventTbl") rows )
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSMsg")) # Ptr  |-> pointer)
  **  ((&((pd)  # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_mbox_data" ->ₛ "OSEventTbl") rows )
|--
  EX (snapshot: MboxQuerySnapshot) ,
  (coq_prop (mbox_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mbox_query_critical (eid) (entry) (snapshot) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (mbox_query_output_fields_rep pd snapshot )
).

Module Type VC_Correct.


Axiom proof_of_OSMboxQuery_safety_wit_1 : OSMboxQuery_safety_wit_1.
Axiom proof_of_OSMboxQuery_safety_wit_2 : OSMboxQuery_safety_wit_2.
Axiom proof_of_OSMboxQuery_safety_wit_3 : OSMboxQuery_safety_wit_3.
Axiom proof_of_OSMboxQuery_safety_wit_4 : OSMboxQuery_safety_wit_4.
Axiom proof_of_OSMboxQuery_safety_wit_5 : OSMboxQuery_safety_wit_5.
Axiom proof_of_OSMboxQuery_safety_wit_6 : OSMboxQuery_safety_wit_6.
Axiom proof_of_OSMboxQuery_safety_wit_7 : OSMboxQuery_safety_wit_7.
Axiom proof_of_OSMboxQuery_safety_wit_8 : OSMboxQuery_safety_wit_8.
Axiom proof_of_OSMboxQuery_safety_wit_9 : OSMboxQuery_safety_wit_9.
Axiom proof_of_OSMboxQuery_safety_wit_10 : OSMboxQuery_safety_wit_10.
Axiom proof_of_OSMboxQuery_safety_wit_11 : OSMboxQuery_safety_wit_11.
Axiom proof_of_OSMboxQuery_safety_wit_12 : OSMboxQuery_safety_wit_12.
Axiom proof_of_OSMboxQuery_safety_wit_13 : OSMboxQuery_safety_wit_13.
Axiom proof_of_OSMboxQuery_safety_wit_14 : OSMboxQuery_safety_wit_14.
Axiom proof_of_OSMboxQuery_safety_wit_15 : OSMboxQuery_safety_wit_15.
Axiom proof_of_OSMboxQuery_safety_wit_16 : OSMboxQuery_safety_wit_16.
Axiom proof_of_OSMboxQuery_safety_wit_17 : OSMboxQuery_safety_wit_17.
Axiom proof_of_OSMboxQuery_safety_wit_18 : OSMboxQuery_safety_wit_18.
Axiom proof_of_OSMboxQuery_safety_wit_19 : OSMboxQuery_safety_wit_19.
Axiom proof_of_OSMboxQuery_safety_wit_20 : OSMboxQuery_safety_wit_20.
Axiom proof_of_OSMboxQuery_safety_wit_21 : OSMboxQuery_safety_wit_21.
Axiom proof_of_OSMboxQuery_entail_wit_1_1 : OSMboxQuery_entail_wit_1_1.
Axiom proof_of_OSMboxQuery_entail_wit_1_2 : OSMboxQuery_entail_wit_1_2.
Axiom proof_of_OSMboxQuery_entail_wit_2 : OSMboxQuery_entail_wit_2.
Axiom proof_of_OSMboxQuery_entail_wit_3 : OSMboxQuery_entail_wit_3.
Axiom proof_of_OSMboxQuery_return_wit_1 : OSMboxQuery_return_wit_1.
Axiom proof_of_OSMboxQuery_return_wit_2 : OSMboxQuery_return_wit_2.
Axiom proof_of_OSMboxQuery_return_wit_3 : OSMboxQuery_return_wit_3.
Axiom proof_of_OSMboxQuery_return_wit_4 : OSMboxQuery_return_wit_4.
Axiom proof_of_OSMboxQuery_partial_solve_wit_1_pure : OSMboxQuery_partial_solve_wit_1_pure.
Axiom proof_of_OSMboxQuery_partial_solve_wit_1 : OSMboxQuery_partial_solve_wit_1.
Axiom proof_of_OSMboxQuery_partial_solve_wit_2_pure : OSMboxQuery_partial_solve_wit_2_pure.
Axiom proof_of_OSMboxQuery_partial_solve_wit_2 : OSMboxQuery_partial_solve_wit_2.
Axiom proof_of_OSMboxQuery_partial_solve_wit_3_pure : OSMboxQuery_partial_solve_wit_3_pure.
Axiom proof_of_OSMboxQuery_partial_solve_wit_3 : OSMboxQuery_partial_solve_wit_3.
Axiom proof_of_OSMboxQuery_partial_solve_wit_4_pure : OSMboxQuery_partial_solve_wit_4_pure.
Axiom proof_of_OSMboxQuery_partial_solve_wit_4 : OSMboxQuery_partial_solve_wit_4.
Axiom proof_of_OSMboxQuery_partial_solve_wit_5_pure : OSMboxQuery_partial_solve_wit_5_pure.
Axiom proof_of_OSMboxQuery_partial_solve_wit_5 : OSMboxQuery_partial_solve_wit_5.
Axiom proof_of_OSMboxQuery_partial_solve_wit_6 : OSMboxQuery_partial_solve_wit_6.
Axiom proof_of_OSMboxQuery_partial_solve_wit_7_pure : OSMboxQuery_partial_solve_wit_7_pure.
Axiom proof_of_OSMboxQuery_partial_solve_wit_7 : OSMboxQuery_partial_solve_wit_7.
Axiom proof_of_OSMboxQuery_partial_solve_wit_8_pure : OSMboxQuery_partial_solve_wit_8_pure.
Axiom proof_of_OSMboxQuery_partial_solve_wit_8 : OSMboxQuery_partial_solve_wit_8.
Axiom proof_of_OSMboxQuery_partial_solve_wit_9_pure : OSMboxQuery_partial_solve_wit_9_pure.
Axiom proof_of_OSMboxQuery_partial_solve_wit_9 : OSMboxQuery_partial_solve_wit_9.
Axiom proof_of_OSMboxQuery_partial_solve_wit_10_pure : OSMboxQuery_partial_solve_wit_10_pure.
Axiom proof_of_OSMboxQuery_partial_solve_wit_10 : OSMboxQuery_partial_solve_wit_10.
Axiom proof_of_OSMboxQuery_partial_solve_wit_11_pure : OSMboxQuery_partial_solve_wit_11_pure.
Axiom proof_of_OSMboxQuery_partial_solve_wit_11 : OSMboxQuery_partial_solve_wit_11.
Axiom proof_of_OSMboxQuery_which_implies_wit_1 : OSMboxQuery_which_implies_wit_1.
Axiom proof_of_OSMboxQuery_which_implies_wit_2 : OSMboxQuery_which_implies_wit_2.
Axiom proof_of_OSMboxQuery_which_implies_wit_3 : OSMboxQuery_which_implies_wit_3.
Axiom proof_of_OSMboxQuery_which_implies_wit_4 : OSMboxQuery_which_implies_wit_4.
Axiom proof_of_OSMboxQuery_which_implies_wit_5 : OSMboxQuery_which_implies_wit_5.
Axiom proof_of_OSMboxQuery_which_implies_wit_6 : OSMboxQuery_which_implies_wit_6.
Axiom proof_of_OSMboxQuery_which_implies_wit_7 : OSMboxQuery_which_implies_wit_7.
Axiom proof_of_OSMboxQuery_which_implies_wit_8 : OSMboxQuery_which_implies_wit_8.

End VC_Correct.
