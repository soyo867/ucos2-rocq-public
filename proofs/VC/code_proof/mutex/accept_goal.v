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
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_accept_modular_spec.
Local Open Scope sac.

(*----- Function OSMutexAccept -----*)

Definition OSMutexAccept_safety_wit_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = pe)) (PreH2 : (perr_pre = pd)) (PreH3 : (perr_pre <> 0)) (PreH4 : (isr = (intNesting ((IntrState (before)))))) (PreH5 : (isr >= 0)) (PreH6 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexAccept_safety_wit_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = pe)) (PreH2 : (perr_pre = pd)) (PreH3 : (perr_pre <> 0)) (PreH4 : (isr = (intNesting ((IntrState (before)))))) (PreH5 : (isr >= 0)) (PreH6 : (pe = 0)) (PreH7 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexAccept_safety_wit_3 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (perr_pre <> 0)) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : (isr >= 0)) (PreH7 : (pe = 0)) (PreH8 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ False ”
.

Definition OSMutexAccept_safety_wit_4 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : (isr = (intNesting ((IntrState (before)))))) (PreH2 : (isr <= 0)) (PreH3 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH4 : (isr <= 0)) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (isr = (intNesting ((IntrState (before)))))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pevent_pre <> 0)) (PreH16 : (pevent_pre = pe)) (PreH17 : (perr_pre = pd)) (PreH18 : (perr_pre <> 0)) (PreH19 : (isr = (intNesting ((IntrState (before)))))) (PreH20 : (isr >= 0)) (PreH21 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexAccept_safety_wit_5 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (isr = (intNesting ((IntrState (before)))))) (PreH3 : (isr <= 0)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (isr <= 0)) (PreH6 : (0 <= isr)) (PreH7 : (isr <= 255)) (PreH8 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (perr_pre = pd)) (PreH19 : (perr_pre <> 0)) (PreH20 : (isr = (intNesting ((IntrState (before)))))) (PreH21 : (isr >= 0)) (PreH22 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= cnt) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (isr = (intNesting ((IntrState (before)))))) (PreH3 : (isr <= 0)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (isr <= 0)) (PreH6 : (0 <= isr)) (PreH7 : (isr <= 255)) (PreH8 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (perr_pre = pd)) (PreH19 : (perr_pre <> 0)) (PreH20 : (isr = (intNesting ((IntrState (before)))))) (PreH21 : (isr >= 0)) (PreH22 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= cnt) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
).

Definition OSMutexAccept_safety_wit_5_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (isr = (intNesting ((IntrState (before)))))) (PreH3 : (isr <= 0)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (isr <= 0)) (PreH6 : (0 <= isr)) (PreH7 : (isr <= 255)) (PreH8 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (perr_pre = pd)) (PreH19 : (perr_pre <> 0)) (PreH20 : (isr = (intNesting ((IntrState (before)))))) (PreH21 : (isr >= 0)) (PreH22 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= cnt) ”
.

Definition OSMutexAccept_safety_wit_5_split_goal_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (isr = (intNesting ((IntrState (before)))))) (PreH3 : (isr <= 0)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (isr <= 0)) (PreH6 : (0 <= isr)) (PreH7 : (isr <= 255)) (PreH8 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (perr_pre = pd)) (PreH19 : (perr_pre <> 0)) (PreH20 : (isr = (intNesting ((IntrState (before)))))) (PreH21 : (isr >= 0)) (PreH22 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (8 <= 31) ”
.

Definition OSMutexAccept_safety_wit_5_split_goal_3 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (isr = (intNesting ((IntrState (before)))))) (PreH3 : (isr <= 0)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (isr <= 0)) (PreH6 : (0 <= isr)) (PreH7 : (isr <= 255)) (PreH8 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (perr_pre = pd)) (PreH19 : (perr_pre <> 0)) (PreH20 : (isr = (intNesting ((IntrState (before)))))) (PreH21 : (isr >= 0)) (PreH22 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= 8) ”
.

Definition OSMutexAccept_safety_wit_6 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((curPrio (task)) <= (Z.shiftr cnt 8))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) <> 255)) (PreH3 : ((Z.land cnt_2 255) = 255)) (PreH4 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH5 : ((Z.land cnt 255) = 255)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (isr = (intNesting ((IntrState (before)))))) (PreH8 : (isr <= 0)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH10 : (isr <= 0)) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH14 : (isr = (intNesting ((IntrState (before)))))) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (perr_pre = pd)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((IntrState (before)))))) (PreH26 : (isr >= 0)) (PreH27 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (120) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexAccept_safety_wit_7 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) = 255)) (PreH5 : ((Z.land cnt_2 255) = 255)) (PreH6 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH7 : ((Z.land cnt 255) = 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : (isr <= 0)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (perr_pre = pd)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((IntrState (before)))))) (PreH28 : (isr >= 0)) (PreH29 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexAccept_safety_wit_8 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((curPrio (task)) > (Z.shiftr cnt 8))) (PreH5 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) <> 255)) (PreH6 : ((Z.land cnt_2 255) = 255)) (PreH7 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH8 : ((Z.land cnt 255) = 255)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : (isr <= 0)) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (isr <= 0)) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH17 : (isr = (intNesting ((IntrState (before)))))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (perr_pre = pd)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((IntrState (before)))))) (PreH29 : (isr >= 0)) (PreH30 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexAccept_safety_wit_9 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land cnt 255) <> 255)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (isr = (intNesting ((IntrState (before)))))) (PreH4 : (isr <= 0)) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (isr <= 0)) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (perr_pre = pd)) (PreH20 : (perr_pre <> 0)) (PreH21 : (isr = (intNesting ((IntrState (before)))))) (PreH22 : (isr >= 0)) (PreH23 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask entry )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (0) (entry)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexAccept_entail_wit_1 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pevent_pre <> 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (perr_pre = pd)) (PreH5 : (perr_pre <> 0)) (PreH6 : (isr = (intNesting ((IntrState (before)))))) (PreH7 : (isr >= 0)) (PreH8 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pevent_pre <> 0)) (PreH5 : (pevent_pre = pe)) (PreH6 : (perr_pre = pd)) (PreH7 : (perr_pre <> 0)) (PreH8 : (isr = (intNesting ((IntrState (before)))))) (PreH9 : (isr >= 0)) (PreH10 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ”
  &&  emp
).

Definition OSMutexAccept_entail_wit_1_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pevent_pre <> 0)) (PreH5 : (pevent_pre = pe)) (PreH6 : (perr_pre = pd)) (PreH7 : (perr_pre <> 0)) (PreH8 : (isr = (intNesting ((IntrState (before)))))) (PreH9 : (isr >= 0)) (PreH10 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((event_slot_type_value ((EventState (before))) (eid)) <= 255)
.

Definition OSMutexAccept_entail_wit_1_split_goal_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pevent_pre <> 0)) (PreH5 : (pevent_pre = pe)) (PreH6 : (perr_pre = pd)) (PreH7 : (perr_pre <> 0)) (PreH8 : (isr = (intNesting ((IntrState (before)))))) (PreH9 : (isr >= 0)) (PreH10 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (0 <= (event_slot_type_value ((EventState (before))) (eid)))
.

Definition OSMutexAccept_entail_wit_2 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH2 : (isr = (intNesting ((IntrState (before)))))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (perr_pre = pd)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((IntrState (before)))))) (PreH14 : (isr >= 0)) (PreH15 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH2 : (isr = (intNesting ((IntrState (before)))))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (perr_pre = pd)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((IntrState (before)))))) (PreH14 : (isr >= 0)) (PreH15 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  TT && emp 
|--
  “ (isr <= 255) ”
  &&  emp
).

Definition OSMutexAccept_entail_wit_2_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH2 : (isr = (intNesting ((IntrState (before)))))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH4 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (perr_pre = pd)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((IntrState (before)))))) (PreH14 : (isr >= 0)) (PreH15 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (isr <= 255)
.

Definition OSMutexAccept_entail_wit_3_1 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) = 255)) (PreH2 : ((Z.land cnt_2 255) = 255)) (PreH3 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH4 : ((Z.land cnt 255) = 255)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (isr = (intNesting ((IntrState (before)))))) (PreH7 : (isr <= 0)) (PreH8 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH9 : (isr <= 0)) (PreH10 : (0 <= isr)) (PreH11 : (isr <= 255)) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (isr = (intNesting ((IntrState (before)))))) (PreH14 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH15 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (pe = (event_addr (sg) (eid)))) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (perr_pre = pd)) (PreH23 : (perr_pre <> 0)) (PreH24 : (isr = (intNesting ((IntrState (before)))))) (PreH25 : (isr >= 0)) (PreH26 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt_2) (ptr)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt 8))
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt_2 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) = 255) ” 
  &&  “ ((Z.land cnt_2 255) = 255) ” 
  &&  “ ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8)) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt 8))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt_2) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt_2 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval: Z) (cnt: Z) (task: TaskAbstractState) (cnt_2: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) = 255)) (PreH4 : ((Z.land cnt_2 255) = 255)) (PreH5 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH6 : ((Z.land cnt 255) = 255)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (isr = (intNesting ((IntrState (before)))))) (PreH9 : (isr <= 0)) (PreH10 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH11 : (isr <= 0)) (PreH12 : (0 <= isr)) (PreH13 : (isr <= 255)) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (isr = (intNesting ((IntrState (before)))))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH17 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (perr_pre = pd)) (PreH25 : (perr_pre <> 0)) (PreH26 : (isr = (intNesting ((IntrState (before)))))) (PreH27 : (isr >= 0)) (PreH28 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  TT && emp 
|--
  “ ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0) ”
  &&  emp
).

Definition OSMutexAccept_entail_wit_3_1_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval: Z) (cnt: Z) (task: TaskAbstractState) (cnt_2: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) = 255)) (PreH4 : ((Z.land cnt_2 255) = 255)) (PreH5 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH6 : ((Z.land cnt 255) = 255)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (isr = (intNesting ((IntrState (before)))))) (PreH9 : (isr <= 0)) (PreH10 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH11 : (isr <= 0)) (PreH12 : (0 <= isr)) (PreH13 : (isr <= 255)) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (isr = (intNesting ((IntrState (before)))))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH17 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (perr_pre = pd)) (PreH25 : (perr_pre <> 0)) (PreH26 : (isr = (intNesting ((IntrState (before)))))) (PreH27 : (isr >= 0)) (PreH28 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0)
.

Definition OSMutexAccept_entail_wit_3_2 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((curPrio (task)) > (Z.shiftr cnt 8))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) <> 255)) (PreH3 : ((Z.land cnt_2 255) = 255)) (PreH4 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH5 : ((Z.land cnt 255) = 255)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (isr = (intNesting ((IntrState (before)))))) (PreH8 : (isr <= 0)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH10 : (isr <= 0)) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH14 : (isr = (intNesting ((IntrState (before)))))) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (perr_pre = pd)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((IntrState (before)))))) (PreH26 : (isr >= 0)) (PreH27 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt_2) (ptr)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt 8))
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt_2 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ ((curPrio (task)) > (Z.shiftr cnt 8)) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) <> 255) ” 
  &&  “ ((Z.land cnt_2 255) = 255) ” 
  &&  “ ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8)) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt 8))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt_2) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt_2 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval: Z) (cnt: Z) (task: TaskAbstractState) (cnt_2: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((curPrio (task)) > (Z.shiftr cnt 8))) (PreH4 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) <> 255)) (PreH5 : ((Z.land cnt_2 255) = 255)) (PreH6 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH7 : ((Z.land cnt 255) = 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : (isr <= 0)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (perr_pre = pd)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((IntrState (before)))))) (PreH28 : (isr >= 0)) (PreH29 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  TT && emp 
|--
  “ ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0) ”
  &&  emp
).

Definition OSMutexAccept_entail_wit_3_2_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (retval: Z) (cnt: Z) (task: TaskAbstractState) (cnt_2: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((curPrio (task)) > (Z.shiftr cnt 8))) (PreH4 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) <> 255)) (PreH5 : ((Z.land cnt_2 255) = 255)) (PreH6 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH7 : ((Z.land cnt 255) = 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : (isr <= 0)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (perr_pre = pd)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((IntrState (before)))))) (PreH28 : (isr >= 0)) (PreH29 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0)
.

Definition OSMutexAccept_return_wit_1 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land cnt 255) <> 255)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (isr = (intNesting ((IntrState (before)))))) (PreH4 : (isr <= 0)) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (isr <= 0)) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (perr_pre = pd)) (PreH20 : (perr_pre <> 0)) (PreH21 : (isr = (intNesting ((IntrState (before)))))) (PreH22 : (isr >= 0)) (PreH23 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask entry )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (0) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |-> 0)
|--
  EX (code: Z)  (after: UCOS2_Verify_State) ,
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (after)) (return (0)) X ) ”
  &&  (coq_prop (mutex_accept_public_post (critical) (sg) (invocation) (pe) (before) (code) (0) (after)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask after )
  **  ((pd) # UChar  |-> code)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land cnt 255) <> 255)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (isr = (intNesting ((IntrState (before)))))) (PreH4 : (isr <= 0)) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (isr <= 0)) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (perr_pre = pd)) (PreH20 : (perr_pre <> 0)) (PreH21 : (isr = (intNesting ((IntrState (before)))))) (PreH22 : (isr >= 0)) (PreH23 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask entry )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (0) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (after)) (return (0)) X ) ”
  &&  (coq_prop (mutex_accept_public_post (critical) (sg) (invocation) (pe) (before) (0) (0) (after)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask after )
).

Definition OSMutexAccept_return_wit_2 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((curPrio (task)) <= (Z.shiftr cnt 8))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) <> 255)) (PreH3 : ((Z.land cnt_2 255) = 255)) (PreH4 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH5 : ((Z.land cnt 255) = 255)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (isr = (intNesting ((IntrState (before)))))) (PreH8 : (isr <= 0)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH10 : (isr <= 0)) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH14 : (isr = (intNesting ((IntrState (before)))))) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (perr_pre = pd)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((IntrState (before)))))) (PreH26 : (isr >= 0)) (PreH27 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (120) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |-> 120)
|--
  EX (code: Z)  (after: UCOS2_Verify_State) ,
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (after)) (return (1)) X ) ”
  &&  (coq_prop (mutex_accept_public_post (critical) (sg) (invocation) (pe) (before) (code) (1) (after)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask after )
  **  ((pd) # UChar  |-> code)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((curPrio (task)) <= (Z.shiftr cnt 8))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) <> 255)) (PreH3 : ((Z.land cnt_2 255) = 255)) (PreH4 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH5 : ((Z.land cnt 255) = 255)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (isr = (intNesting ((IntrState (before)))))) (PreH8 : (isr <= 0)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH10 : (isr <= 0)) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH14 : (isr = (intNesting ((IntrState (before)))))) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (perr_pre = pd)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((IntrState (before)))))) (PreH26 : (isr >= 0)) (PreH27 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (120) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (after)) (return (1)) X ) ”
  &&  (coq_prop (mutex_accept_public_post (critical) (sg) (invocation) (pe) (before) (120) (1) (after)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask after )
).

Definition OSMutexAccept_return_wit_3 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) = 255)) (PreH5 : ((Z.land cnt_2 255) = 255)) (PreH6 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH7 : ((Z.land cnt 255) = 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : (isr <= 0)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (perr_pre = pd)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((IntrState (before)))))) (PreH28 : (isr >= 0)) (PreH29 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |-> 0)
|--
  EX (code: Z)  (after: UCOS2_Verify_State) ,
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (after)) (return (1)) X ) ”
  &&  (coq_prop (mutex_accept_public_post (critical) (sg) (invocation) (pe) (before) (code) (1) (after)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask after )
  **  ((pd) # UChar  |-> code)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) = 255)) (PreH5 : ((Z.land cnt_2 255) = 255)) (PreH6 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH7 : ((Z.land cnt 255) = 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : (isr <= 0)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (perr_pre = pd)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((IntrState (before)))))) (PreH28 : (isr >= 0)) (PreH29 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (after)) (return (1)) X ) ”
  &&  (coq_prop (mutex_accept_public_post (critical) (sg) (invocation) (pe) (before) (0) (1) (after)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask after )
).

Definition OSMutexAccept_return_wit_4 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((curPrio (task)) > (Z.shiftr cnt 8))) (PreH5 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) <> 255)) (PreH6 : ((Z.land cnt_2 255) = 255)) (PreH7 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH8 : ((Z.land cnt 255) = 255)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : (isr <= 0)) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (isr <= 0)) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH17 : (isr = (intNesting ((IntrState (before)))))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (perr_pre = pd)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((IntrState (before)))))) (PreH29 : (isr >= 0)) (PreH30 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |-> 0)
|--
  EX (code: Z)  (after: UCOS2_Verify_State) ,
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (after)) (return (1)) X ) ”
  &&  (coq_prop (mutex_accept_public_post (critical) (sg) (invocation) (pe) (before) (code) (1) (after)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask after )
  **  ((pd) # UChar  |-> code)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((curPrio (task)) > (Z.shiftr cnt 8))) (PreH5 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) <> 255)) (PreH6 : ((Z.land cnt_2 255) = 255)) (PreH7 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH8 : ((Z.land cnt 255) = 255)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : (isr <= 0)) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (isr <= 0)) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH17 : (isr = (intNesting ((IntrState (before)))))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (perr_pre = pd)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((IntrState (before)))))) (PreH29 : (isr >= 0)) (PreH30 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (after)) (return (1)) X ) ”
  &&  (coq_prop (mutex_accept_public_post (critical) (sg) (invocation) (pe) (before) (0) (1) (after)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask after )
).

Definition OSMutexAccept_return_wit_5 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (isr > 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (perr_pre = pd)) (PreH15 : (perr_pre <> 0)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : (isr >= 0)) (PreH18 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |-> 2)
|--
  EX (code: Z)  (after: UCOS2_Verify_State) ,
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (after)) (return (0)) X ) ”
  &&  (coq_prop (mutex_accept_public_post (critical) (sg) (invocation) (pe) (before) (code) (0) (after)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask after )
  **  ((pd) # UChar  |-> code)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (isr > 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (perr_pre = pd)) (PreH15 : (perr_pre <> 0)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : (isr >= 0)) (PreH18 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (after)) (return (0)) X ) ”
  &&  (coq_prop (mutex_accept_public_post (critical) (sg) (invocation) (pe) (before) (2) (0) (after)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask after )
).

Definition OSMutexAccept_return_wit_6 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 4)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pevent_pre <> 0)) (PreH8 : (pevent_pre = pe)) (PreH9 : (perr_pre = pd)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((IntrState (before)))))) (PreH12 : (isr >= 0)) (PreH13 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |-> 1)
|--
  EX (code: Z)  (after: UCOS2_Verify_State) ,
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (after)) (return (0)) X ) ”
  &&  (coq_prop (mutex_accept_public_post (critical) (sg) (invocation) (pe) (before) (code) (0) (after)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask after )
  **  ((pd) # UChar  |-> code)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 4)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pevent_pre <> 0)) (PreH8 : (pevent_pre = pe)) (PreH9 : (perr_pre = pd)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((IntrState (before)))))) (PreH12 : (isr >= 0)) (PreH13 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (after)) (return (0)) X ) ”
  &&  (coq_prop (mutex_accept_public_post (critical) (sg) (invocation) (pe) (before) (1) (0) (after)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask after )
).

Definition OSMutexAccept_return_wit_7 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (perr_pre <> 0)) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : (isr >= 0)) (PreH7 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |-> 4)
|--
  EX (code: Z)  (after: UCOS2_Verify_State) ,
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (after)) (return (0)) X ) ”
  &&  (coq_prop (mutex_accept_public_post (critical) (sg) (invocation) (pe) (before) (code) (0) (after)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask after )
  **  ((pd) # UChar  |-> code)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (perr_pre <> 0)) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : (isr >= 0)) (PreH7 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
  **  (mutex_accept_call_support environment saved_local sg context before )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (after)) (return (0)) X ) ”
  &&  (coq_prop (mutex_accept_public_post (critical) (sg) (invocation) (pe) (before) (4) (0) (after)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask after )
).

Definition OSMutexAccept_return_wit_8 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (perr_pre <> 0)) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : (isr >= 0)) (PreH7 : (pe = 0)) (PreH8 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |-> 4)
|--
  EX (code: Z)  (after: UCOS2_Verify_State) ,
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (after)) (return (0)) X ) ”
  &&  (coq_prop (mutex_accept_public_post (critical) (sg) (invocation) (pe) (before) (code) (0) (after)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask after )
  **  ((pd) # UChar  |-> code)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (perr_pre <> 0)) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : (isr >= 0)) (PreH7 : (pe = 0)) (PreH8 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
  **  (mutex_accept_call_support environment saved_local sg context before )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (after)) (return (0)) X ) ”
  &&  (coq_prop (mutex_accept_public_post (critical) (sg) (invocation) (pe) (before) (4) (0) (after)) )
  **  (mutex_accept_call_return environment platform critical saved_local sg context invocation origin mask after )
).

Definition OSMutexAccept_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (perr_pre <> 0)) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : (isr >= 0)) (PreH7 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ”
.

Definition OSMutexAccept_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (perr_pre = pd)) (PreH4 : (perr_pre <> 0)) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : (isr >= 0)) (PreH7 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMutexAccept_partial_solve_wit_1 := OSMutexAccept_partial_solve_wit_1_pure -> OSMutexAccept_partial_solve_wit_1_aux.

Definition OSMutexAccept_partial_solve_wit_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 4)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pevent_pre <> 0)) (PreH8 : (pevent_pre = pe)) (PreH9 : (perr_pre = pd)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((IntrState (before)))))) (PreH12 : (isr >= 0)) (PreH13 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) <> 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMutexAccept_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pevent_pre <> 0)) (PreH8 : (pevent_pre = pe)) (PreH9 : (perr_pre = pd)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((IntrState (before)))))) (PreH12 : (isr >= 0)) (PreH13 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ”
.

Definition OSMutexAccept_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pevent_pre <> 0)) (PreH8 : (pevent_pre = pe)) (PreH9 : (perr_pre = pd)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((IntrState (before)))))) (PreH12 : (isr >= 0)) (PreH13 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMutexAccept_partial_solve_wit_3 := OSMutexAccept_partial_solve_wit_3_pure -> OSMutexAccept_partial_solve_wit_3_aux.

Definition OSMutexAccept_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (isr > 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (perr_pre = pd)) (PreH15 : (perr_pre <> 0)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : (isr >= 0)) (PreH18 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (isr = (intNesting ((IntrState (before))))) ”
.

Definition OSMutexAccept_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (isr > 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (perr_pre = pd)) (PreH15 : (perr_pre <> 0)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : (isr >= 0)) (PreH18 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr > 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMutexAccept_partial_solve_wit_4 := OSMutexAccept_partial_solve_wit_4_pure -> OSMutexAccept_partial_solve_wit_4_aux.

Definition OSMutexAccept_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (isr <= 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (perr_pre = pd)) (PreH15 : (perr_pre <> 0)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : (isr >= 0)) (PreH18 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr <= 0) ”
.

Definition OSMutexAccept_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (isr <= 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (perr_pre = pd)) (PreH15 : (perr_pre <> 0)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : (isr >= 0)) (PreH18 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMutexAccept_partial_solve_wit_5 := OSMutexAccept_partial_solve_wit_5_pure -> OSMutexAccept_partial_solve_wit_5_aux.

Definition OSMutexAccept_partial_solve_wit_6_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (isr = (intNesting ((IntrState (before)))))) (PreH2 : (isr <= 0)) (PreH3 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH4 : (isr <= 0)) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (isr = (intNesting ((IntrState (before)))))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pevent_pre <> 0)) (PreH16 : (pevent_pre = pe)) (PreH17 : (perr_pre = pd)) (PreH18 : (perr_pre <> 0)) (PreH19 : (isr = (intNesting ((IntrState (before)))))) (PreH20 : (isr >= 0)) (PreH21 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (kernel_call_task_source (context) (before)) )
  **  (coq_prop (mutex_accept_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((encode_event_type ((eventType (observed)))) = 4) ”
.

Definition OSMutexAccept_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (isr = (intNesting ((IntrState (before)))))) (PreH2 : (isr <= 0)) (PreH3 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH4 : (isr <= 0)) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (isr = (intNesting ((IntrState (before)))))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pevent_pre <> 0)) (PreH16 : (pevent_pre = pe)) (PreH17 : (perr_pre = pd)) (PreH18 : (perr_pre <> 0)) (PreH19 : (isr = (intNesting ((IntrState (before)))))) (PreH20 : (isr >= 0)) (PreH21 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (kernel_call_task_source (context) (before)) )
  **  (coq_prop (mutex_accept_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (kernel_call_task_source (context) (before)) )
  **  (coq_prop (mutex_accept_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMutexAccept_partial_solve_wit_6 := OSMutexAccept_partial_solve_wit_6_pure -> OSMutexAccept_partial_solve_wit_6_aux.

Definition OSMutexAccept_partial_solve_wit_7_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : (isr = (intNesting ((IntrState (before)))))) (PreH2 : (isr <= 0)) (PreH3 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH4 : (isr <= 0)) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (isr = (intNesting ((IntrState (before)))))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pevent_pre <> 0)) (PreH16 : (pevent_pre = pe)) (PreH17 : (perr_pre = pd)) (PreH18 : (perr_pre <> 0)) (PreH19 : (isr = (intNesting ((IntrState (before)))))) (PreH20 : (isr >= 0)) (PreH21 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMutexAccept_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : (isr = (intNesting ((IntrState (before)))))) (PreH2 : (isr <= 0)) (PreH3 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH4 : (isr <= 0)) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (isr = (intNesting ((IntrState (before)))))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pevent_pre <> 0)) (PreH16 : (pevent_pre = pe)) (PreH17 : (perr_pre = pd)) (PreH18 : (perr_pre <> 0)) (PreH19 : (isr = (intNesting ((IntrState (before)))))) (PreH20 : (isr >= 0)) (PreH21 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMutexAccept_partial_solve_wit_7 := OSMutexAccept_partial_solve_wit_7_pure -> OSMutexAccept_partial_solve_wit_7_aux.

Definition OSMutexAccept_partial_solve_wit_8_pure := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land cnt 255) = 255)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (isr = (intNesting ((IntrState (before)))))) (PreH4 : (isr <= 0)) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (isr <= 0)) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (perr_pre = pd)) (PreH20 : (perr_pre <> 0)) (PreH21 : (isr = (intNesting ((IntrState (before)))))) (PreH22 : (isr >= 0)) (PreH23 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((Z.land cnt 255) = 255) ” 
  &&  “ ((Z.shiftr cnt 8) = (Z.shiftr cnt 8)) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (Z.shiftr cnt 8)) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (Z.shiftr cnt 8)) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (Z.shiftr cnt 8)) ”
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : (isr <= 0)) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (isr <= 0)) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr = (intNesting ((IntrState (before)))))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH14 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (perr_pre = pd)) (PreH22 : (perr_pre <> 0)) (PreH23 : (isr = (intNesting ((IntrState (before)))))) (PreH24 : (isr >= 0)) (PreH25 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (Z.shiftr cnt 8)) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (Z.shiftr cnt 8)) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (Z.shiftr cnt 8)) ”
).

Definition OSMutexAccept_partial_solve_wit_8_pure_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : (isr <= 0)) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (isr <= 0)) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr = (intNesting ((IntrState (before)))))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH14 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (perr_pre = pd)) (PreH22 : (perr_pre <> 0)) (PreH23 : (isr = (intNesting ((IntrState (before)))))) (PreH24 : (isr >= 0)) (PreH25 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (Z.shiftr cnt 8)) ”
.

Definition OSMutexAccept_partial_solve_wit_8_pure_split_goal_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : (isr <= 0)) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (isr <= 0)) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr = (intNesting ((IntrState (before)))))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH14 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (perr_pre = pd)) (PreH22 : (perr_pre <> 0)) (PreH23 : (isr = (intNesting ((IntrState (before)))))) (PreH24 : (isr >= 0)) (PreH25 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (Z.shiftr cnt 8)) ”
.

Definition OSMutexAccept_partial_solve_wit_8_pure_split_goal_3 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (isr = (intNesting ((IntrState (before)))))) (PreH6 : (isr <= 0)) (PreH7 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH8 : (isr <= 0)) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr = (intNesting ((IntrState (before)))))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH14 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH16 : (0 <= UINT_MAX)) (PreH17 : (0 >= 0)) (PreH18 : (pe = (event_addr (sg) (eid)))) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (perr_pre = pd)) (PreH22 : (perr_pre <> 0)) (PreH23 : (isr = (intNesting ((IntrState (before)))))) (PreH24 : (isr >= 0)) (PreH25 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (Z.shiftr cnt 8)) ”
.

Definition OSMutexAccept_partial_solve_wit_8_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land cnt 255) = 255)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (isr = (intNesting ((IntrState (before)))))) (PreH4 : (isr <= 0)) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (isr <= 0)) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (perr_pre = pd)) (PreH20 : (perr_pre <> 0)) (PreH21 : (isr = (intNesting ((IntrState (before)))))) (PreH22 : (isr >= 0)) (PreH23 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((Z.land cnt 255) = 255) ” 
  &&  “ ((Z.shiftr cnt 8) = (Z.shiftr cnt 8)) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (Z.shiftr cnt 8)) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (Z.shiftr cnt 8)) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (8)) = (Z.shiftr cnt 8)) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt 8))
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMutexAccept_partial_solve_wit_8 := OSMutexAccept_partial_solve_wit_8_pure -> OSMutexAccept_partial_solve_wit_8_aux.

Definition OSMutexAccept_partial_solve_wit_9_pure := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt_2: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((curPrio (task)) <= (Z.shiftr cnt_2 8))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) <> 255)) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8))) (PreH5 : ((Z.land cnt_2 255) = 255)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (isr = (intNesting ((IntrState (before)))))) (PreH8 : (isr <= 0)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH10 : (isr <= 0)) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH14 : (isr = (intNesting ((IntrState (before)))))) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (perr_pre = pd)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((IntrState (before)))))) (PreH26 : (isr >= 0)) (PreH27 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ ((Z.shiftr cnt 8) = (Z.shiftr cnt 8)) ” 
  &&  “ ((curPrio (task)) <= (Z.shiftr cnt 8)) ” 
  &&  “ ((Z.shiftr cnt 8) <> 255) ” 
  &&  “ ((Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))) = (Z.lor (Z.land cnt 65280) (curPrio (task)))) ”
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt_2: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((curPrio (task)) <= (Z.shiftr cnt_2 8))) (PreH4 : ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) <> 255)) (PreH5 : ((Z.land cnt 255) = 255)) (PreH6 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8))) (PreH7 : ((Z.land cnt_2 255) = 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : (isr <= 0)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (perr_pre = pd)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((IntrState (before)))))) (PreH28 : (isr >= 0)) (PreH29 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))) = (Z.lor (Z.land cnt 65280) (curPrio (task)))) ” 
  &&  “ ((Z.shiftr cnt 8) <> 255) ”
).

Definition OSMutexAccept_partial_solve_wit_9_pure_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt_2: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((curPrio (task)) <= (Z.shiftr cnt_2 8))) (PreH4 : ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) <> 255)) (PreH5 : ((Z.land cnt 255) = 255)) (PreH6 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8))) (PreH7 : ((Z.land cnt_2 255) = 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : (isr <= 0)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (perr_pre = pd)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((IntrState (before)))))) (PreH28 : (isr >= 0)) (PreH29 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))) = (Z.lor (Z.land cnt 65280) (curPrio (task)))) ”
.

Definition OSMutexAccept_partial_solve_wit_9_pure_split_goal_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt_2: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((curPrio (task)) <= (Z.shiftr cnt_2 8))) (PreH4 : ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) <> 255)) (PreH5 : ((Z.land cnt 255) = 255)) (PreH6 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8))) (PreH7 : ((Z.land cnt_2 255) = 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : (isr <= 0)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (perr_pre = pd)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((IntrState (before)))))) (PreH28 : (isr >= 0)) (PreH29 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((Z.shiftr cnt 8) <> 255) ”
.

Definition OSMutexAccept_partial_solve_wit_9_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt_2: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((curPrio (task)) <= (Z.shiftr cnt_2 8))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) <> 255)) (PreH3 : ((Z.land cnt 255) = 255)) (PreH4 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8))) (PreH5 : ((Z.land cnt_2 255) = 255)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (isr = (intNesting ((IntrState (before)))))) (PreH8 : (isr <= 0)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH10 : (isr <= 0)) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH14 : (isr = (intNesting ((IntrState (before)))))) (PreH15 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH16 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH18 : (0 <= UINT_MAX)) (PreH19 : (0 >= 0)) (PreH20 : (pe = (event_addr (sg) (eid)))) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (perr_pre = pd)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((IntrState (before)))))) (PreH26 : (isr >= 0)) (PreH27 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ ((Z.shiftr cnt 8) = (Z.shiftr cnt 8)) ” 
  &&  “ ((curPrio (task)) <= (Z.shiftr cnt 8)) ” 
  &&  “ ((Z.shiftr cnt 8) <> 255) ” 
  &&  “ ((Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))) = (Z.lor (Z.land cnt 65280) (curPrio (task)))) ” 
  &&  “ ((curPrio (task)) <= (Z.shiftr cnt_2 8)) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) <> 255) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8)) ” 
  &&  “ ((Z.land cnt_2 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt 8))
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (curPrio (task))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMutexAccept_partial_solve_wit_9 := OSMutexAccept_partial_solve_wit_9_pure -> OSMutexAccept_partial_solve_wit_9_aux.

Definition OSMutexAccept_partial_solve_wit_10_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt_2 8))) (PreH2 : ((curPrio (task)) <= (Z.shiftr cnt 8))) (PreH3 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) <> 255)) (PreH4 : ((Z.land cnt_2 255) = 255)) (PreH5 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH6 : ((Z.land cnt 255) = 255)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (isr = (intNesting ((IntrState (before)))))) (PreH9 : (isr <= 0)) (PreH10 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH11 : (isr <= 0)) (PreH12 : (0 <= isr)) (PreH13 : (isr <= 255)) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (isr = (intNesting ((IntrState (before)))))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH17 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (perr_pre = pd)) (PreH25 : (perr_pre <> 0)) (PreH26 : (isr = (intNesting ((IntrState (before)))))) (PreH27 : (isr >= 0)) (PreH28 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (120) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ”
.

Definition OSMutexAccept_partial_solve_wit_10_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt_2 8))) (PreH2 : ((curPrio (task)) <= (Z.shiftr cnt 8))) (PreH3 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) <> 255)) (PreH4 : ((Z.land cnt_2 255) = 255)) (PreH5 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH6 : ((Z.land cnt 255) = 255)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (isr = (intNesting ((IntrState (before)))))) (PreH9 : (isr <= 0)) (PreH10 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH11 : (isr <= 0)) (PreH12 : (0 <= isr)) (PreH13 : (isr <= 255)) (PreH14 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH15 : (isr = (intNesting ((IntrState (before)))))) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH17 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (perr_pre = pd)) (PreH25 : (perr_pre <> 0)) (PreH26 : (isr = (intNesting ((IntrState (before)))))) (PreH27 : (isr >= 0)) (PreH28 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (120) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ” 
  &&  “ ((curPrio (task)) <= (Z.shiftr cnt 8)) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) <> 255) ” 
  &&  “ ((Z.land cnt_2 255) = 255) ” 
  &&  “ ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8)) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (120) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMutexAccept_partial_solve_wit_10 := OSMutexAccept_partial_solve_wit_10_pure -> OSMutexAccept_partial_solve_wit_10_aux.

Definition OSMutexAccept_partial_solve_wit_11_pure := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt_2: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((mutex_accept_pcp_code ((Z.shiftr cnt_2 8)) ((curPrio (task)))) = 0)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((curPrio (task)) > (Z.shiftr cnt_2 8))) (PreH5 : ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) <> 255)) (PreH6 : ((Z.land cnt 255) = 255)) (PreH7 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8))) (PreH8 : ((Z.land cnt_2 255) = 255)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : (isr <= 0)) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (isr <= 0)) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH17 : (isr = (intNesting ((IntrState (before)))))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (perr_pre = pd)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((IntrState (before)))))) (PreH29 : (isr >= 0)) (PreH30 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ ((Z.shiftr cnt 8) = (Z.shiftr cnt 8)) ” 
  &&  “ ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0) ” 
  &&  “ ((Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))) = (Z.lor (Z.land cnt 65280) (curPrio (task)))) ”
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt_2: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((mutex_accept_pcp_code ((Z.shiftr cnt_2 8)) ((curPrio (task)))) = 0)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((curPrio (task)) > (Z.shiftr cnt_2 8))) (PreH5 : ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) <> 255)) (PreH6 : ((Z.land cnt 255) = 255)) (PreH7 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8))) (PreH8 : ((Z.land cnt_2 255) = 255)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : (isr <= 0)) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (isr <= 0)) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH17 : (isr = (intNesting ((IntrState (before)))))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (perr_pre = pd)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((IntrState (before)))))) (PreH29 : (isr >= 0)) (PreH30 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))) = (Z.lor (Z.land cnt 65280) (curPrio (task)))) ” 
  &&  “ ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0) ”
).

Definition OSMutexAccept_partial_solve_wit_11_pure_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt_2: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((mutex_accept_pcp_code ((Z.shiftr cnt_2 8)) ((curPrio (task)))) = 0)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((curPrio (task)) > (Z.shiftr cnt_2 8))) (PreH5 : ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) <> 255)) (PreH6 : ((Z.land cnt 255) = 255)) (PreH7 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8))) (PreH8 : ((Z.land cnt_2 255) = 255)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : (isr <= 0)) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (isr <= 0)) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH17 : (isr = (intNesting ((IntrState (before)))))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (perr_pre = pd)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((IntrState (before)))))) (PreH29 : (isr >= 0)) (PreH30 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))) = (Z.lor (Z.land cnt 65280) (curPrio (task)))) ”
.

Definition OSMutexAccept_partial_solve_wit_11_pure_split_goal_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt_2: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((mutex_accept_pcp_code ((Z.shiftr cnt_2 8)) ((curPrio (task)))) = 0)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((curPrio (task)) > (Z.shiftr cnt_2 8))) (PreH5 : ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) <> 255)) (PreH6 : ((Z.land cnt 255) = 255)) (PreH7 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8))) (PreH8 : ((Z.land cnt_2 255) = 255)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : (isr <= 0)) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (isr <= 0)) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH17 : (isr = (intNesting ((IntrState (before)))))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (perr_pre = pd)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((IntrState (before)))))) (PreH29 : (isr >= 0)) (PreH30 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0) ”
.

Definition OSMutexAccept_partial_solve_wit_11_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt_2: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((mutex_accept_pcp_code ((Z.shiftr cnt_2 8)) ((curPrio (task)))) = 0)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((curPrio (task)) > (Z.shiftr cnt_2 8))) (PreH5 : ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) <> 255)) (PreH6 : ((Z.land cnt 255) = 255)) (PreH7 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8))) (PreH8 : ((Z.land cnt_2 255) = 255)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : (isr <= 0)) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (isr <= 0)) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH17 : (isr = (intNesting ((IntrState (before)))))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (perr_pre = pd)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((IntrState (before)))))) (PreH29 : (isr >= 0)) (PreH30 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ ((Z.shiftr cnt 8) = (Z.shiftr cnt 8)) ” 
  &&  “ ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0) ” 
  &&  “ ((Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))) = (Z.lor (Z.land cnt 65280) (curPrio (task)))) ” 
  &&  “ ((mutex_accept_pcp_code ((Z.shiftr cnt_2 8)) ((curPrio (task)))) = 0) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ ((curPrio (task)) > (Z.shiftr cnt_2 8)) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) <> 255) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8)) ” 
  &&  “ ((Z.land cnt_2 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt 8))
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (curPrio (task))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMutexAccept_partial_solve_wit_11 := OSMutexAccept_partial_solve_wit_11_pure -> OSMutexAccept_partial_solve_wit_11_aux.

Definition OSMutexAccept_partial_solve_wit_12_pure := 
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt_2: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((mutex_accept_pcp_code ((Z.shiftr cnt_2 8)) ((curPrio (task)))) = 0)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) = 255)) (PreH5 : ((Z.land cnt 255) = 255)) (PreH6 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8))) (PreH7 : ((Z.land cnt_2 255) = 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : (isr <= 0)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (perr_pre = pd)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((IntrState (before)))))) (PreH28 : (isr >= 0)) (PreH29 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ ((Z.shiftr cnt 8) = (Z.shiftr cnt 8)) ” 
  &&  “ ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0) ” 
  &&  “ ((Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))) = (Z.lor (Z.land cnt 65280) (curPrio (task)))) ”
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt_2: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((mutex_accept_pcp_code ((Z.shiftr cnt_2 8)) ((curPrio (task)))) = 0)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) = 255)) (PreH5 : ((Z.land cnt 255) = 255)) (PreH6 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8))) (PreH7 : ((Z.land cnt_2 255) = 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : (isr <= 0)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (perr_pre = pd)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((IntrState (before)))))) (PreH28 : (isr >= 0)) (PreH29 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))) = (Z.lor (Z.land cnt 65280) (curPrio (task)))) ” 
  &&  “ ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0) ”
).

Definition OSMutexAccept_partial_solve_wit_12_pure_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt_2: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((mutex_accept_pcp_code ((Z.shiftr cnt_2 8)) ((curPrio (task)))) = 0)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) = 255)) (PreH5 : ((Z.land cnt 255) = 255)) (PreH6 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8))) (PreH7 : ((Z.land cnt_2 255) = 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : (isr <= 0)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (perr_pre = pd)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((IntrState (before)))))) (PreH28 : (isr >= 0)) (PreH29 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))) = (Z.lor (Z.land cnt 65280) (curPrio (task)))) ”
.

Definition OSMutexAccept_partial_solve_wit_12_pure_split_goal_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt_2: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((mutex_accept_pcp_code ((Z.shiftr cnt_2 8)) ((curPrio (task)))) = 0)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) = 255)) (PreH5 : ((Z.land cnt 255) = 255)) (PreH6 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8))) (PreH7 : ((Z.land cnt_2 255) = 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : (isr <= 0)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (perr_pre = pd)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((IntrState (before)))))) (PreH28 : (isr >= 0)) (PreH29 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0) ”
.

Definition OSMutexAccept_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt_2: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((mutex_accept_pcp_code ((Z.shiftr cnt_2 8)) ((curPrio (task)))) = 0)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) = 255)) (PreH5 : ((Z.land cnt 255) = 255)) (PreH6 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8))) (PreH7 : ((Z.land cnt_2 255) = 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (isr = (intNesting ((IntrState (before)))))) (PreH10 : (isr <= 0)) (PreH11 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH12 : (isr <= 0)) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH16 : (isr = (intNesting ((IntrState (before)))))) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH18 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (perr_pre = pd)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((IntrState (before)))))) (PreH28 : (isr >= 0)) (PreH29 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ ((Z.shiftr cnt 8) = (Z.shiftr cnt 8)) ” 
  &&  “ ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0) ” 
  &&  “ ((Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))) = (Z.lor (Z.land cnt 65280) (curPrio (task)))) ” 
  &&  “ ((mutex_accept_pcp_code ((Z.shiftr cnt_2 8)) ((curPrio (task)))) = 0) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt_2 8)) (32)) = 255) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ ((Z.shiftr cnt_2 8) = (Z.shiftr cnt 8)) ” 
  &&  “ ((Z.land cnt_2 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt 8))
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (curPrio (task))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMutexAccept_partial_solve_wit_12 := OSMutexAccept_partial_solve_wit_12_pure -> OSMutexAccept_partial_solve_wit_12_aux.

Definition OSMutexAccept_partial_solve_wit_13_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt_2 8))) (PreH2 : ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (retval >= 0)) (PreH5 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) = 255)) (PreH6 : ((Z.land cnt_2 255) = 255)) (PreH7 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH8 : ((Z.land cnt 255) = 255)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : (isr <= 0)) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (isr <= 0)) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH17 : (isr = (intNesting ((IntrState (before)))))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (perr_pre = pd)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((IntrState (before)))))) (PreH29 : (isr >= 0)) (PreH30 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ”
.

Definition OSMutexAccept_partial_solve_wit_13_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt_2 8))) (PreH2 : ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (retval >= 0)) (PreH5 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) = 255)) (PreH6 : ((Z.land cnt_2 255) = 255)) (PreH7 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH8 : ((Z.land cnt 255) = 255)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : (isr <= 0)) (PreH12 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH13 : (isr <= 0)) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH17 : (isr = (intNesting ((IntrState (before)))))) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (pevent_pre <> 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (perr_pre = pd)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((IntrState (before)))))) (PreH29 : (isr >= 0)) (PreH30 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ” 
  &&  “ ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) = 255) ” 
  &&  “ ((Z.land cnt_2 255) = 255) ” 
  &&  “ ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8)) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMutexAccept_partial_solve_wit_13 := OSMutexAccept_partial_solve_wit_13_pure -> OSMutexAccept_partial_solve_wit_13_aux.

Definition OSMutexAccept_partial_solve_wit_14_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt_2 8))) (PreH2 : ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (retval >= 0)) (PreH5 : ((curPrio (task)) > (Z.shiftr cnt 8))) (PreH6 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) <> 255)) (PreH7 : ((Z.land cnt_2 255) = 255)) (PreH8 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH9 : ((Z.land cnt 255) = 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (isr = (intNesting ((IntrState (before)))))) (PreH12 : (isr <= 0)) (PreH13 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH14 : (isr <= 0)) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH18 : (isr = (intNesting ((IntrState (before)))))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (pevent_pre <> 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (perr_pre = pd)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((IntrState (before)))))) (PreH30 : (isr >= 0)) (PreH31 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ”
.

Definition OSMutexAccept_partial_solve_wit_14_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (tid: Z) (task: TaskAbstractState) (m: MutexFields) (cnt_2: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.shiftr cnt_2 8) = (Z.shiftr cnt_2 8))) (PreH2 : ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (retval >= 0)) (PreH5 : ((curPrio (task)) > (Z.shiftr cnt 8))) (PreH6 : ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) <> 255)) (PreH7 : ((Z.land cnt_2 255) = 255)) (PreH8 : ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8))) (PreH9 : ((Z.land cnt 255) = 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (isr = (intNesting ((IntrState (before)))))) (PreH12 : (isr <= 0)) (PreH13 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH14 : (isr <= 0)) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH18 : (isr = (intNesting ((IntrState (before)))))) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (pevent_pre <> 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (perr_pre = pd)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((IntrState (before)))))) (PreH30 : (isr >= 0)) (PreH31 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ” 
  &&  “ ((mutex_accept_pcp_code ((Z.shiftr cnt 8)) ((curPrio (task)))) = 0) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (retval >= 0) ” 
  &&  “ ((curPrio (task)) > (Z.shiftr cnt 8)) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr cnt 8)) (32)) <> 255) ” 
  &&  “ ((Z.land cnt_2 255) = 255) ” 
  &&  “ ((Z.shiftr cnt 8) = (Z.shiftr cnt_2 8)) ” 
  &&  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMutexAccept_partial_solve_wit_14 := OSMutexAccept_partial_solve_wit_14_pure -> OSMutexAccept_partial_solve_wit_14_aux.

Definition OSMutexAccept_partial_solve_wit_15_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land cnt 255) <> 255)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (isr = (intNesting ((IntrState (before)))))) (PreH4 : (isr <= 0)) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (isr <= 0)) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (perr_pre = pd)) (PreH20 : (perr_pre <> 0)) (PreH21 : (isr = (intNesting ((IntrState (before)))))) (PreH22 : (isr >= 0)) (PreH23 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) <> 255) ”
.

Definition OSMutexAccept_partial_solve_wit_15_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (m: MutexFields) (cnt: Z) (ptr: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land cnt 255) <> 255)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (isr = (intNesting ((IntrState (before)))))) (PreH4 : (isr <= 0)) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (isr <= 0)) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (perr_pre = pd)) (PreH20 : (perr_pre <> 0)) (PreH21 : (isr = (intNesting ((IntrState (before)))))) (PreH22 : (isr >= 0)) (PreH23 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((Z.land cnt 255) <> 255) ” 
  &&  “ ((Z.land cnt 255) <> 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMutexAccept_partial_solve_wit_15 := OSMutexAccept_partial_solve_wit_15_pure -> OSMutexAccept_partial_solve_wit_15_aux.

Definition OSMutexAccept_partial_solve_wit_16_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land cnt 255) <> 255)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (isr = (intNesting ((IntrState (before)))))) (PreH4 : (isr <= 0)) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (isr <= 0)) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (perr_pre = pd)) (PreH20 : (perr_pre <> 0)) (PreH21 : (isr = (intNesting ((IntrState (before)))))) (PreH22 : (isr >= 0)) (PreH23 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (0) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ”
.

Definition OSMutexAccept_partial_solve_wit_16_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (isr: Z) (pd: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (cnt: Z) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land cnt 255) <> 255)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (isr = (intNesting ((IntrState (before)))))) (PreH4 : (isr <= 0)) (PreH5 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH6 : (isr <= 0)) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH10 : (isr = (intNesting ((IntrState (before)))))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (0 <= UINT_MAX)) (PreH15 : (0 >= 0)) (PreH16 : (pe = (event_addr (sg) (eid)))) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (perr_pre = pd)) (PreH20 : (perr_pre <> 0)) (PreH21 : (isr = (intNesting ((IntrState (before)))))) (PreH22 : (isr >= 0)) (PreH23 : (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X )) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (0) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ” 
  &&  “ ((Z.land cnt 255) <> 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 4) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (perr_pre = pd) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (safeExec (LastSeen (before)) (bind ((atomic_cmd ((mutex_accept_public_program (critical) (sg) (invocation) (pe))))) (mutex_accept_observe_result)) X ) ”
  &&  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (0) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMutexAccept_partial_solve_wit_16 := OSMutexAccept_partial_solve_wit_16_pure -> OSMutexAccept_partial_solve_wit_16_aux.

Definition OSMutexAccept_which_implies_wit_1 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) ,
  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) ,
  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
).

Definition OSMutexAccept_which_implies_wit_1_split_goal_1 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) ,
  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMutexAccept_which_implies_wit_1_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) ,
  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
|--
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
.

Definition OSMutexAccept_which_implies_wit_2 := 
(
forall (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
) \/
(
forall (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
).

Definition OSMutexAccept_which_implies_wit_2_split_goal_spatial := 
forall (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
.

Definition OSMutexAccept_which_implies_wit_3 := 
(
forall (isr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH2 : (isr = (intNesting ((IntrState (before)))))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  “ ((encode_event_type ((eventType (observed)))) = 4) ” 
  &&  “ (isr = (intNesting ((IntrState (before))))) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
) \/
(
forall (isr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH2 : (isr = (intNesting ((IntrState (before)))))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
).

Definition OSMutexAccept_which_implies_wit_3_split_goal_1 := 
forall (isr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH2 : (isr = (intNesting ((IntrState (before)))))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  “ ((encode_event_type ((eventType (observed)))) = 4) ”
.

Definition OSMutexAccept_which_implies_wit_3_split_goal_spatial := 
forall (isr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 4)) (PreH2 : (isr = (intNesting ((IntrState (before)))))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
|--
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
.

Definition OSMutexAccept_which_implies_wit_4 := 
(
forall (isr: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((IntrState (before)))))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
|--
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
) \/
(
forall (isr: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((IntrState (before)))))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
|--
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
).

Definition OSMutexAccept_which_implies_wit_4_split_goal_spatial := 
forall (isr: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (isr = (intNesting ((IntrState (before)))))) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
|--
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
.

Definition OSMutexAccept_which_implies_wit_5 := 
(
forall (isr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (context: OsSchedCallContext) (PreH1 : (pe <> 0)) (PreH2 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH3 : (isr = (intNesting ((IntrState (before)))))) (PreH4 : (isr <= 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
|--
  “ (isr = (intNesting ((IntrState (before))))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 4) ”
  &&  (coq_prop (kernel_call_task_source (context) (before)) )
  **  (coq_prop (mutex_accept_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (UCOS2_inv sg before )
) \/
(
forall (isr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (context: OsSchedCallContext) (PreH1 : (pe <> 0)) (PreH2 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH3 : (isr = (intNesting ((IntrState (before)))))) (PreH4 : (isr <= 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
|--
  (coq_prop (kernel_call_task_source (context) (before)) )
  **  (coq_prop (mutex_accept_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (UCOS2_inv sg before )
).

Definition OSMutexAccept_which_implies_wit_5_split_goal_spatial := 
forall (isr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (context: OsSchedCallContext) (PreH1 : (pe <> 0)) (PreH2 : ((encode_event_type ((eventType (observed)))) = 4)) (PreH3 : (isr = (intNesting ((IntrState (before)))))) (PreH4 : (isr <= 0)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
|--
  (coq_prop (kernel_call_task_source (context) (before)) )
  **  (coq_prop (mutex_accept_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (UCOS2_inv sg before )
.

Definition OSMutexAccept_which_implies_wit_6 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (mutex_accept_call_support environment saved_local sg context entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (m: MutexFields)  (cnt: Z)  (ptr: Z)  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (mutex_accept_call_support environment saved_local sg context entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (m: MutexFields)  (cnt: Z)  (ptr: Z)  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
).

Definition OSMutexAccept_which_implies_wit_7 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (ptr_2: Z) (cnt_2: Z) (m_2: MutexFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (pcp: Z) (PreH1 : ((Z.land cnt_2 255) = 255)) (PreH2 : (pcp = (Z.shiftr cnt_2 8))) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry_2) (eid) (current_2) (m_2) (cnt_2) (ptr_2)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (mutex_accept_call_support environment saved_local sg context entry_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr_2)
  **  (mutex_accept_event_frame sg entry_2 eid current_2 )
|--
  EX (tid: Z)  (task: TaskAbstractState)  (m: MutexFields)  (cnt: Z)  (ptr: Z)  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ ((Z.land cnt 255) = 255) ” 
  &&  “ (pcp = (Z.shiftr cnt 8)) ”
  &&  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (ptr_2: Z) (cnt_2: Z) (m_2: MutexFields) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (pcp: Z) (PreH1 : ((Z.land cnt_2 255) = 255)) (PreH2 : (pcp = (Z.shiftr cnt_2 8))) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry_2) (eid) (current_2) (m_2) (cnt_2) (ptr_2)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (mutex_accept_call_support environment saved_local sg context entry_2 )
  **  (mutex_accept_event_frame sg entry_2 eid current_2 )
|--
  EX (tid: Z)  (task: TaskAbstractState)  (m: MutexFields)  (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ ((Z.land cnt_2 255) = 255) ” 
  &&  “ (pcp = (Z.shiftr cnt_2 8)) ”
  &&  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt_2) (ptr_2)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
).

Definition OSMutexAccept_which_implies_wit_8 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (task: TaskAbstractState) (tid: Z) (ptr: Z) (cnt: Z) (m: MutexFields) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (cpu_sr: Z) (pcp: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Z.land cnt 255) = 255)) (PreH3 : (pcp = (Z.shiftr cnt 8))) (PreH4 : (pcp <> 255)) (PreH5 : ((curPrio (task)) <= pcp)) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (curPrio (task))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
|--
  “ (pcp = (Z.shiftr cnt 8)) ”
  &&  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (120) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (task: TaskAbstractState) (tid: Z) (ptr: Z) (cnt: Z) (m: MutexFields) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (cpu_sr: Z) (pcp: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Z.land cnt 255) = 255)) (PreH3 : (pcp = (Z.shiftr cnt 8))) (PreH4 : (pcp <> 255)) (PreH5 : ((curPrio (task)) <= pcp)) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (curPrio (task))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
|--
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (120) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
).

Definition OSMutexAccept_which_implies_wit_8_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (task: TaskAbstractState) (tid: Z) (ptr: Z) (cnt: Z) (m: MutexFields) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (cpu_sr: Z) (pcp: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Z.land cnt 255) = 255)) (PreH3 : (pcp = (Z.shiftr cnt 8))) (PreH4 : (pcp <> 255)) (PreH5 : ((curPrio (task)) <= pcp)) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (curPrio (task))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
|--
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (120) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
.

Definition OSMutexAccept_which_implies_wit_9 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (task: TaskAbstractState) (tid: Z) (ptr: Z) (cnt: Z) (m: MutexFields) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (cpu_sr: Z) (pcp: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Z.land cnt 255) = 255)) (PreH3 : (pcp = (Z.shiftr cnt 8))) (PreH4 : ((mutex_accept_pcp_code (pcp) ((curPrio (task)))) = 0)) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (curPrio (task))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
|--
  “ (pcp = (Z.shiftr cnt 8)) ”
  &&  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (task: TaskAbstractState) (tid: Z) (ptr: Z) (cnt: Z) (m: MutexFields) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (cpu_sr: Z) (pcp: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Z.land cnt 255) = 255)) (PreH3 : (pcp = (Z.shiftr cnt 8))) (PreH4 : ((mutex_accept_pcp_code (pcp) ((curPrio (task)))) = 0)) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (curPrio (task))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
|--
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
).

Definition OSMutexAccept_which_implies_wit_9_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (task: TaskAbstractState) (tid: Z) (ptr: Z) (cnt: Z) (m: MutexFields) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (cpu_sr: Z) (pcp: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Z.land cnt 255) = 255)) (PreH3 : (pcp = (Z.shiftr cnt 8))) (PreH4 : ((mutex_accept_pcp_code (pcp) ((curPrio (task)))) = 0)) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (curPrio (task))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
|--
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
.

Definition OSMutexAccept_which_implies_wit_10 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (ptr: Z) (cnt: Z) (m: MutexFields) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Z.land cnt 255) <> 255)) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
|--
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (0) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  (UCOS2_inv sg entry )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (ptr: Z) (cnt: Z) (m: MutexFields) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Z.land cnt 255) <> 255)) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
|--
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (0) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  (UCOS2_inv sg entry )
).

Definition OSMutexAccept_which_implies_wit_10_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (context: OsSchedCallContext) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (ptr: Z) (cnt: Z) (m: MutexFields) (current: OSEventAbstractState) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : ((Z.land cnt 255) <> 255)) ,
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
|--
  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (0) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  (UCOS2_inv sg entry )
.

Module Type VC_Correct.


Axiom proof_of_OSMutexAccept_safety_wit_1 : OSMutexAccept_safety_wit_1.
Axiom proof_of_OSMutexAccept_safety_wit_2 : OSMutexAccept_safety_wit_2.
Axiom proof_of_OSMutexAccept_safety_wit_3 : OSMutexAccept_safety_wit_3.
Axiom proof_of_OSMutexAccept_safety_wit_4 : OSMutexAccept_safety_wit_4.
Axiom proof_of_OSMutexAccept_safety_wit_5 : OSMutexAccept_safety_wit_5.
Axiom proof_of_OSMutexAccept_safety_wit_6 : OSMutexAccept_safety_wit_6.
Axiom proof_of_OSMutexAccept_safety_wit_7 : OSMutexAccept_safety_wit_7.
Axiom proof_of_OSMutexAccept_safety_wit_8 : OSMutexAccept_safety_wit_8.
Axiom proof_of_OSMutexAccept_safety_wit_9 : OSMutexAccept_safety_wit_9.
Axiom proof_of_OSMutexAccept_entail_wit_1 : OSMutexAccept_entail_wit_1.
Axiom proof_of_OSMutexAccept_entail_wit_2 : OSMutexAccept_entail_wit_2.
Axiom proof_of_OSMutexAccept_entail_wit_3_1 : OSMutexAccept_entail_wit_3_1.
Axiom proof_of_OSMutexAccept_entail_wit_3_2 : OSMutexAccept_entail_wit_3_2.
Axiom proof_of_OSMutexAccept_return_wit_1 : OSMutexAccept_return_wit_1.
Axiom proof_of_OSMutexAccept_return_wit_2 : OSMutexAccept_return_wit_2.
Axiom proof_of_OSMutexAccept_return_wit_3 : OSMutexAccept_return_wit_3.
Axiom proof_of_OSMutexAccept_return_wit_4 : OSMutexAccept_return_wit_4.
Axiom proof_of_OSMutexAccept_return_wit_5 : OSMutexAccept_return_wit_5.
Axiom proof_of_OSMutexAccept_return_wit_6 : OSMutexAccept_return_wit_6.
Axiom proof_of_OSMutexAccept_return_wit_7 : OSMutexAccept_return_wit_7.
Axiom proof_of_OSMutexAccept_return_wit_8 : OSMutexAccept_return_wit_8.
Axiom proof_of_OSMutexAccept_partial_solve_wit_1_pure : OSMutexAccept_partial_solve_wit_1_pure.
Axiom proof_of_OSMutexAccept_partial_solve_wit_1 : OSMutexAccept_partial_solve_wit_1.
Axiom proof_of_OSMutexAccept_partial_solve_wit_2 : OSMutexAccept_partial_solve_wit_2.
Axiom proof_of_OSMutexAccept_partial_solve_wit_3_pure : OSMutexAccept_partial_solve_wit_3_pure.
Axiom proof_of_OSMutexAccept_partial_solve_wit_3 : OSMutexAccept_partial_solve_wit_3.
Axiom proof_of_OSMutexAccept_partial_solve_wit_4_pure : OSMutexAccept_partial_solve_wit_4_pure.
Axiom proof_of_OSMutexAccept_partial_solve_wit_4 : OSMutexAccept_partial_solve_wit_4.
Axiom proof_of_OSMutexAccept_partial_solve_wit_5_pure : OSMutexAccept_partial_solve_wit_5_pure.
Axiom proof_of_OSMutexAccept_partial_solve_wit_5 : OSMutexAccept_partial_solve_wit_5.
Axiom proof_of_OSMutexAccept_partial_solve_wit_6_pure : OSMutexAccept_partial_solve_wit_6_pure.
Axiom proof_of_OSMutexAccept_partial_solve_wit_6 : OSMutexAccept_partial_solve_wit_6.
Axiom proof_of_OSMutexAccept_partial_solve_wit_7_pure : OSMutexAccept_partial_solve_wit_7_pure.
Axiom proof_of_OSMutexAccept_partial_solve_wit_7 : OSMutexAccept_partial_solve_wit_7.
Axiom proof_of_OSMutexAccept_partial_solve_wit_8_pure : OSMutexAccept_partial_solve_wit_8_pure.
Axiom proof_of_OSMutexAccept_partial_solve_wit_8 : OSMutexAccept_partial_solve_wit_8.
Axiom proof_of_OSMutexAccept_partial_solve_wit_9_pure : OSMutexAccept_partial_solve_wit_9_pure.
Axiom proof_of_OSMutexAccept_partial_solve_wit_9 : OSMutexAccept_partial_solve_wit_9.
Axiom proof_of_OSMutexAccept_partial_solve_wit_10_pure : OSMutexAccept_partial_solve_wit_10_pure.
Axiom proof_of_OSMutexAccept_partial_solve_wit_10 : OSMutexAccept_partial_solve_wit_10.
Axiom proof_of_OSMutexAccept_partial_solve_wit_11_pure : OSMutexAccept_partial_solve_wit_11_pure.
Axiom proof_of_OSMutexAccept_partial_solve_wit_11 : OSMutexAccept_partial_solve_wit_11.
Axiom proof_of_OSMutexAccept_partial_solve_wit_12_pure : OSMutexAccept_partial_solve_wit_12_pure.
Axiom proof_of_OSMutexAccept_partial_solve_wit_12 : OSMutexAccept_partial_solve_wit_12.
Axiom proof_of_OSMutexAccept_partial_solve_wit_13_pure : OSMutexAccept_partial_solve_wit_13_pure.
Axiom proof_of_OSMutexAccept_partial_solve_wit_13 : OSMutexAccept_partial_solve_wit_13.
Axiom proof_of_OSMutexAccept_partial_solve_wit_14_pure : OSMutexAccept_partial_solve_wit_14_pure.
Axiom proof_of_OSMutexAccept_partial_solve_wit_14 : OSMutexAccept_partial_solve_wit_14.
Axiom proof_of_OSMutexAccept_partial_solve_wit_15_pure : OSMutexAccept_partial_solve_wit_15_pure.
Axiom proof_of_OSMutexAccept_partial_solve_wit_15 : OSMutexAccept_partial_solve_wit_15.
Axiom proof_of_OSMutexAccept_partial_solve_wit_16_pure : OSMutexAccept_partial_solve_wit_16_pure.
Axiom proof_of_OSMutexAccept_partial_solve_wit_16 : OSMutexAccept_partial_solve_wit_16.
Axiom proof_of_OSMutexAccept_which_implies_wit_1 : OSMutexAccept_which_implies_wit_1.
Axiom proof_of_OSMutexAccept_which_implies_wit_2 : OSMutexAccept_which_implies_wit_2.
Axiom proof_of_OSMutexAccept_which_implies_wit_3 : OSMutexAccept_which_implies_wit_3.
Axiom proof_of_OSMutexAccept_which_implies_wit_4 : OSMutexAccept_which_implies_wit_4.
Axiom proof_of_OSMutexAccept_which_implies_wit_5 : OSMutexAccept_which_implies_wit_5.
Axiom proof_of_OSMutexAccept_which_implies_wit_6 : OSMutexAccept_which_implies_wit_6.
Axiom proof_of_OSMutexAccept_which_implies_wit_7 : OSMutexAccept_which_implies_wit_7.
Axiom proof_of_OSMutexAccept_which_implies_wit_8 : OSMutexAccept_which_implies_wit_8.
Axiom proof_of_OSMutexAccept_which_implies_wit_9 : OSMutexAccept_which_implies_wit_9.
Axiom proof_of_OSMutexAccept_which_implies_wit_10 : OSMutexAccept_which_implies_wit_10.

End VC_Correct.
