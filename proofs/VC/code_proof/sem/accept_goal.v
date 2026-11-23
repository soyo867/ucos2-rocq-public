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
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_source_api_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSSemAccept -----*)

Definition OSSemAccept_safety_wit_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "cnt" ) )) # UShort  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (sem_accept_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemAccept_safety_wit_2 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = pe)) (PreH2 : (pevent_pre = 0)) (PreH3 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "cnt" ) )) # UShort  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (sem_accept_closed platform critical sg invocation origin mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemAccept_safety_wit_3 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (pevent_pre = 0)) (PreH4 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "cnt" ) )) # UShort  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (sem_accept_closed platform critical sg invocation origin mask before )
|--
  “ False ”
.

Definition OSSemAccept_safety_wit_4 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pevent_pre <> 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "cnt" ) )) # UShort  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemAccept_safety_wit_5 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: OSEventAbstractState) (cpu_sr: Z) (cnt: Z) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (after: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (sem_accept_checkpoint (entry) (eid) (current_2)) after )) (PreH2 : ((encode_event_cnt_value (current)) = (encode_event_cnt_value (current_2)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (sem_accept_source_api_safe critical sg invocation pe before X )) (PreH7 : (cnt = (encode_event_cnt_value (current)))) ,
  (sem_accept_closed platform critical sg invocation origin mask after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current_2)) )
  **  ((( &( "cnt" ) )) # UShort  |-> (encode_event_cnt_value (current)))
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSSemAccept_entail_wit_1_1 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) > 0)) (PreH2 : (0 <= (encode_event_cnt_value (current)))) (PreH3 : ((encode_event_cnt_value (current)) <= 65535)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = pe)) (PreH10 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry_2) (observed) (current)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((encode_event_cnt_value (current)) - 1 ))
  **  (sem_accept_count_frame sg entry_2 eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  EX (entry: UCOS2_Verify_State)  (current_2: OSEventAbstractState) ,
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (sem_accept_source_api_safe critical sg invocation pe before X ) ” 
  &&  “ ((encode_event_cnt_value (current)) = (encode_event_cnt_value (current_2))) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current_2)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (sem_accept_stored_count (current_2)))
  **  (sem_accept_count_frame sg entry eid current_2 )
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (current: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) > 0)) (PreH2 : (0 <= (encode_event_cnt_value (current)))) (PreH3 : ((encode_event_cnt_value (current)) <= 65535)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = pe)) (PreH10 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  “ (((encode_event_cnt_value (current)) - 1 ) = (sem_accept_stored_count (current))) ”
  &&  emp
).

Definition OSSemAccept_entail_wit_1_1_split_goal_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (current: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) > 0)) (PreH2 : (0 <= (encode_event_cnt_value (current)))) (PreH3 : ((encode_event_cnt_value (current)) <= 65535)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = pe)) (PreH10 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  “ (((encode_event_cnt_value (current)) - 1 ) = (sem_accept_stored_count (current))) ”
.

Definition OSSemAccept_entail_wit_1_1_split_goal_spatial := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (current: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) > 0)) (PreH2 : (0 <= (encode_event_cnt_value (current)))) (PreH3 : ((encode_event_cnt_value (current)) <= 65535)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = pe)) (PreH10 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  TT && emp 
.

Definition OSSemAccept_entail_wit_1_2 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (retval: Z) (entry_2: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) <= 0)) (PreH2 : (0 <= (encode_event_cnt_value (current)))) (PreH3 : ((encode_event_cnt_value (current)) <= 65535)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = pe)) (PreH10 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry_2) (observed) (current)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (sem_accept_count_frame sg entry_2 eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  EX (entry: UCOS2_Verify_State)  (current_2: OSEventAbstractState) ,
  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (sem_accept_source_api_safe critical sg invocation pe before X ) ” 
  &&  “ ((encode_event_cnt_value (current)) = (encode_event_cnt_value (current_2))) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current_2)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (sem_accept_stored_count (current_2)))
  **  (sem_accept_count_frame sg entry eid current_2 )
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (current: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) <= 0)) (PreH2 : (0 <= (encode_event_cnt_value (current)))) (PreH3 : ((encode_event_cnt_value (current)) <= 65535)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = pe)) (PreH10 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  “ ((encode_event_cnt_value (current)) = (sem_accept_stored_count (current))) ”
  &&  emp
).

Definition OSSemAccept_entail_wit_1_2_split_goal_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (current: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) <= 0)) (PreH2 : (0 <= (encode_event_cnt_value (current)))) (PreH3 : ((encode_event_cnt_value (current)) <= 65535)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = pe)) (PreH10 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  “ ((encode_event_cnt_value (current)) = (sem_accept_stored_count (current))) ”
.

Definition OSSemAccept_entail_wit_1_2_split_goal_spatial := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (current: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) <= 0)) (PreH2 : (0 <= (encode_event_cnt_value (current)))) (PreH3 : ((encode_event_cnt_value (current)) <= 65535)) (PreH4 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = pe)) (PreH10 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  TT && emp 
.

Definition OSSemAccept_return_wit_1 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: OSEventAbstractState) (cpu_sr: Z) (cnt: Z) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (after_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (sem_accept_checkpoint (entry) (eid) (current_2)) after_2 )) (PreH2 : ((encode_event_cnt_value (current)) = (encode_event_cnt_value (current_2)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (sem_accept_source_api_safe critical sg invocation pe before X )) (PreH7 : (cnt = (encode_event_cnt_value (current)))) ,
  (sem_accept_closed platform critical sg invocation origin mask after_2 )
  **  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current_2)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (sem_accept_source_api_return_safe after (encode_event_cnt_value (current)) X ) ”
  &&  (coq_prop (sem_accept_source_api_post (critical) (sg) (invocation) (pe) (before) ((encode_event_cnt_value (current))) (after)) )
  **  (sem_accept_closed platform critical sg invocation origin mask after )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: OSEventAbstractState) (cpu_sr: Z) (cnt: Z) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (after_2: UCOS2_Verify_State) (PreH1 : (critical_region_interval critical sg invocation (sem_accept_checkpoint (entry) (eid) (current_2)) after_2 )) (PreH2 : ((encode_event_cnt_value (current)) = (encode_event_cnt_value (current_2)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (sem_accept_source_api_safe critical sg invocation pe before X )) (PreH7 : (cnt = (encode_event_cnt_value (current)))) ,
  (sem_accept_closed platform critical sg invocation origin mask after_2 )
  **  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current_2)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (sem_accept_source_api_return_safe after (encode_event_cnt_value (current)) X ) ”
  &&  (coq_prop (sem_accept_source_api_post (critical) (sg) (invocation) (pe) (before) ((encode_event_cnt_value (current))) (after)) )
  **  (sem_accept_closed platform critical sg invocation origin mask after )
).

Definition OSSemAccept_return_wit_2 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) <> 3)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pevent_pre <> 0)) (PreH4 : (pevent_pre = pe)) (PreH5 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (sem_accept_type_frame sg before eid observed )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (sem_accept_source_api_return_safe after 0 X ) ”
  &&  (coq_prop (sem_accept_source_api_post (critical) (sg) (invocation) (pe) (before) (0) (after)) )
  **  (sem_accept_closed platform critical sg invocation origin mask after )
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) <> 3)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pevent_pre <> 0)) (PreH4 : (pevent_pre = pe)) (PreH5 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (sem_accept_type_frame sg before eid observed )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (sem_accept_source_api_return_safe after 0 X ) ”
  &&  (coq_prop (sem_accept_source_api_post (critical) (sg) (invocation) (pe) (before) (0) (after)) )
  **  (sem_accept_closed platform critical sg invocation origin mask after )
).

Definition OSSemAccept_return_wit_3 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (sem_accept_closed platform critical sg invocation origin mask before )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (sem_accept_source_api_return_safe after 0 X ) ”
  &&  (coq_prop (sem_accept_source_api_post (critical) (sg) (invocation) (pe) (before) (0) (after)) )
  **  (sem_accept_closed platform critical sg invocation origin mask after )
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (sem_accept_closed platform critical sg invocation origin mask before )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (sem_accept_source_api_return_safe after 0 X ) ”
  &&  (coq_prop (sem_accept_source_api_post (critical) (sg) (invocation) (pe) (before) (0) (after)) )
  **  (sem_accept_closed platform critical sg invocation origin mask after )
).

Definition OSSemAccept_return_wit_4 := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (pevent_pre = 0)) (PreH4 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (sem_accept_closed platform critical sg invocation origin mask before )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (sem_accept_source_api_return_safe after 0 X ) ”
  &&  (coq_prop (sem_accept_source_api_post (critical) (sg) (invocation) (pe) (before) (0) (after)) )
  **  (sem_accept_closed platform critical sg invocation origin mask after )
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (pevent_pre = 0)) (PreH4 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (sem_accept_closed platform critical sg invocation origin mask before )
|--
  EX (after: UCOS2_Verify_State) ,
  “ (sem_accept_source_api_return_safe after 0 X ) ”
  &&  (coq_prop (sem_accept_source_api_post (critical) (sg) (invocation) (pe) (before) (0) (after)) )
  **  (sem_accept_closed platform critical sg invocation origin mask after )
).

Definition OSSemAccept_partial_solve_wit_1_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "cnt" ) )) # UShort  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (sem_accept_closed platform critical sg invocation origin mask before )
|--
  “ (pe <> 0) ”
.

Definition OSSemAccept_partial_solve_wit_1_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (sem_accept_closed platform critical sg invocation origin mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_accept_source_api_safe critical sg invocation pe before X ) ”
  &&  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (sem_accept_closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
.

Definition OSSemAccept_partial_solve_wit_1 := OSSemAccept_partial_solve_wit_1_pure -> OSSemAccept_partial_solve_wit_1_aux.

Definition OSSemAccept_partial_solve_wit_2_pure := 
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pevent_pre <> 0)) (PreH4 : (pevent_pre = pe)) (PreH5 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (sem_accept_type_frame sg before eid observed )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "cnt" ) )) # UShort  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  “ (pe <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ”
) \/
(
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pevent_pre <> 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (sem_accept_type_frame sg before eid observed )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "cnt" ) )) # UShort  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  “ ((encode_event_type ((eventType (observed)))) = 3) ”
).

Definition OSSemAccept_partial_solve_wit_2_pure_split_goal_1 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pevent_pre <> 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (sem_accept_type_frame sg before eid observed )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "cnt" ) )) # UShort  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  “ ((encode_event_type ((eventType (observed)))) = 3) ”
.

Definition OSSemAccept_partial_solve_wit_2_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pevent_pre <> 0)) (PreH4 : (pevent_pre = pe)) (PreH5 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (sem_accept_type_frame sg before eid observed )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  “ (pe <> 0) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_accept_source_api_safe critical sg invocation pe before X ) ”
  &&  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (sem_accept_type_frame sg before eid observed )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
.

Definition OSSemAccept_partial_solve_wit_2 := OSSemAccept_partial_solve_wit_2_pure -> OSSemAccept_partial_solve_wit_2_aux.

Definition OSSemAccept_partial_solve_wit_3_pure := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pevent_pre <> 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (sem_accept_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "cnt" ) )) # UShort  |->_)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  “ ((encode_event_type ((eventType (observed)))) = 3) ”
.

Definition OSSemAccept_partial_solve_wit_3_aux := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pevent_pre <> 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (sem_accept_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_accept_source_api_safe critical sg invocation pe before X ) ”
  &&  (coq_prop (sem_accept_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
.

Definition OSSemAccept_partial_solve_wit_3 := OSSemAccept_partial_solve_wit_3_pure -> OSSemAccept_partial_solve_wit_3_aux.

Definition OSSemAccept_partial_solve_wit_4 := 
forall (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (retval: Z) (PreH1 : ((encode_event_type ((eventType (observed)))) = 3)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pevent_pre <> 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (sem_accept_source_api_safe critical sg invocation pe before X )) ,
  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
|--
  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((unsigned_last_nbits ((encode_event_type ((eventType (observed))))) (32)) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (sem_accept_source_api_safe critical sg invocation pe before X ) ”
  &&  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (sem_accept_profile (sg)) )
.

Definition OSSemAccept_partial_solve_wit_5_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cpu_sr: Z) (cnt: Z) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (sem_accept_source_api_safe critical sg invocation pe before X )) (PreH4 : (cnt = (encode_event_cnt_value (current)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  ((( &( "cnt" ) )) # UShort  |-> cnt)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (sem_accept_stored_count (current)))
  **  (sem_accept_count_frame sg entry eid current )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_cnt_value (current)) = (encode_event_cnt_value (current))) ”
.

Definition OSSemAccept_partial_solve_wit_5_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (entry: UCOS2_Verify_State) (current: OSEventAbstractState) (cpu_sr: Z) (cnt: Z) (PreH1 : (pe <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (sem_accept_source_api_safe critical sg invocation pe before X )) (PreH4 : (cnt = (encode_event_cnt_value (current)))) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  ((( &( "cnt" ) )) # UShort  |-> cnt)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (sem_accept_stored_count (current)))
  **  (sem_accept_count_frame sg entry eid current )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ ((encode_event_cnt_value (current)) = (encode_event_cnt_value (current))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (sem_accept_source_api_safe critical sg invocation pe before X ) ” 
  &&  “ (cnt = (encode_event_cnt_value (current))) ”
  &&  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "cnt" ) )) # UShort  |-> (encode_event_cnt_value (current)))
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (sem_accept_stored_count (current)))
  **  (sem_accept_count_frame sg entry eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSSemAccept_partial_solve_wit_5 := OSSemAccept_partial_solve_wit_5_pure -> OSSemAccept_partial_solve_wit_5_aux.

Definition OSSemAccept_partial_solve_wit_6 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current: OSEventAbstractState) (cpu_sr: Z) (cnt: Z) (entry: UCOS2_Verify_State) (current_2: OSEventAbstractState) (PreH1 : ((encode_event_cnt_value (current)) = (encode_event_cnt_value (current_2)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (sem_accept_source_api_safe critical sg invocation pe before X )) (PreH6 : (cnt = (encode_event_cnt_value (current)))) ,
  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current_2)) )
  **  (sem_accept_source_api_restore_pre platform critical sg invocation origin mask cpu_sr entry (sem_accept_checkpoint (entry) (eid) (current_2)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ ((encode_event_cnt_value (current)) = (encode_event_cnt_value (current_2))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (sem_accept_source_api_safe critical sg invocation pe before X ) ” 
  &&  “ (cnt = (encode_event_cnt_value (current))) ”
  &&  (sem_accept_source_api_restore_pre platform critical sg invocation origin mask cpu_sr entry (sem_accept_checkpoint (entry) (eid) (current_2)) )
  **  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current_2)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSSemAccept_which_implies_wit_1 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) ,
  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (sem_accept_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (sem_accept_type_frame sg before eid observed )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) ,
  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (sem_accept_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (sem_accept_type_frame sg before eid observed )
).

Definition OSSemAccept_which_implies_wit_1_split_goal_1 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) ,
  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (sem_accept_closed platform critical sg invocation origin mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSSemAccept_which_implies_wit_1_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) ,
  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (sem_accept_closed platform critical sg invocation origin mask before )
|--
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (sem_accept_type_frame sg before eid observed )
.

Definition OSSemAccept_which_implies_wit_2 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : ((encode_event_type ((eventType (observed)))) = 3)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (sem_accept_type_frame sg before eid observed )
|--
  “ ((encode_event_type ((eventType (observed)))) = 3) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (sem_accept_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_inv sg before )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : ((encode_event_type ((eventType (observed)))) = 3)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (sem_accept_type_frame sg before eid observed )
|--
  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (sem_accept_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_inv sg before )
).

Definition OSSemAccept_which_implies_wit_2_split_goal_1 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : ((encode_event_type ((eventType (observed)))) = 3)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (sem_accept_type_frame sg before eid observed )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSSemAccept_which_implies_wit_2_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (pe <> 0)) (PreH2 : ((encode_event_type ((eventType (observed)))) = 3)) ,
  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (sem_accept_call_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (sem_accept_type_frame sg before eid observed )
|--
  (coq_prop (sem_accept_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (sem_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_inv sg before )
.

Definition OSSemAccept_which_implies_wit_3 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) ,
  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (0 <= (encode_event_cnt_value (current))) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 65535) ”
  &&  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (sem_accept_count_frame sg entry eid current )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) ,
  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  (UCOS2_inv sg entry_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (0 <= (encode_event_cnt_value (current))) ” 
  &&  “ ((encode_event_cnt_value (current)) <= 65535) ”
  &&  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (sem_accept_count_frame sg entry eid current )
).

Definition OSSemAccept_which_implies_wit_4 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (cnt: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (cnt = (encode_event_cnt_value (current_2)))) ,
  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (sem_accept_stored_count (current_2)))
  **  (sem_accept_count_frame sg entry_2 eid current_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (cnt = (encode_event_cnt_value (current))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (sem_accept_source_api_restore_pre platform critical sg invocation origin mask cpu_sr entry (sem_accept_checkpoint (entry) (eid) (current)) )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (current_2: OSEventAbstractState) (entry_2: UCOS2_Verify_State) (cpu_sr: Z) (cnt: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (cnt = (encode_event_cnt_value (current_2)))) ,
  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry_2) (observed) (current_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (sem_accept_stored_count (current_2)))
  **  (sem_accept_count_frame sg entry_2 eid current_2 )
|--
  EX (entry: UCOS2_Verify_State)  (current: OSEventAbstractState) ,
  “ (cnt = (encode_event_cnt_value (current))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  (coq_prop (sem_accept_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (sem_accept_source_api_restore_pre platform critical sg invocation origin mask cpu_sr entry (sem_accept_checkpoint (entry) (eid) (current)) )
).

Module Type VC_Correct.


Axiom proof_of_OSSemAccept_safety_wit_1 : OSSemAccept_safety_wit_1.
Axiom proof_of_OSSemAccept_safety_wit_2 : OSSemAccept_safety_wit_2.
Axiom proof_of_OSSemAccept_safety_wit_3 : OSSemAccept_safety_wit_3.
Axiom proof_of_OSSemAccept_safety_wit_4 : OSSemAccept_safety_wit_4.
Axiom proof_of_OSSemAccept_safety_wit_5 : OSSemAccept_safety_wit_5.
Axiom proof_of_OSSemAccept_entail_wit_1_1 : OSSemAccept_entail_wit_1_1.
Axiom proof_of_OSSemAccept_entail_wit_1_2 : OSSemAccept_entail_wit_1_2.
Axiom proof_of_OSSemAccept_return_wit_1 : OSSemAccept_return_wit_1.
Axiom proof_of_OSSemAccept_return_wit_2 : OSSemAccept_return_wit_2.
Axiom proof_of_OSSemAccept_return_wit_3 : OSSemAccept_return_wit_3.
Axiom proof_of_OSSemAccept_return_wit_4 : OSSemAccept_return_wit_4.
Axiom proof_of_OSSemAccept_partial_solve_wit_1_pure : OSSemAccept_partial_solve_wit_1_pure.
Axiom proof_of_OSSemAccept_partial_solve_wit_1 : OSSemAccept_partial_solve_wit_1.
Axiom proof_of_OSSemAccept_partial_solve_wit_2_pure : OSSemAccept_partial_solve_wit_2_pure.
Axiom proof_of_OSSemAccept_partial_solve_wit_2 : OSSemAccept_partial_solve_wit_2.
Axiom proof_of_OSSemAccept_partial_solve_wit_3_pure : OSSemAccept_partial_solve_wit_3_pure.
Axiom proof_of_OSSemAccept_partial_solve_wit_3 : OSSemAccept_partial_solve_wit_3.
Axiom proof_of_OSSemAccept_partial_solve_wit_4 : OSSemAccept_partial_solve_wit_4.
Axiom proof_of_OSSemAccept_partial_solve_wit_5_pure : OSSemAccept_partial_solve_wit_5_pure.
Axiom proof_of_OSSemAccept_partial_solve_wit_5 : OSSemAccept_partial_solve_wit_5.
Axiom proof_of_OSSemAccept_partial_solve_wit_6 : OSSemAccept_partial_solve_wit_6.
Axiom proof_of_OSSemAccept_which_implies_wit_1 : OSSemAccept_which_implies_wit_1.
Axiom proof_of_OSSemAccept_which_implies_wit_2 : OSSemAccept_which_implies_wit_2.
Axiom proof_of_OSSemAccept_which_implies_wit_3 : OSSemAccept_which_implies_wit_3.
Axiom proof_of_OSSemAccept_which_implies_wit_4 : OSSemAccept_which_implies_wit_4.

End VC_Correct.
