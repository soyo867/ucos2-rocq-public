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
Require Import Ucos2Verify.VC.code.queue.spec.q_post_opt_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSQPostOpt -----*)

Definition OSQPostOpt_safety_wit_1 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= options)) (PreH2 : (options <= 255)) (PreH3 : (0 <= UINT_MAX)) (PreH4 : (0 >= 0)) (PreH5 : (pevent_pre = pe)) (PreH6 : (pmsg_pre = message)) (PreH7 : (opt_pre = options)) (PreH8 : (q_post_profile sg )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (q_post_call_input critical sg caller pe before eid observed )) (PreH11 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH12 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPostOpt_safety_wit_2 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe <> 0)) (PreH10 : (valid_event_id sg eid )) (PreH11 : (q_post_profile sg )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (q_post_call_input critical sg caller pe before eid observed )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (0 <= options)) (PreH16 : (options <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (pmsg_pre = message)) (PreH21 : (opt_pre = options)) (PreH22 : (q_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_post_call_input critical sg caller pe before eid observed )) (PreH25 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH26 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_save_result environment critical saved_local sg caller mask retval before eid observed )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPostOpt_safety_wit_3 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (0 <= options)) (PreH13 : (options <= 255)) (PreH14 : ((Z.land options 1) <> 0)) (PreH15 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH16 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 0 (q_post_opt_schedule_flag (options)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPostOpt_safety_wit_4 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : ((Z.land options 1) = 0)) (PreH5 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH6 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (q_post_opt_schedule_flag (options)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPostOpt_safety_wit_5 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (q_2: QueueFields) (PreH1 : ((queue_entries (q_2)) >= (qSize (q_2)))) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (0 <= (qSize (q_2)))) (PreH5 : ((qSize (q_2)) <= 65535)) (PreH6 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (q_post_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (q_post_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (q_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (q_post_call_input critical sg caller pe before eid observed )) (PreH31 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 30 0 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPostOpt_safety_wit_6 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q: QueueFields) (pq: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= (queue_entries (q)))) (PreH5 : ((queue_entries (q)) < 65535)) (PreH6 : ((queue_entries (q)) < (qSize (q)))) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 0 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pq" ) )) # Ptr  |-> pq)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "opt" ) )) # UChar  |-> options)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQPostOpt_entail_wit_1 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = pe)) (PreH2 : (pmsg_pre = message)) (PreH3 : (opt_pre = options)) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (pmsg_pre = message)) (PreH5 : (opt_pre = options)) (PreH6 : (q_post_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (q_post_call_input critical sg caller pe before eid observed )) (PreH9 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ (opt_pre <= 255) ” 
  &&  “ (0 <= opt_pre) ”
  &&  emp
).

Definition OSQPostOpt_entail_wit_1_split_goal_1 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (pmsg_pre = message)) (PreH5 : (opt_pre = options)) (PreH6 : (q_post_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (q_post_call_input critical sg caller pe before eid observed )) (PreH9 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (opt_pre <= 255)
.

Definition OSQPostOpt_entail_wit_1_split_goal_2 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (pmsg_pre = message)) (PreH5 : (opt_pre = options)) (PreH6 : (q_post_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (q_post_call_input critical sg caller pe before eid observed )) (PreH9 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (0 <= opt_pre)
.

Definition OSQPostOpt_entail_wit_2 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : (pevent_pre <> 0)) (PreH8 : (0 <= options)) (PreH9 : (options <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (pmsg_pre = message)) (PreH14 : (opt_pre = options)) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : (pevent_pre <> 0)) (PreH8 : (0 <= options)) (PreH9 : (options <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (pmsg_pre = message)) (PreH14 : (opt_pre = options)) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ”
  &&  emp
).

Definition OSQPostOpt_entail_wit_2_split_goal_1 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : (pevent_pre <> 0)) (PreH8 : (0 <= options)) (PreH9 : (options <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (pmsg_pre = message)) (PreH14 : (opt_pre = options)) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((event_slot_type_value ((EventState (before))) (eid)) <= 255)
.

Definition OSQPostOpt_entail_wit_2_split_goal_2 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : (pevent_pre <> 0)) (PreH8 : (0 <= options)) (PreH9 : (options <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pevent_pre = pe)) (PreH13 : (pmsg_pre = message)) (PreH14 : (opt_pre = options)) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH20 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (0 <= (event_slot_type_value ((EventState (before))) (eid)))
.

Definition OSQPostOpt_entail_wit_3 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((Z.land opt_pre 1) <> 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_post_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (0 <= options)) (PreH19 : (options <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (opt_pre = options)) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH29 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_post_opt_loop_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed initial_2 message state_2 node_2 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state_2) (node_2)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  (q_post_opt_loop_context environment critical saved_local sg caller active mask retval before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
.

Definition OSQPostOpt_entail_wit_4 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : ((Z.land options 1) <> 0)) (PreH6 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH7 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_loop_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 message state_2 node_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state_2) (node_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
.

Definition OSQPostOpt_entail_wit_5 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (state_3: UCOS2_Verify_State) (node_3: OSEventAbstractState) (tid_2: Z) (old_2: TaskAbstractState) (retval: Z) (PreH1 : ((unsigned_last_nbits ((q_post_group (state_2) (node_2))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (0 <= options)) (PreH13 : (options <= 255)) (PreH14 : ((Z.land options 1) <> 0)) (PreH15 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH16 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (event_task_rdy_post sg (TskState (state_3)) eid node_3 tid_2 old_2 message 4 0 (q_post_sched_group (state_3)) (q_post_sched_rows (state_3)) retval )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_post_opt_loop_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 message state_3 node_3 tid_2 old_2 )
|--
  EX (priority: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old message 4 0 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
.

Definition OSQPostOpt_entail_wit_6 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_post_opt_loop_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 message state_2 node_2 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state_2) (node_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
.

Definition OSQPostOpt_entail_wit_7 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (tid_2: Z) (old_2: TaskAbstractState) (retval_2: Z) (PreH1 : ((Z.land opt_pre 1) = 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (0 <= options)) (PreH18 : (options <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (pmsg_pre = message)) (PreH23 : (opt_pre = options)) (PreH24 : (q_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_post_call_input critical sg caller pe before eid observed )) (PreH27 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH28 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (event_task_rdy_post sg (TskState (acquired_3)) eid current_3 tid_2 old_2 pmsg_pre 4 0 (q_post_sched_group (acquired_3)) (q_post_sched_rows (acquired_3)) retval_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_post_wake_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 tid_2 old_2 )
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  EX (priority: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) = 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 4 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (tid_2: Z) (old_2: TaskAbstractState) (retval_2: Z) (PreH1 : ((Z.land opt_pre 1) = 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (0 <= options)) (PreH18 : (options <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (pmsg_pre = message)) (PreH23 : (opt_pre = options)) (PreH24 : (q_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_post_call_input critical sg caller pe before eid observed )) (PreH27 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH28 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (event_task_rdy_post sg (TskState (acquired_3)) eid current_3 tid_2 old_2 pmsg_pre 4 0 (q_post_sched_group (acquired_3)) (q_post_sched_rows (acquired_3)) retval_2 )
  **  (q_post_wake_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 tid_2 old_2 )
|--
  EX (priority: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (opt_pre = options) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ ((event_addr (sg) (eid)) = pe) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) = 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 4 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
).

Definition OSQPostOpt_entail_wit_8_1 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (q_3: QueueFields) (q_4: QueueFields) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (q_5: QueueFields) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (PreH1 : ((queue_out_addr (q_5)) = (qStart (q_5)))) (PreH2 : ((Z.land opt_pre 2) <> 0)) (PreH3 : (0 <= (queue_entries (q_4)))) (PreH4 : ((queue_entries (q_4)) < 65535)) (PreH5 : ((queue_entries (q_4)) < (qSize (q_4)))) (PreH6 : (((queue_in_addr (q_4)) + 4 ) <= (queue_end_addr (q_4)))) (PreH7 : ((qStart (q_4)) <= (q_post_opt_next_out (q_4)))) (PreH8 : ((q_post_opt_next_out (q_4)) < (queue_end_addr (q_4)))) (PreH9 : ((queue_entries (q_3)) < (qSize (q_3)))) (PreH10 : (0 <= (queue_entries (q_3)))) (PreH11 : ((queue_entries (q_3)) <= 65535)) (PreH12 : (0 <= (qSize (q_3)))) (PreH13 : ((qSize (q_3)) <= 65535)) (PreH14 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) = 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_post_profile sg )) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pe <> 0)) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (0 <= options)) (PreH30 : (options <= 255)) (PreH31 : (0 <= UINT_MAX)) (PreH32 : (0 >= 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (pmsg_pre = message)) (PreH35 : (opt_pre = options)) (PreH36 : (q_post_profile sg )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : (q_post_call_input critical sg caller pe before eid observed )) (PreH39 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH40 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 q_5 free_2 slots_2 (qcb_addr (sg) ((qID (q)))) )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_end_addr (q_5)) + ((-1) * sizeof(PTR))))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (((q_post_opt_next_out (q_5))) # Ptr  |->_)
  **  (q_post_opt_front_slot_frame q_5 slots_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q_2: QueueFields) ,
  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 2) <> 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) < 65535) ” 
  &&  “ ((queue_entries (q_2)) < (qSize (q_2))) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ”
  &&  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired eid observed current q_2 free slots (qcb_addr (sg) ((qID (q)))) )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_post_opt_next_out (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (((q_post_opt_next_out (q_2))) # Ptr  |->_)
  **  (q_post_opt_front_slot_frame q_2 slots )
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (q_3: QueueFields) (q_4: QueueFields) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (q_5: QueueFields) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (PreH1 : ((queue_out_addr (q_5)) = (qStart (q_5)))) (PreH2 : ((Z.land opt_pre 2) <> 0)) (PreH3 : (0 <= (queue_entries (q_4)))) (PreH4 : ((queue_entries (q_4)) < 65535)) (PreH5 : ((queue_entries (q_4)) < (qSize (q_4)))) (PreH6 : (((queue_in_addr (q_4)) + 4 ) <= (queue_end_addr (q_4)))) (PreH7 : ((qStart (q_4)) <= (q_post_opt_next_out (q_4)))) (PreH8 : ((q_post_opt_next_out (q_4)) < (queue_end_addr (q_4)))) (PreH9 : ((queue_entries (q_3)) < (qSize (q_3)))) (PreH10 : (0 <= (queue_entries (q_3)))) (PreH11 : ((queue_entries (q_3)) <= 65535)) (PreH12 : (0 <= (qSize (q_3)))) (PreH13 : ((qSize (q_3)) <= 65535)) (PreH14 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) = 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_post_profile sg )) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pe <> 0)) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (0 <= options)) (PreH30 : (options <= 255)) (PreH31 : (0 <= UINT_MAX)) (PreH32 : (0 >= 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (pmsg_pre = message)) (PreH35 : (opt_pre = options)) (PreH36 : (q_post_profile sg )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : (q_post_call_input critical sg caller pe before eid observed )) (PreH39 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH40 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 q_5 free_2 slots_2 (qcb_addr (sg) ((qID (q)))) )
  **  (((q_post_opt_next_out (q_5))) # Ptr  |->_)
  **  (q_post_opt_front_slot_frame q_5 slots_2 )
|--
  EX (x: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q_2: QueueFields) ,
  “ (opt_pre = options) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ ((event_addr (sg) (eid)) = pe) ” 
  &&  “ ((qStart (q_5)) = (qStart (q_2))) ” 
  &&  “ ((queue_end_addr (q_5)) = (queue_end_addr (q_2))) ” 
  &&  “ ((qSize (q_5)) = (qSize (q_2))) ” 
  &&  “ ((queue_entries (q_5)) = (queue_entries (q_2))) ” 
  &&  “ (((queue_end_addr (q_5)) + ((-1) * sizeof(PTR))) = (q_post_opt_next_out (q_2))) ” 
  &&  “ ((queue_in_addr (q_5)) = (queue_in_addr (q_2))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 2) <> 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) < 65535) ” 
  &&  “ ((queue_entries (q_2)) < (qSize (q_2))) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ”
  &&  (((q_post_opt_next_out (q_2))) # Ptr  |-> x)
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired eid observed current q_2 free slots (qcb_addr (sg) ((qID (q)))) )
  **  (q_post_opt_front_slot_frame q_2 slots )
).

Definition OSQPostOpt_entail_wit_8_2 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (q_3: QueueFields) (q_4: QueueFields) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (q_5: QueueFields) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (PreH1 : ((queue_out_addr (q_5)) <> (qStart (q_5)))) (PreH2 : ((Z.land opt_pre 2) <> 0)) (PreH3 : (0 <= (queue_entries (q_4)))) (PreH4 : ((queue_entries (q_4)) < 65535)) (PreH5 : ((queue_entries (q_4)) < (qSize (q_4)))) (PreH6 : (((queue_in_addr (q_4)) + 4 ) <= (queue_end_addr (q_4)))) (PreH7 : ((qStart (q_4)) <= (q_post_opt_next_out (q_4)))) (PreH8 : ((q_post_opt_next_out (q_4)) < (queue_end_addr (q_4)))) (PreH9 : ((queue_entries (q_3)) < (qSize (q_3)))) (PreH10 : (0 <= (queue_entries (q_3)))) (PreH11 : ((queue_entries (q_3)) <= 65535)) (PreH12 : (0 <= (qSize (q_3)))) (PreH13 : ((qSize (q_3)) <= 65535)) (PreH14 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) = 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_post_profile sg )) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pe <> 0)) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (0 <= options)) (PreH30 : (options <= 255)) (PreH31 : (0 <= UINT_MAX)) (PreH32 : (0 >= 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (pmsg_pre = message)) (PreH35 : (opt_pre = options)) (PreH36 : (q_post_profile sg )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : (q_post_call_input critical sg caller pe before eid observed )) (PreH39 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH40 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 q_5 free_2 slots_2 (qcb_addr (sg) ((qID (q)))) )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> ((queue_out_addr (q_5)) + ((-1) * sizeof(PTR))))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (((q_post_opt_next_out (q_5))) # Ptr  |->_)
  **  (q_post_opt_front_slot_frame q_5 slots_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q_2: QueueFields) ,
  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 2) <> 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) < 65535) ” 
  &&  “ ((queue_entries (q_2)) < (qSize (q_2))) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ”
  &&  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired eid observed current q_2 free slots (qcb_addr (sg) ((qID (q)))) )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_post_opt_next_out (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (((q_post_opt_next_out (q_2))) # Ptr  |->_)
  **  (q_post_opt_front_slot_frame q_2 slots )
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (q_3: QueueFields) (q_4: QueueFields) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (q_5: QueueFields) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (PreH1 : ((queue_out_addr (q_5)) <> (qStart (q_5)))) (PreH2 : ((Z.land opt_pre 2) <> 0)) (PreH3 : (0 <= (queue_entries (q_4)))) (PreH4 : ((queue_entries (q_4)) < 65535)) (PreH5 : ((queue_entries (q_4)) < (qSize (q_4)))) (PreH6 : (((queue_in_addr (q_4)) + 4 ) <= (queue_end_addr (q_4)))) (PreH7 : ((qStart (q_4)) <= (q_post_opt_next_out (q_4)))) (PreH8 : ((q_post_opt_next_out (q_4)) < (queue_end_addr (q_4)))) (PreH9 : ((queue_entries (q_3)) < (qSize (q_3)))) (PreH10 : (0 <= (queue_entries (q_3)))) (PreH11 : ((queue_entries (q_3)) <= 65535)) (PreH12 : (0 <= (qSize (q_3)))) (PreH13 : ((qSize (q_3)) <= 65535)) (PreH14 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) = 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_post_profile sg )) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pe <> 0)) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (0 <= options)) (PreH30 : (options <= 255)) (PreH31 : (0 <= UINT_MAX)) (PreH32 : (0 >= 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (pmsg_pre = message)) (PreH35 : (opt_pre = options)) (PreH36 : (q_post_profile sg )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : (q_post_call_input critical sg caller pe before eid observed )) (PreH39 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH40 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 q_5 free_2 slots_2 (qcb_addr (sg) ((qID (q)))) )
  **  (((q_post_opt_next_out (q_5))) # Ptr  |->_)
  **  (q_post_opt_front_slot_frame q_5 slots_2 )
|--
  EX (x: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q_2: QueueFields) ,
  “ (opt_pre = options) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ ((event_addr (sg) (eid)) = pe) ” 
  &&  “ ((qStart (q_5)) = (qStart (q_2))) ” 
  &&  “ ((queue_end_addr (q_5)) = (queue_end_addr (q_2))) ” 
  &&  “ ((qSize (q_5)) = (qSize (q_2))) ” 
  &&  “ ((queue_entries (q_5)) = (queue_entries (q_2))) ” 
  &&  “ (((queue_out_addr (q_5)) + ((-1) * sizeof(PTR))) = (q_post_opt_next_out (q_2))) ” 
  &&  “ ((queue_in_addr (q_5)) = (queue_in_addr (q_2))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 2) <> 0) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) < 65535) ” 
  &&  “ ((queue_entries (q_2)) < (qSize (q_2))) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ”
  &&  (((q_post_opt_next_out (q_2))) # Ptr  |-> x)
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired eid observed current q_2 free slots (qcb_addr (sg) ((qID (q)))) )
  **  (q_post_opt_front_slot_frame q_2 slots )
).

Definition OSQPostOpt_entail_wit_9_1 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q_2: QueueFields) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (pq: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : ((Z.land options 2) <> 0)) (PreH5 : (0 <= (queue_entries (q_2)))) (PreH6 : ((queue_entries (q_2)) < 65535)) (PreH7 : ((queue_entries (q_2)) < (qSize (q_2)))) (PreH8 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 q_2 free_2 slots_2 pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_post_opt_next_out (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (((q_post_opt_next_out (q_2))) # Ptr  |-> message)
  **  (q_post_opt_front_slot_frame q_2 slots_2 )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) < 65535) ” 
  &&  “ ((queue_entries (q)) < (qSize (q))) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ”
  &&  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (q_post_opt_written_in (options) (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_post_opt_written_out (options) (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (q_post_opt_written_buffer options q message slots )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q_2: QueueFields) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (pq: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : ((Z.land options 2) <> 0)) (PreH5 : (0 <= (queue_entries (q_2)))) (PreH6 : ((queue_entries (q_2)) < 65535)) (PreH7 : ((queue_entries (q_2)) < (qSize (q_2)))) (PreH8 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 q_2 free_2 slots_2 pq )
  **  (((q_post_opt_next_out (q_2))) # Ptr  |-> message)
  **  (q_post_opt_front_slot_frame q_2 slots_2 )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ ((qStart (q_2)) = (qStart (q))) ” 
  &&  “ ((queue_end_addr (q_2)) = (queue_end_addr (q))) ” 
  &&  “ ((qSize (q_2)) = (qSize (q))) ” 
  &&  “ ((queue_entries (q_2)) = (queue_entries (q))) ” 
  &&  “ ((q_post_opt_next_out (q_2)) = (q_post_opt_written_out (options) (q))) ” 
  &&  “ ((queue_in_addr (q_2)) = (q_post_opt_written_in (options) (q))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) < 65535) ” 
  &&  “ ((queue_entries (q)) < (qSize (q))) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ”
  &&  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  (q_post_opt_written_buffer options q message slots )
).

Definition OSQPostOpt_entail_wit_9_2 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (q_3: QueueFields) (q_4: QueueFields) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (q_5: QueueFields) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (PreH1 : (((queue_in_addr (q_5)) + (1 * sizeof(PTR))) = (queue_end_addr (q_5)))) (PreH2 : ((Z.land opt_pre 2) = 0)) (PreH3 : (0 <= (queue_entries (q_4)))) (PreH4 : ((queue_entries (q_4)) < 65535)) (PreH5 : ((queue_entries (q_4)) < (qSize (q_4)))) (PreH6 : (((queue_in_addr (q_4)) + 4 ) <= (queue_end_addr (q_4)))) (PreH7 : ((qStart (q_4)) <= (q_post_opt_next_out (q_4)))) (PreH8 : ((q_post_opt_next_out (q_4)) < (queue_end_addr (q_4)))) (PreH9 : ((queue_entries (q_3)) < (qSize (q_3)))) (PreH10 : (0 <= (queue_entries (q_3)))) (PreH11 : ((queue_entries (q_3)) <= 65535)) (PreH12 : (0 <= (qSize (q_3)))) (PreH13 : ((qSize (q_3)) <= 65535)) (PreH14 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) = 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_post_profile sg )) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pe <> 0)) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (0 <= options)) (PreH30 : (options <= 255)) (PreH31 : (0 <= UINT_MAX)) (PreH32 : (0 >= 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (pmsg_pre = message)) (PreH35 : (opt_pre = options)) (PreH36 : (q_post_profile sg )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : (q_post_call_input critical sg caller pe before eid observed )) (PreH39 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH40 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 q_5 free_2 slots_2 (qcb_addr (sg) ((qID (q)))) )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (qStart (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (((queue_in_addr (q_5))) # Ptr  |-> pmsg_pre)
  **  (q_post_slot_frame q_5 slots_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q_2: QueueFields) ,
  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) < 65535) ” 
  &&  “ ((queue_entries (q_2)) < (qSize (q_2))) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ”
  &&  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired eid observed current q_2 free slots (qcb_addr (sg) ((qID (q)))) )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (q_post_opt_written_in (options) (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_post_opt_written_out (options) (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (q_post_opt_written_buffer options q_2 message slots )
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (q_3: QueueFields) (q_4: QueueFields) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (q_5: QueueFields) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (PreH1 : (((queue_in_addr (q_5)) + (1 * sizeof(PTR))) = (queue_end_addr (q_5)))) (PreH2 : ((Z.land opt_pre 2) = 0)) (PreH3 : (0 <= (queue_entries (q_4)))) (PreH4 : ((queue_entries (q_4)) < 65535)) (PreH5 : ((queue_entries (q_4)) < (qSize (q_4)))) (PreH6 : (((queue_in_addr (q_4)) + 4 ) <= (queue_end_addr (q_4)))) (PreH7 : ((qStart (q_4)) <= (q_post_opt_next_out (q_4)))) (PreH8 : ((q_post_opt_next_out (q_4)) < (queue_end_addr (q_4)))) (PreH9 : ((queue_entries (q_3)) < (qSize (q_3)))) (PreH10 : (0 <= (queue_entries (q_3)))) (PreH11 : ((queue_entries (q_3)) <= 65535)) (PreH12 : (0 <= (qSize (q_3)))) (PreH13 : ((qSize (q_3)) <= 65535)) (PreH14 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) = 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_post_profile sg )) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pe <> 0)) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (0 <= options)) (PreH30 : (options <= 255)) (PreH31 : (0 <= UINT_MAX)) (PreH32 : (0 >= 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (pmsg_pre = message)) (PreH35 : (opt_pre = options)) (PreH36 : (q_post_profile sg )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : (q_post_call_input critical sg caller pe before eid observed )) (PreH39 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH40 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 q_5 free_2 slots_2 (qcb_addr (sg) ((qID (q)))) )
  **  (((queue_in_addr (q_5))) # Ptr  |-> pmsg_pre)
  **  (q_post_slot_frame q_5 slots_2 )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q_2: QueueFields) ,
  “ (opt_pre = options) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ ((event_addr (sg) (eid)) = pe) ” 
  &&  “ ((qStart (q_5)) = (qStart (q_2))) ” 
  &&  “ ((queue_end_addr (q_5)) = (queue_end_addr (q_2))) ” 
  &&  “ ((qSize (q_5)) = (qSize (q_2))) ” 
  &&  “ ((queue_entries (q_5)) = (queue_entries (q_2))) ” 
  &&  “ ((queue_out_addr (q_5)) = (q_post_opt_written_out (options) (q_2))) ” 
  &&  “ ((qStart (q_5)) = (q_post_opt_written_in (options) (q_2))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) < 65535) ” 
  &&  “ ((queue_entries (q_2)) < (qSize (q_2))) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ”
  &&  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired eid observed current q_2 free slots (qcb_addr (sg) ((qID (q)))) )
  **  (q_post_opt_written_buffer options q_2 message slots )
).

Definition OSQPostOpt_entail_wit_9_3 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (q_3: QueueFields) (q_4: QueueFields) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (q_5: QueueFields) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (PreH1 : (((queue_in_addr (q_5)) + (1 * sizeof(PTR))) <> (queue_end_addr (q_5)))) (PreH2 : ((Z.land opt_pre 2) = 0)) (PreH3 : (0 <= (queue_entries (q_4)))) (PreH4 : ((queue_entries (q_4)) < 65535)) (PreH5 : ((queue_entries (q_4)) < (qSize (q_4)))) (PreH6 : (((queue_in_addr (q_4)) + 4 ) <= (queue_end_addr (q_4)))) (PreH7 : ((qStart (q_4)) <= (q_post_opt_next_out (q_4)))) (PreH8 : ((q_post_opt_next_out (q_4)) < (queue_end_addr (q_4)))) (PreH9 : ((queue_entries (q_3)) < (qSize (q_3)))) (PreH10 : (0 <= (queue_entries (q_3)))) (PreH11 : ((queue_entries (q_3)) <= 65535)) (PreH12 : (0 <= (qSize (q_3)))) (PreH13 : ((qSize (q_3)) <= 65535)) (PreH14 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) = 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_post_profile sg )) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pe <> 0)) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (0 <= options)) (PreH30 : (options <= 255)) (PreH31 : (0 <= UINT_MAX)) (PreH32 : (0 >= 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (pmsg_pre = message)) (PreH35 : (opt_pre = options)) (PreH36 : (q_post_profile sg )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : (q_post_call_input critical sg caller pe before eid observed )) (PreH39 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH40 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 q_5 free_2 slots_2 (qcb_addr (sg) ((qID (q)))) )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> ((queue_in_addr (q_5)) + (1 * sizeof(PTR))))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_5)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (((queue_in_addr (q_5))) # Ptr  |-> pmsg_pre)
  **  (q_post_slot_frame q_5 slots_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q_2: QueueFields) ,
  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) < 65535) ” 
  &&  “ ((queue_entries (q_2)) < (qSize (q_2))) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ”
  &&  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired eid observed current q_2 free slots (qcb_addr (sg) ((qID (q)))) )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (q_post_opt_written_in (options) (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_post_opt_written_out (options) (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (q_post_opt_written_buffer options q_2 message slots )
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (q_3: QueueFields) (q_4: QueueFields) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (current_3: OSEventAbstractState) (q_5: QueueFields) (free_2: (@list Z)) (slots_2: (@list (@option Z))) (PreH1 : (((queue_in_addr (q_5)) + (1 * sizeof(PTR))) <> (queue_end_addr (q_5)))) (PreH2 : ((Z.land opt_pre 2) = 0)) (PreH3 : (0 <= (queue_entries (q_4)))) (PreH4 : ((queue_entries (q_4)) < 65535)) (PreH5 : ((queue_entries (q_4)) < (qSize (q_4)))) (PreH6 : (((queue_in_addr (q_4)) + 4 ) <= (queue_end_addr (q_4)))) (PreH7 : ((qStart (q_4)) <= (q_post_opt_next_out (q_4)))) (PreH8 : ((q_post_opt_next_out (q_4)) < (queue_end_addr (q_4)))) (PreH9 : ((queue_entries (q_3)) < (qSize (q_3)))) (PreH10 : (0 <= (queue_entries (q_3)))) (PreH11 : ((queue_entries (q_3)) <= 65535)) (PreH12 : (0 <= (qSize (q_3)))) (PreH13 : ((qSize (q_3)) <= 65535)) (PreH14 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) = 0)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_post_profile sg )) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (pe = (event_addr (sg) (eid)))) (PreH23 : (pe <> 0)) (PreH24 : (valid_event_id sg eid )) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (pevent_pre <> 0)) (PreH29 : (0 <= options)) (PreH30 : (options <= 255)) (PreH31 : (0 <= UINT_MAX)) (PreH32 : (0 >= 0)) (PreH33 : (pevent_pre = pe)) (PreH34 : (pmsg_pre = message)) (PreH35 : (opt_pre = options)) (PreH36 : (q_post_profile sg )) (PreH37 : (UCOS2_state_inv sg before )) (PreH38 : (q_post_call_input critical sg caller pe before eid observed )) (PreH39 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH40 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH41 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed current_3 q_5 free_2 slots_2 (qcb_addr (sg) ((qID (q)))) )
  **  (((queue_in_addr (q_5))) # Ptr  |-> pmsg_pre)
  **  (q_post_slot_frame q_5 slots_2 )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q_2: QueueFields) ,
  “ (opt_pre = options) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ ((event_addr (sg) (eid)) = pe) ” 
  &&  “ ((qStart (q_5)) = (qStart (q_2))) ” 
  &&  “ ((queue_end_addr (q_5)) = (queue_end_addr (q_2))) ” 
  &&  “ ((qSize (q_5)) = (qSize (q_2))) ” 
  &&  “ ((queue_entries (q_5)) = (queue_entries (q_2))) ” 
  &&  “ ((queue_out_addr (q_5)) = (q_post_opt_written_out (options) (q_2))) ” 
  &&  “ (((queue_in_addr (q_5)) + (1 * sizeof(PTR))) = (q_post_opt_written_in (options) (q_2))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= (queue_entries (q_2))) ” 
  &&  “ ((queue_entries (q_2)) < 65535) ” 
  &&  “ ((queue_entries (q_2)) < (qSize (q_2))) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ”
  &&  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired eid observed current q_2 free slots (qcb_addr (sg) ((qID (q)))) )
  **  (q_post_opt_written_buffer options q_2 message slots )
).

Definition OSQPostOpt_return_wit_1 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q: QueueFields) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= (queue_entries (q)))) (PreH5 : ((queue_entries (q)) < 65535)) (PreH6 : ((queue_entries (q)) < (qSize (q)))) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 0 )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q: QueueFields) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= (queue_entries (q)))) (PreH5 : ((queue_entries (q)) < 65535)) (PreH6 : ((queue_entries (q)) < (qSize (q)))) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 0 )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
).

Definition OSQPostOpt_return_wit_1_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q: QueueFields) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= (queue_entries (q)))) (PreH5 : ((queue_entries (q)) < 65535)) (PreH6 : ((queue_entries (q)) < (qSize (q)))) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 0 )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
.

Definition OSQPostOpt_return_wit_2 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (PreH1 : ((queue_entries (q)) >= (qSize (q)))) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (0 <= (qSize (q)))) (PreH5 : ((qSize (q)) <= 65535)) (PreH6 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (q_post_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (q_post_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (q_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (q_post_call_input critical sg caller pe before eid observed )) (PreH31 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 30 0 )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 30 X )
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (PreH1 : ((queue_entries (q)) >= (qSize (q)))) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (0 <= (qSize (q)))) (PreH5 : ((qSize (q)) <= 65535)) (PreH6 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (q_post_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (q_post_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (q_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (q_post_call_input critical sg caller pe before eid observed )) (PreH31 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 30 0 )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 30 X )
).

Definition OSQPostOpt_return_wit_2_split_goal_spatial := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (PreH1 : ((queue_entries (q)) >= (qSize (q)))) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) <= 65535)) (PreH4 : (0 <= (qSize (q)))) (PreH5 : ((qSize (q)) <= 65535)) (PreH6 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (q_post_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (q_post_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (q_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (q_post_call_input critical sg caller pe before eid observed )) (PreH31 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 30 0 )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 30 X )
.

Definition OSQPostOpt_return_wit_3 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (q_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (q_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
).

Definition OSQPostOpt_return_wit_3_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (q_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
.

Definition OSQPostOpt_return_wit_4 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (q_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) = 0)) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (q_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) = 0)) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
).

Definition OSQPostOpt_return_wit_4_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (q_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) = 0)) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
.

Definition OSQPostOpt_return_wit_5 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((Z.land options 4) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (0 <= options)) (PreH6 : (options <= 255)) (PreH7 : ((Z.land options 1) <> 0)) (PreH8 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH9 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : ((Z.land options 1) <> 0)) (PreH16 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH17 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 0 (q_post_opt_schedule_flag (options)) )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((Z.land options 4) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (0 <= options)) (PreH6 : (options <= 255)) (PreH7 : ((Z.land options 1) <> 0)) (PreH8 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH9 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : ((Z.land options 1) <> 0)) (PreH16 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH17 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 0 (q_post_opt_schedule_flag (options)) )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
).

Definition OSQPostOpt_return_wit_5_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((Z.land options 4) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (0 <= options)) (PreH6 : (options <= 255)) (PreH7 : ((Z.land options 1) <> 0)) (PreH8 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH9 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : ((Z.land options 1) <> 0)) (PreH16 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH17 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 0 (q_post_opt_schedule_flag (options)) )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
.

Definition OSQPostOpt_return_wit_6 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((Z.land options 4) <> 0)) (PreH2 : (pe <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : ((Z.land options 1) = 0)) (PreH6 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH7 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (q_post_opt_schedule_flag (options)) )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((Z.land options 4) <> 0)) (PreH2 : (pe <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : ((Z.land options 1) = 0)) (PreH6 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH7 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (q_post_opt_schedule_flag (options)) )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
).

Definition OSQPostOpt_return_wit_6_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((Z.land options 4) <> 0)) (PreH2 : (pe <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : ((Z.land options 1) = 0)) (PreH6 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH7 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (q_post_opt_schedule_flag (options)) )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
.

Definition OSQPostOpt_return_wit_7 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (q_post_call_input critical sg caller pe before eid observed )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (0 <= options)) (PreH12 : (options <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (pmsg_pre = message)) (PreH17 : (opt_pre = options)) (PreH18 : (q_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (q_post_call_input critical sg caller pe before eid observed )) (PreH21 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH22 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH23 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 1 X )
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (q_post_call_input critical sg caller pe before eid observed )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (0 <= options)) (PreH12 : (options <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (pmsg_pre = message)) (PreH17 : (opt_pre = options)) (PreH18 : (q_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (q_post_call_input critical sg caller pe before eid observed )) (PreH21 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH22 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH23 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 1 X )
).

Definition OSQPostOpt_return_wit_7_split_goal_spatial := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (q_post_call_input critical sg caller pe before eid observed )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (0 <= options)) (PreH12 : (options <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (pmsg_pre = message)) (PreH17 : (opt_pre = options)) (PreH18 : (q_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (q_post_call_input critical sg caller pe before eid observed )) (PreH21 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH22 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH23 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 1 X )
.

Definition OSQPostOpt_return_wit_8 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (pmsg_pre = message)) (PreH8 : (opt_pre = options)) (PreH9 : (q_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_post_call_input critical sg caller pe before eid observed )) (PreH12 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH13 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 4 X )
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (pmsg_pre = message)) (PreH8 : (opt_pre = options)) (PreH9 : (q_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_post_call_input critical sg caller pe before eid observed )) (PreH12 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH13 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 4 X )
).

Definition OSQPostOpt_return_wit_8_split_goal_spatial := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (pmsg_pre = message)) (PreH8 : (opt_pre = options)) (PreH9 : (q_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_post_call_input critical sg caller pe before eid observed )) (PreH12 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH13 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (q_post_opt_post environment critical saved_local sg caller mask pe eid message options before 4 X )
.

Definition OSQPostOpt_partial_solve_wit_1_pure := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (pmsg_pre = message)) (PreH8 : (opt_pre = options)) (PreH9 : (q_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_post_call_input critical sg caller pe before eid observed )) (PreH12 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH13 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ”
.

Definition OSQPostOpt_partial_solve_wit_1_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (pmsg_pre = message)) (PreH8 : (opt_pre = options)) (PreH9 : (q_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_post_call_input critical sg caller pe before eid observed )) (PreH12 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH13 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_closed environment critical saved_local sg caller mask before )
.

Definition OSQPostOpt_partial_solve_wit_1 := OSQPostOpt_partial_solve_wit_1_pure -> OSQPostOpt_partial_solve_wit_1_aux.

Definition OSQPostOpt_partial_solve_wit_2_pure := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (q_post_call_input critical sg caller pe before eid observed )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (0 <= options)) (PreH12 : (options <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (pmsg_pre = message)) (PreH17 : (opt_pre = options)) (PreH18 : (q_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (q_post_call_input critical sg caller pe before eid observed )) (PreH21 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH22 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH23 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ”
.

Definition OSQPostOpt_partial_solve_wit_2_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (q_post_call_input critical sg caller pe before eid observed )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (0 <= options)) (PreH12 : (options <= 255)) (PreH13 : (0 <= UINT_MAX)) (PreH14 : (0 >= 0)) (PreH15 : (pevent_pre = pe)) (PreH16 : (pmsg_pre = message)) (PreH17 : (opt_pre = options)) (PreH18 : (q_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (q_post_call_input critical sg caller pe before eid observed )) (PreH21 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH22 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH23 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
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
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
.

Definition OSQPostOpt_partial_solve_wit_2 := OSQPostOpt_partial_solve_wit_2_pure -> OSQPostOpt_partial_solve_wit_2_aux.

Definition OSQPostOpt_partial_solve_wit_3 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe <> 0)) (PreH10 : (valid_event_id sg eid )) (PreH11 : (q_post_profile sg )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (q_post_call_input critical sg caller pe before eid observed )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (0 <= options)) (PreH16 : (options <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (pmsg_pre = message)) (PreH21 : (opt_pre = options)) (PreH22 : (q_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_post_call_input critical sg caller pe before eid observed )) (PreH25 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH26 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_save_pre environment critical saved_local sg caller mask before pe eid observed )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_save_pre environment critical saved_local sg caller mask before (event_addr (sg) (eid)) eid observed )
.

Definition OSQPostOpt_partial_solve_wit_4_pure := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe <> 0)) (PreH10 : (valid_event_id sg eid )) (PreH11 : (q_post_profile sg )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (q_post_call_input critical sg caller pe before eid observed )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (0 <= options)) (PreH16 : (options <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (pmsg_pre = message)) (PreH21 : (opt_pre = options)) (PreH22 : (q_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_post_call_input critical sg caller pe before eid observed )) (PreH25 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH26 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_save_result environment critical saved_local sg caller mask retval before eid observed )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ”
.

Definition OSQPostOpt_partial_solve_wit_4_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe <> 0)) (PreH10 : (valid_event_id sg eid )) (PreH11 : (q_post_profile sg )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (q_post_call_input critical sg caller pe before eid observed )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (0 <= options)) (PreH16 : (options <= 255)) (PreH17 : (0 <= UINT_MAX)) (PreH18 : (0 >= 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (pmsg_pre = message)) (PreH21 : (opt_pre = options)) (PreH22 : (q_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (q_post_call_input critical sg caller pe before eid observed )) (PreH25 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH26 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
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
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_post_save_result environment critical saved_local sg caller mask retval before eid observed )
.

Definition OSQPostOpt_partial_solve_wit_4 := OSQPostOpt_partial_solve_wit_4_pure -> OSQPostOpt_partial_solve_wit_4_aux.

Definition OSQPostOpt_partial_solve_wit_5_pure := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land opt_pre 1) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH3 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_post_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (0 <= options)) (PreH19 : (options <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (opt_pre = options)) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH29 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) <> 0) ”
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) <> 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (0 <= options)) (PreH20 : (options <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (opt_pre = options)) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH30 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((q_post_group (acquired) (current)) <> 0) ”
).

Definition OSQPostOpt_partial_solve_wit_5_pure_split_goal_1 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) <> 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (0 <= options)) (PreH20 : (options <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (opt_pre = options)) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH30 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((q_post_group (acquired) (current)) <> 0) ”
.

Definition OSQPostOpt_partial_solve_wit_5_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land opt_pre 1) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH3 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_post_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (0 <= options)) (PreH19 : (options <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (opt_pre = options)) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH29 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) <> 0) ” 
  &&  “ ((Z.land opt_pre 1) <> 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
.

Definition OSQPostOpt_partial_solve_wit_5 := OSQPostOpt_partial_solve_wit_5_pure -> OSQPostOpt_partial_solve_wit_5_aux.

Definition OSQPostOpt_partial_solve_wit_6_pure := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (0 <= options)) (PreH13 : (options <= 255)) (PreH14 : ((Z.land options 1) <> 0)) (PreH15 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH16 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (state) (node)) <> 0) ”
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  “ ((q_post_group (state) (node)) <> 0) ”
).

Definition OSQPostOpt_partial_solve_wit_6_pure_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  “ ((q_post_group (state) (node)) <> 0) ”
.

Definition OSQPostOpt_partial_solve_wit_6_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (0 <= options)) (PreH13 : (options <= 255)) (PreH14 : ((Z.land options 1) <> 0)) (PreH15 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH16 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (state) (node)) <> 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
.

Definition OSQPostOpt_partial_solve_wit_6 := OSQPostOpt_partial_solve_wit_6_pure -> OSQPostOpt_partial_solve_wit_6_aux.

Definition OSQPostOpt_partial_solve_wit_7_pure := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (0 <= options)) (PreH6 : (options <= 255)) (PreH7 : ((Z.land options 1) <> 0)) (PreH8 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH9 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : ((Z.land options 1) <> 0)) (PreH16 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH17 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state_2 node_2 tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state_2 node_2 tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
).

Definition OSQPostOpt_partial_solve_wit_7_pure_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state_2 node_2 tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
.

Definition OSQPostOpt_partial_solve_wit_7_pure_split_goal_2 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state_2 node_2 tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ”
.

Definition OSQPostOpt_partial_solve_wit_7_pure_split_goal_3 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state_2 node_2 tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
.

Definition OSQPostOpt_partial_solve_wit_7_pure_split_goal_4 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state_2 node_2 tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
.

Definition OSQPostOpt_partial_solve_wit_7_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (0 <= options)) (PreH6 : (options <= 255)) (PreH7 : ((Z.land options 1) <> 0)) (PreH8 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH9 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : ((Z.land options 1) <> 0)) (PreH16 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH17 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state_2 node_2 tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  (q_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state_2 node_2 tid old )
.

Definition OSQPostOpt_partial_solve_wit_7 := OSQPostOpt_partial_solve_wit_7_pure -> OSQPostOpt_partial_solve_wit_7_aux.

Definition OSQPostOpt_partial_solve_wit_8_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (priority: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : ((Z.land options 1) <> 0)) (PreH6 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH7 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old message 4 0 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ”
.

Definition OSQPostOpt_partial_solve_wit_8_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (priority: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : ((Z.land options 1) <> 0)) (PreH6 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH7 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old message 4 0 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old message 4 0 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
.

Definition OSQPostOpt_partial_solve_wit_8 := OSQPostOpt_partial_solve_wit_8_pure -> OSQPostOpt_partial_solve_wit_8_aux.

Definition OSQPostOpt_partial_solve_wit_9_pure := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (0 <= options)) (PreH13 : (options <= 255)) (PreH14 : ((Z.land options 1) <> 0)) (PreH15 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH16 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ ((q_post_group (state) (node)) = 0) ”
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  “ ((q_post_group (state) (node)) = 0) ”
).

Definition OSQPostOpt_partial_solve_wit_9_pure_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  “ ((q_post_group (state) (node)) = 0) ”
.

Definition OSQPostOpt_partial_solve_wit_9_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (0 <= options)) (PreH13 : (options <= 255)) (PreH14 : ((Z.land options 1) <> 0)) (PreH15 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH16 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ ((q_post_group (state) (node)) = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
.

Definition OSQPostOpt_partial_solve_wit_9 := OSQPostOpt_partial_solve_wit_9_pure -> OSQPostOpt_partial_solve_wit_9_aux.

Definition OSQPostOpt_partial_solve_wit_10_pure := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land opt_pre 1) = 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH3 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_post_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (0 <= options)) (PreH19 : (options <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (opt_pre = options)) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH29 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) <> 0) ”
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) = 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (0 <= options)) (PreH20 : (options <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (opt_pre = options)) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH30 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((q_post_group (acquired) (current)) <> 0) ”
).

Definition OSQPostOpt_partial_solve_wit_10_pure_split_goal_1 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) = 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (0 <= options)) (PreH20 : (options <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (opt_pre = options)) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH30 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((q_post_group (acquired) (current)) <> 0) ”
.

Definition OSQPostOpt_partial_solve_wit_10_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((Z.land opt_pre 1) = 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH3 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_post_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (0 <= options)) (PreH19 : (options <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (opt_pre = options)) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH29 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) <> 0) ” 
  &&  “ ((Z.land opt_pre 1) = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
.

Definition OSQPostOpt_partial_solve_wit_10 := OSQPostOpt_partial_solve_wit_10_pure -> OSQPostOpt_partial_solve_wit_10_aux.

Definition OSQPostOpt_partial_solve_wit_11_pure := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((Z.land opt_pre 1) = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_post_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (0 <= options)) (PreH19 : (options <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (opt_pre = options)) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH29 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) = 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (0 <= options)) (PreH20 : (options <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (opt_pre = options)) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH30 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
).

Definition OSQPostOpt_partial_solve_wit_11_pure_split_goal_1 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) = 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (0 <= options)) (PreH20 : (options <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (opt_pre = options)) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH30 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
.

Definition OSQPostOpt_partial_solve_wit_11_pure_split_goal_2 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) = 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (0 <= options)) (PreH20 : (options <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (opt_pre = options)) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH30 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ”
.

Definition OSQPostOpt_partial_solve_wit_11_pure_split_goal_3 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) = 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (0 <= options)) (PreH20 : (options <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (opt_pre = options)) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH30 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
.

Definition OSQPostOpt_partial_solve_wit_11_pure_split_goal_4 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) = 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (q_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (0 <= options)) (PreH20 : (options <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pevent_pre = pe)) (PreH24 : (pmsg_pre = message)) (PreH25 : (opt_pre = options)) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH30 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH31 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
.

Definition OSQPostOpt_partial_solve_wit_11_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((Z.land opt_pre 1) = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_post_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (0 <= options)) (PreH19 : (options <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (opt_pre = options)) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH29 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ ((Z.land opt_pre 1) = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  (q_post_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 tid old )
.

Definition OSQPostOpt_partial_solve_wit_11 := OSQPostOpt_partial_solve_wit_11_pure -> OSQPostOpt_partial_solve_wit_11_aux.

Definition OSQPostOpt_partial_solve_wit_12_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (priority: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : ((Z.land options 1) = 0)) (PreH5 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH6 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 4 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
|--
  “ (pe <> 0) ” 
  &&  “ ((Z.land options 1) = 0) ”
.

Definition OSQPostOpt_partial_solve_wit_12_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (priority: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : ((Z.land options 1) = 0)) (PreH5 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH6 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 4 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
|--
  “ (pe <> 0) ” 
  &&  “ ((Z.land options 1) = 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) = 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 4 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
.

Definition OSQPostOpt_partial_solve_wit_12 := OSQPostOpt_partial_solve_wit_12_pure -> OSQPostOpt_partial_solve_wit_12_aux.

Definition OSQPostOpt_partial_solve_wit_13_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (0 <= options)) (PreH13 : (options <= 255)) (PreH14 : ((Z.land options 1) <> 0)) (PreH15 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH16 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (q_post_opt_schedule_flag (options)) )
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSQPostOpt_partial_solve_wit_13_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (0 <= options)) (PreH13 : (options <= 255)) (PreH14 : ((Z.land options 1) <> 0)) (PreH15 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH16 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (q_post_opt_schedule_flag (options)) )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr (event_addr (sg) (eid)) eid message options before acquired released 0 (q_post_opt_schedule_flag (options)) )
.

Definition OSQPostOpt_partial_solve_wit_13 := OSQPostOpt_partial_solve_wit_13_pure -> OSQPostOpt_partial_solve_wit_13_aux.

Definition OSQPostOpt_partial_solve_wit_14_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : ((Z.land options 1) = 0)) (PreH5 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH6 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (q_post_opt_schedule_flag (options)) )
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSQPostOpt_partial_solve_wit_14_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : ((Z.land options 1) = 0)) (PreH5 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH6 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (q_post_opt_schedule_flag (options)) )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) = 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (q_post_opt_schedule_flag (options)) )
.

Definition OSQPostOpt_partial_solve_wit_14 := OSQPostOpt_partial_solve_wit_14_pure -> OSQPostOpt_partial_solve_wit_14_aux.

Definition OSQPostOpt_partial_solve_wit_15_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (PreH1 : ((Z.land options 4) = 0)) (PreH2 : (pe <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : ((Z.land options 1) = 0)) (PreH6 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH7 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (q_post_opt_schedule_flag (options)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ ((Z.land options 4) = 0) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ”
.

Definition OSQPostOpt_partial_solve_wit_15_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((Z.land options 4) = 0)) (PreH2 : (pe <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : ((Z.land options 1) = 0)) (PreH6 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH7 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (q_post_opt_schedule_flag (options)) )
|--
  “ ((Z.land options 4) = 0) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ ((Z.land options 4) = 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) = 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (q_post_opt_schedule_flag (options)) )
.

Definition OSQPostOpt_partial_solve_wit_15 := OSQPostOpt_partial_solve_wit_15_pure -> OSQPostOpt_partial_solve_wit_15_aux.

Definition OSQPostOpt_partial_solve_wit_16_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((Z.land options 4) = 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (0 <= options)) (PreH6 : (options <= 255)) (PreH7 : ((Z.land options 1) <> 0)) (PreH8 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH9 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : ((Z.land options 1) <> 0)) (PreH16 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH17 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 0 (q_post_opt_schedule_flag (options)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ ((Z.land options 4) = 0) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ”
.

Definition OSQPostOpt_partial_solve_wit_16_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((Z.land options 4) = 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (0 <= options)) (PreH6 : (options <= 255)) (PreH7 : ((Z.land options 1) <> 0)) (PreH8 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH9 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : ((Z.land options 1) <> 0)) (PreH16 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH17 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 0 (q_post_opt_schedule_flag (options)) )
|--
  “ ((Z.land options 4) = 0) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ ((Z.land options 4) = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (q_post_opt_schedule_flag (options)) )
.

Definition OSQPostOpt_partial_solve_wit_16 := OSQPostOpt_partial_solve_wit_16_pure -> OSQPostOpt_partial_solve_wit_16_aux.

Definition OSQPostOpt_partial_solve_wit_17_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (q_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSQPostOpt_partial_solve_wit_17_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (q_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored ) ” 
  &&  “ ((Z.land options 4) = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
.

Definition OSQPostOpt_partial_solve_wit_17 := OSQPostOpt_partial_solve_wit_17_pure -> OSQPostOpt_partial_solve_wit_17_aux.

Definition OSQPostOpt_partial_solve_wit_18_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (q_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) = 0)) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSQPostOpt_partial_solve_wit_18_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (q_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) = 0)) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored ) ” 
  &&  “ ((Z.land options 4) = 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) = 0) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
.

Definition OSQPostOpt_partial_solve_wit_18 := OSQPostOpt_partial_solve_wit_18_pure -> OSQPostOpt_partial_solve_wit_18_aux.

Definition OSQPostOpt_partial_solve_wit_19_pure := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (0 <= options)) (PreH18 : (options <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (pmsg_pre = message)) (PreH23 : (opt_pre = options)) (PreH24 : (q_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_post_call_input critical sg caller pe before eid observed )) (PreH27 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH28 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) = 0) ”
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_post_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (0 <= options)) (PreH19 : (options <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (opt_pre = options)) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH29 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((q_post_group (acquired) (current)) = 0) ”
).

Definition OSQPostOpt_partial_solve_wit_19_pure_split_goal_1 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_post_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (0 <= options)) (PreH19 : (options <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (opt_pre = options)) (PreH25 : (q_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (q_post_call_input critical sg caller pe before eid observed )) (PreH28 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH29 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((q_post_group (acquired) (current)) = 0) ”
.

Definition OSQPostOpt_partial_solve_wit_19_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (0 <= options)) (PreH18 : (options <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (pmsg_pre = message)) (PreH23 : (opt_pre = options)) (PreH24 : (q_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_post_call_input critical sg caller pe before eid observed )) (PreH27 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH28 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
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
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
.

Definition OSQPostOpt_partial_solve_wit_19 := OSQPostOpt_partial_solve_wit_19_pure -> OSQPostOpt_partial_solve_wit_19_aux.

Definition OSQPostOpt_partial_solve_wit_20_pure := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (0 <= options)) (PreH18 : (options <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (pmsg_pre = message)) (PreH23 : (opt_pre = options)) (PreH24 : (q_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_post_call_input critical sg caller pe before eid observed )) (PreH27 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH28 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_pointer_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((qcb_addr (sg) ((qID (q)))) = (qcb_addr (sg) ((qID (q))))) ” 
  &&  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ”
.

Definition OSQPostOpt_partial_solve_wit_20_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (q: QueueFields) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (0 <= options)) (PreH18 : (options <= 255)) (PreH19 : (0 <= UINT_MAX)) (PreH20 : (0 >= 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (pmsg_pre = message)) (PreH23 : (opt_pre = options)) (PreH24 : (q_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_post_call_input critical sg caller pe before eid observed )) (PreH27 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH28 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
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
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_pointer_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
.

Definition OSQPostOpt_partial_solve_wit_20 := OSQPostOpt_partial_solve_wit_20_pure -> OSQPostOpt_partial_solve_wit_20_aux.

Definition OSQPostOpt_partial_solve_wit_21_pure := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q_2: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (PreH1 : ((queue_entries (q)) >= (qSize (q)))) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (0 <= (qSize (q)))) (PreH6 : ((qSize (q)) <= 65535)) (PreH7 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe <> 0)) (PreH10 : (valid_event_id sg eid )) (PreH11 : (q_post_profile sg )) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH14 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (q_post_call_input critical sg caller pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (0 <= options)) (PreH23 : (options <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (pmsg_pre = message)) (PreH28 : (opt_pre = options)) (PreH29 : (q_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (q_post_call_input critical sg caller pe before eid observed )) (PreH32 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH33 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q slots )
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (pe <> 0) ” 
  &&  “ ((queue_entries (q)) >= (qSize (q))) ”
.

Definition OSQPostOpt_partial_solve_wit_21_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q_2: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (PreH1 : ((queue_entries (q)) >= (qSize (q)))) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (0 <= (qSize (q)))) (PreH6 : ((qSize (q)) <= 65535)) (PreH7 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe <> 0)) (PreH10 : (valid_event_id sg eid )) (PreH11 : (q_post_profile sg )) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH14 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (q_post_call_input critical sg caller pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (0 <= options)) (PreH23 : (options <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (pmsg_pre = message)) (PreH28 : (opt_pre = options)) (PreH29 : (q_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (q_post_call_input critical sg caller pe before eid observed )) (PreH32 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH33 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
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
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q slots )
.

Definition OSQPostOpt_partial_solve_wit_21 := OSQPostOpt_partial_solve_wit_21_pure -> OSQPostOpt_partial_solve_wit_21_aux.

Definition OSQPostOpt_partial_solve_wit_22_pure := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (q_2: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (PreH1 : ((queue_entries (q_2)) >= (qSize (q_2)))) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (0 <= (qSize (q_2)))) (PreH5 : ((qSize (q_2)) <= 65535)) (PreH6 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (q_post_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (q_post_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (q_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (q_post_call_input critical sg caller pe before eid observed )) (PreH31 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_opt_restore_pre environment critical saved_local sg caller active mask retval pe eid message options before acquired_2 acquired_2 30 0 )
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (retval = retval) ”
.

Definition OSQPostOpt_partial_solve_wit_22_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q_2: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (PreH1 : ((queue_entries (q_2)) >= (qSize (q_2)))) (PreH2 : (0 <= (queue_entries (q_2)))) (PreH3 : ((queue_entries (q_2)) <= 65535)) (PreH4 : (0 <= (qSize (q_2)))) (PreH5 : ((qSize (q_2)) <= 65535)) (PreH6 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (valid_event_id sg eid )) (PreH10 : (q_post_profile sg )) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH12 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH13 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (q_post_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (q_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (q_post_call_input critical sg caller pe before eid observed )) (PreH31 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_opt_restore_pre environment critical saved_local sg caller active mask retval pe eid message options before acquired_2 acquired_2 30 0 )
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
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_opt_restore_pre environment critical saved_local sg caller active mask retval (event_addr (sg) (eid)) eid message options before acquired_2 acquired_2 30 0 )
.

Definition OSQPostOpt_partial_solve_wit_22 := OSQPostOpt_partial_solve_wit_22_pure -> OSQPostOpt_partial_solve_wit_22_aux.

Definition OSQPostOpt_partial_solve_wit_23_pure := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q_2: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (PreH1 : ((queue_entries (q)) < (qSize (q)))) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (0 <= (qSize (q)))) (PreH6 : ((qSize (q)) <= 65535)) (PreH7 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe <> 0)) (PreH10 : (valid_event_id sg eid )) (PreH11 : (q_post_profile sg )) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH14 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (q_post_call_input critical sg caller pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (0 <= options)) (PreH23 : (options <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (pmsg_pre = message)) (PreH28 : (opt_pre = options)) (PreH29 : (q_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (q_post_call_input critical sg caller pe before eid observed )) (PreH32 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH33 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q slots )
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((queue_entries (q)) < (qSize (q))) ”
.

Definition OSQPostOpt_partial_solve_wit_23_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q_2: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (PreH1 : ((queue_entries (q)) < (qSize (q)))) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (0 <= (queue_entries (q)))) (PreH4 : ((queue_entries (q)) <= 65535)) (PreH5 : (0 <= (qSize (q)))) (PreH6 : ((qSize (q)) <= 65535)) (PreH7 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe <> 0)) (PreH10 : (valid_event_id sg eid )) (PreH11 : (q_post_profile sg )) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH14 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH15 : (pe = (event_addr (sg) (eid)))) (PreH16 : (pe <> 0)) (PreH17 : (valid_event_id sg eid )) (PreH18 : (q_post_profile sg )) (PreH19 : (UCOS2_state_inv sg before )) (PreH20 : (q_post_call_input critical sg caller pe before eid observed )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (0 <= options)) (PreH23 : (options <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (pmsg_pre = message)) (PreH28 : (opt_pre = options)) (PreH29 : (q_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (q_post_call_input critical sg caller pe before eid observed )) (PreH32 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH33 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
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
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q slots )
.

Definition OSQPostOpt_partial_solve_wit_23 := OSQPostOpt_partial_solve_wit_23_pure -> OSQPostOpt_partial_solve_wit_23_aux.

Definition OSQPostOpt_partial_solve_wit_24_pure := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q_2: QueueFields) (q_3: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (PreH1 : ((Z.land opt_pre 2) <> 0)) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) < 65535)) (PreH4 : ((queue_entries (q)) < (qSize (q)))) (PreH5 : (((queue_in_addr (q)) + 4 ) <= (queue_end_addr (q)))) (PreH6 : ((qStart (q)) <= (q_post_opt_next_out (q)))) (PreH7 : ((q_post_opt_next_out (q)) < (queue_end_addr (q)))) (PreH8 : ((queue_entries (q_3)) < (qSize (q_3)))) (PreH9 : (0 <= (queue_entries (q_3)))) (PreH10 : ((queue_entries (q_3)) <= 65535)) (PreH11 : (0 <= (qSize (q_3)))) (PreH12 : ((qSize (q_3)) <= 65535)) (PreH13 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_post_profile sg )) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (pe <> 0)) (PreH23 : (valid_event_id sg eid )) (PreH24 : (q_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_post_call_input critical sg caller pe before eid observed )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (0 <= options)) (PreH29 : (options <= 255)) (PreH30 : (0 <= UINT_MAX)) (PreH31 : (0 >= 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (pmsg_pre = message)) (PreH34 : (opt_pre = options)) (PreH35 : (q_post_profile sg )) (PreH36 : (UCOS2_state_inv sg before )) (PreH37 : (q_post_call_input critical sg caller pe before eid observed )) (PreH38 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH39 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH40 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q slots )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((queue_entries (q)) < (qSize (q))) ”
.

Definition OSQPostOpt_partial_solve_wit_24_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q_2: QueueFields) (q_3: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (PreH1 : ((Z.land opt_pre 2) <> 0)) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) < 65535)) (PreH4 : ((queue_entries (q)) < (qSize (q)))) (PreH5 : (((queue_in_addr (q)) + 4 ) <= (queue_end_addr (q)))) (PreH6 : ((qStart (q)) <= (q_post_opt_next_out (q)))) (PreH7 : ((q_post_opt_next_out (q)) < (queue_end_addr (q)))) (PreH8 : ((queue_entries (q_3)) < (qSize (q_3)))) (PreH9 : (0 <= (queue_entries (q_3)))) (PreH10 : ((queue_entries (q_3)) <= 65535)) (PreH11 : (0 <= (qSize (q_3)))) (PreH12 : ((qSize (q_3)) <= 65535)) (PreH13 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_post_profile sg )) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (pe <> 0)) (PreH23 : (valid_event_id sg eid )) (PreH24 : (q_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_post_call_input critical sg caller pe before eid observed )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (0 <= options)) (PreH29 : (options <= 255)) (PreH30 : (0 <= UINT_MAX)) (PreH31 : (0 >= 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (pmsg_pre = message)) (PreH34 : (opt_pre = options)) (PreH35 : (q_post_profile sg )) (PreH36 : (UCOS2_state_inv sg before )) (PreH37 : (q_post_call_input critical sg caller pe before eid observed )) (PreH38 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH39 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH40 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q slots )
|--
  “ ((queue_entries (q)) < (qSize (q))) ” 
  &&  “ ((Z.land opt_pre 2) <> 0) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) < 65535) ” 
  &&  “ ((queue_entries (q)) < (qSize (q))) ” 
  &&  “ (((queue_in_addr (q)) + 4 ) <= (queue_end_addr (q))) ” 
  &&  “ ((qStart (q)) <= (q_post_opt_next_out (q))) ” 
  &&  “ ((q_post_opt_next_out (q)) < (queue_end_addr (q))) ” 
  &&  “ ((queue_entries (q_3)) < (qSize (q_3))) ” 
  &&  “ (0 <= (queue_entries (q_3))) ” 
  &&  “ ((queue_entries (q_3)) <= 65535) ” 
  &&  “ (0 <= (qSize (q_3))) ” 
  &&  “ ((qSize (q_3)) <= 65535) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q slots )
.

Definition OSQPostOpt_partial_solve_wit_24 := OSQPostOpt_partial_solve_wit_24_pure -> OSQPostOpt_partial_solve_wit_24_aux.

Definition OSQPostOpt_partial_solve_wit_25_pure := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q_2: QueueFields) (q_3: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (PreH1 : ((Z.land opt_pre 2) = 0)) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) < 65535)) (PreH4 : ((queue_entries (q)) < (qSize (q)))) (PreH5 : (((queue_in_addr (q)) + 4 ) <= (queue_end_addr (q)))) (PreH6 : ((qStart (q)) <= (q_post_opt_next_out (q)))) (PreH7 : ((q_post_opt_next_out (q)) < (queue_end_addr (q)))) (PreH8 : ((queue_entries (q_3)) < (qSize (q_3)))) (PreH9 : (0 <= (queue_entries (q_3)))) (PreH10 : ((queue_entries (q_3)) <= 65535)) (PreH11 : (0 <= (qSize (q_3)))) (PreH12 : ((qSize (q_3)) <= 65535)) (PreH13 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_post_profile sg )) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (pe <> 0)) (PreH23 : (valid_event_id sg eid )) (PreH24 : (q_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_post_call_input critical sg caller pe before eid observed )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (0 <= options)) (PreH29 : (options <= 255)) (PreH30 : (0 <= UINT_MAX)) (PreH31 : (0 >= 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (pmsg_pre = message)) (PreH34 : (opt_pre = options)) (PreH35 : (q_post_profile sg )) (PreH36 : (UCOS2_state_inv sg before )) (PreH37 : (q_post_call_input critical sg caller pe before eid observed )) (PreH38 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH39 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH40 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q slots )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((queue_entries (q)) < (qSize (q))) ”
.

Definition OSQPostOpt_partial_solve_wit_25_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q_2: QueueFields) (q_3: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q: QueueFields) (PreH1 : ((Z.land opt_pre 2) = 0)) (PreH2 : (0 <= (queue_entries (q)))) (PreH3 : ((queue_entries (q)) < 65535)) (PreH4 : ((queue_entries (q)) < (qSize (q)))) (PreH5 : (((queue_in_addr (q)) + 4 ) <= (queue_end_addr (q)))) (PreH6 : ((qStart (q)) <= (q_post_opt_next_out (q)))) (PreH7 : ((q_post_opt_next_out (q)) < (queue_end_addr (q)))) (PreH8 : ((queue_entries (q_3)) < (qSize (q_3)))) (PreH9 : (0 <= (queue_entries (q_3)))) (PreH10 : ((queue_entries (q_3)) <= 65535)) (PreH11 : (0 <= (qSize (q_3)))) (PreH12 : ((qSize (q_3)) <= 65535)) (PreH13 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_post_profile sg )) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (pe = (event_addr (sg) (eid)))) (PreH22 : (pe <> 0)) (PreH23 : (valid_event_id sg eid )) (PreH24 : (q_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_post_call_input critical sg caller pe before eid observed )) (PreH27 : (pevent_pre <> 0)) (PreH28 : (0 <= options)) (PreH29 : (options <= 255)) (PreH30 : (0 <= UINT_MAX)) (PreH31 : (0 >= 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (pmsg_pre = message)) (PreH34 : (opt_pre = options)) (PreH35 : (q_post_profile sg )) (PreH36 : (UCOS2_state_inv sg before )) (PreH37 : (q_post_call_input critical sg caller pe before eid observed )) (PreH38 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH39 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH40 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q slots )
|--
  “ ((queue_entries (q)) < (qSize (q))) ” 
  &&  “ ((Z.land opt_pre 2) = 0) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) < 65535) ” 
  &&  “ ((queue_entries (q)) < (qSize (q))) ” 
  &&  “ (((queue_in_addr (q)) + 4 ) <= (queue_end_addr (q))) ” 
  &&  “ ((qStart (q)) <= (q_post_opt_next_out (q))) ” 
  &&  “ ((q_post_opt_next_out (q)) < (queue_end_addr (q))) ” 
  &&  “ ((queue_entries (q_3)) < (qSize (q_3))) ” 
  &&  “ (0 <= (queue_entries (q_3))) ” 
  &&  “ ((queue_entries (q_3)) <= 65535) ” 
  &&  “ (0 <= (qSize (q_3))) ” 
  &&  “ ((qSize (q_3)) <= 65535) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_store_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed current_2 q free slots (qcb_addr (sg) ((qID (q_2)))) )
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&(((qcb_addr (sg) ((qID (q_2)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q slots )
.

Definition OSQPostOpt_partial_solve_wit_25 := OSQPostOpt_partial_solve_wit_25_pure -> OSQPostOpt_partial_solve_wit_25_aux.

Definition OSQPostOpt_partial_solve_wit_26_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (pq: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= (queue_entries (q)))) (PreH5 : ((queue_entries (q)) < 65535)) (PreH6 : ((queue_entries (q)) < (qSize (q)))) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> pq)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (q_post_opt_written_in (options) (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_post_opt_written_out (options) (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) + 1 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (q_post_opt_written_buffer options q message slots )
|--
  “ (pe <> 0) ” 
  &&  “ ((queue_entries (q)) < (qSize (q))) ”
.

Definition OSQPostOpt_partial_solve_wit_26_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (q: QueueFields) (free: (@list Z)) (slots: (@list (@option Z))) (pq: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= (queue_entries (q)))) (PreH5 : ((queue_entries (q)) < 65535)) (PreH6 : ((queue_entries (q)) < (qSize (q)))) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (q_post_opt_written_in (options) (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_post_opt_written_out (options) (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) + 1 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (q_post_opt_written_buffer options q message slots )
|--
  “ (pe <> 0) ” 
  &&  “ ((queue_entries (q)) < (qSize (q))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) < 65535) ” 
  &&  “ ((queue_entries (q)) < (qSize (q))) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ”
  &&  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (q_post_opt_written_in (options) (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_post_opt_written_out (options) (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) + 1 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (q_post_opt_written_buffer options q message slots )
.

Definition OSQPostOpt_partial_solve_wit_26 := OSQPostOpt_partial_solve_wit_26_pure -> OSQPostOpt_partial_solve_wit_26_aux.

Definition OSQPostOpt_partial_solve_wit_27_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q: QueueFields) (pq: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= (queue_entries (q)))) (PreH5 : ((queue_entries (q)) < 65535)) (PreH6 : ((queue_entries (q)) < (qSize (q)))) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "pq" ) )) # Ptr  |-> pq)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 0 )
  **  ((( &( "opt" ) )) # UChar  |-> options)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSQPostOpt_partial_solve_wit_27_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q: QueueFields) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= (queue_entries (q)))) (PreH5 : ((queue_entries (q)) < 65535)) (PreH6 : ((queue_entries (q)) < (qSize (q)))) (PreH7 : (q_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 0 )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) < 65535) ” 
  &&  “ ((queue_entries (q)) < (qSize (q))) ” 
  &&  “ (q_post_opt_safe environment critical sg caller mask pe eid message options before X ) ”
  &&  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 0 )
.

Definition OSQPostOpt_partial_solve_wit_27 := OSQPostOpt_partial_solve_wit_27_pure -> OSQPostOpt_partial_solve_wit_27_aux.

Definition OSQPostOpt_which_implies_wit_1 := 
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

Definition OSQPostOpt_which_implies_wit_1_split_goal_1 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (q_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (q_post_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (valid_event_id sg eid ) ”
.

Definition OSQPostOpt_which_implies_wit_1_split_goal_2 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (q_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (q_post_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSQPostOpt_which_implies_wit_1_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (q_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (q_post_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
.

Definition OSQPostOpt_which_implies_wit_2 := 
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

Definition OSQPostOpt_which_implies_wit_2_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  (q_post_save_pre environment critical saved_local sg caller mask before pe eid observed )
.

Definition OSQPostOpt_which_implies_wit_3 := 
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

Definition OSQPostOpt_which_implies_wit_4 := 
(
forall (message: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (acquired_2) (initial_2)) <> 0)) ,
  (q_post_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
) \/
(
forall (message: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (acquired_2) (initial_2)) <> 0)) ,
  (q_post_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState) ,
  “ ((q_post_group (acquired_2) (initial_2)) = (q_post_group (state) (node))) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node )
).

Definition OSQPostOpt_which_implies_wit_5 := 
(
forall (message: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (node_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (state_2) (node_2)) <> 0)) ,
  (q_post_opt_loop_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 message state_2 node_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state_2) (node_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node tid old )
  **  (event_task_rdy_pre sg (TskState (state)) eid node tid old 4 0 (q_post_sched_group (state)) (q_post_sched_rows (state)) )
) \/
(
forall (message: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (node_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (state_2) (node_2)) <> 0)) ,
  (q_post_opt_loop_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 message state_2 node_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state_2) (node_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node tid old )
  **  (event_task_rdy_pre sg (TskState (state)) eid node tid old 4 0 (q_post_sched_group (state)) (q_post_sched_rows (state)) )
).

Definition OSQPostOpt_which_implies_wit_6 := 
(
forall (message: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (node_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) ,
  (q_post_opt_loop_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 message state_2 node_2 tid old )
  **  (event_task_rdy_post sg (TskState (state_2)) eid node_2 tid old message 4 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
) \/
(
forall (message: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (node_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) ,
  (q_post_opt_loop_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 message state_2 node_2 tid old )
  **  (event_task_rdy_post sg (TskState (state_2)) eid node_2 tid old message 4 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial message state node )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
).

Definition OSQPostOpt_which_implies_wit_7 := 
(
forall (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (node: OSEventAbstractState) (state: UCOS2_Verify_State) (initial: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : ((Z.land options 1) <> 0)) (PreH4 : ((q_post_group (state) (node)) = 0)) ,
  (q_post_opt_loop_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (q_post_opt_schedule_flag (options)) )
) \/
(
forall (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (node: OSEventAbstractState) (state: UCOS2_Verify_State) (initial: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : ((Z.land options 1) <> 0)) (PreH4 : ((q_post_group (state) (node)) = 0)) ,
  (q_post_opt_loop_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (q_post_opt_schedule_flag (options)) )
).

Definition OSQPostOpt_which_implies_wit_8 := 
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

Definition OSQPostOpt_which_implies_wit_9 := 
(
forall (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : ((Z.land options 1) = 0)) ,
  (q_post_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired_2)) eid current tid old message 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (q_post_opt_schedule_flag (options)) )
) \/
(
forall (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : ((Z.land options 1) = 0)) ,
  (q_post_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired_2)) eid current tid old message 4 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (q_post_opt_schedule_flag (options)) )
).

Definition OSQPostOpt_which_implies_wit_10 := 
(
forall (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((Z.land options 4) = 0)) (PreH2 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (q_post_opt_schedule_flag (options)) )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (q_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
) \/
(
forall (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((Z.land options 4) = 0)) (PreH2 : (q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) ,
  (q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (q_post_opt_schedule_flag (options)) )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (q_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
).

Definition OSQPostOpt_which_implies_wit_11 := 
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

Definition OSQPostOpt_which_implies_wit_12 := 
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
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q slots )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q_2: QueueFields) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (pevent: Z) (cpu_sr: Z) (PreH1 : (pq = (qcb_addr (sg) ((qID (q_2)))))) (PreH2 : (pevent = (event_addr (sg) (eid)))) ,
  (q_post_pointer_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 q_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q_2)))))
|--
  EX (x: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) <= 65535) ” 
  &&  “ (0 <= (qSize (q))) ” 
  &&  “ ((qSize (q)) <= 65535) ”
  &&  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> x)
  **  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  (queue_buffer_rep q slots )
).

Definition OSQPostOpt_which_implies_wit_13 := 
(
forall (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : ((queue_entries (q)) >= (qSize (q)))) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q slots )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State) ,
  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired acquired 30 0 )
) \/
(
forall (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : ((queue_entries (q)) >= (qSize (q)))) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q slots )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State) ,
  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired acquired 30 0 )
).

Definition OSQPostOpt_which_implies_wit_14 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q_2)) < (qSize (q_2)))) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 q_2 free_2 slots_2 pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q_2 slots_2 )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ (0 <= (queue_entries (q))) ” 
  &&  “ ((queue_entries (q)) < 65535) ” 
  &&  “ ((queue_entries (q)) < (qSize (q))) ” 
  &&  “ (((queue_in_addr (q)) + 4 ) <= (queue_end_addr (q))) ” 
  &&  “ ((qStart (q)) <= (q_post_opt_next_out (q))) ” 
  &&  “ ((q_post_opt_next_out (q)) < (queue_end_addr (q))) ”
  &&  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q slots )
) \/
(
forall (q_2: QueueFields) (PreH1 : ((queue_entries (q_2)) < (qSize (q_2)))) ,
  TT && emp 
|--
  “ ((q_post_opt_next_out (q_2)) < (queue_end_addr (q_2))) ” 
  &&  “ ((qStart (q_2)) <= (q_post_opt_next_out (q_2))) ” 
  &&  “ (((queue_in_addr (q_2)) + 4 ) <= (queue_end_addr (q_2))) ” 
  &&  “ ((queue_entries (q_2)) < 65535) ” 
  &&  “ (0 <= (queue_entries (q_2))) ”
  &&  emp
).

Definition OSQPostOpt_which_implies_wit_14_split_goal_1 := 
forall (q_2: QueueFields) (PreH1 : ((queue_entries (q_2)) < (qSize (q_2)))) ,
  ((q_post_opt_next_out (q_2)) < (queue_end_addr (q_2)))
.

Definition OSQPostOpt_which_implies_wit_14_split_goal_2 := 
forall (q_2: QueueFields) (PreH1 : ((queue_entries (q_2)) < (qSize (q_2)))) ,
  ((qStart (q_2)) <= (q_post_opt_next_out (q_2)))
.

Definition OSQPostOpt_which_implies_wit_14_split_goal_3 := 
forall (q_2: QueueFields) (PreH1 : ((queue_entries (q_2)) < (qSize (q_2)))) ,
  (((queue_in_addr (q_2)) + 4 ) <= (queue_end_addr (q_2)))
.

Definition OSQPostOpt_which_implies_wit_14_split_goal_4 := 
forall (q_2: QueueFields) (PreH1 : ((queue_entries (q_2)) < (qSize (q_2)))) ,
  ((queue_entries (q_2)) < 65535)
.

Definition OSQPostOpt_which_implies_wit_14_split_goal_5 := 
forall (q_2: QueueFields) (PreH1 : ((queue_entries (q_2)) < (qSize (q_2)))) ,
  (0 <= (queue_entries (q_2)))
.

Definition OSQPostOpt_which_implies_wit_15 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q_2)) < (qSize (q_2)))) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 q_2 free_2 slots_2 pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q_2 slots_2 )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z))) ,
  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (((q_post_opt_next_out (q))) # Ptr  |->_)
  **  (q_post_opt_front_slot_frame q slots )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q_2)) < (qSize (q_2)))) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 q_2 free_2 slots_2 pq )
  **  (queue_buffer_rep q_2 slots_2 )
|--
  EX (x: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z))) ,
  “ ((qStart (q_2)) = (qStart (q))) ” 
  &&  “ ((queue_end_addr (q_2)) = (queue_end_addr (q))) ” 
  &&  “ ((qSize (q_2)) = (qSize (q))) ” 
  &&  “ ((queue_entries (q_2)) = (queue_entries (q))) ” 
  &&  “ ((queue_out_addr (q_2)) = (queue_out_addr (q))) ” 
  &&  “ ((queue_in_addr (q_2)) = (queue_in_addr (q))) ”
  &&  (((q_post_opt_next_out (q))) # Ptr  |-> x)
  **  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  (q_post_opt_front_slot_frame q slots )
).

Definition OSQPostOpt_which_implies_wit_16 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q_2)) < (qSize (q_2)))) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 q_2 free_2 slots_2 pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q_2)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (queue_buffer_rep q_2 slots_2 )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z))) ,
  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (queue_in_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (queue_out_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> (queue_entries (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (((queue_in_addr (q))) # Ptr  |->_)
  **  (q_post_slot_frame q slots )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots_2: (@list (@option Z))) (free_2: (@list Z)) (q_2: QueueFields) (current_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (cpu_sr: Z) (PreH1 : ((queue_entries (q_2)) < (qSize (q_2)))) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current_2 q_2 free_2 slots_2 pq )
  **  (queue_buffer_rep q_2 slots_2 )
|--
  EX (x: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (current: OSEventAbstractState)  (q: QueueFields)  (free: (@list Z))  (slots: (@list (@option Z))) ,
  “ ((qStart (q_2)) = (qStart (q))) ” 
  &&  “ ((queue_end_addr (q_2)) = (queue_end_addr (q))) ” 
  &&  “ ((qSize (q_2)) = (qSize (q))) ” 
  &&  “ ((queue_entries (q_2)) = (queue_entries (q))) ” 
  &&  “ ((queue_out_addr (q_2)) = (queue_out_addr (q))) ” 
  &&  “ ((queue_in_addr (q_2)) = (queue_in_addr (q))) ”
  &&  (((queue_in_addr (q))) # Ptr  |-> x)
  **  (q_post_store_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed current q free slots pq )
  **  (q_post_slot_frame q slots )
).

Definition OSQPostOpt_which_implies_wit_17 := 
(
forall (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : ((queue_entries (q)) < (qSize (q)))) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (q_post_opt_written_in (options) (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_post_opt_written_out (options) (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) + 1 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (q_post_opt_written_buffer options q message slots )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 0 )
) \/
(
forall (options: Z) (message: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (current: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : ((queue_entries (q)) < (qSize (q)))) ,
  (q_post_store_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed current q free slots pq )
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> (q_post_opt_written_in (options) (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> (q_post_opt_written_out (options) (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> ((queue_entries (q)) + 1 ))
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> (qSize (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (queue_end_addr (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> (qStart (q)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  (q_post_opt_written_buffer options q message slots )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (q_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 0 )
).

Module Type VC_Correct.


Axiom proof_of_OSQPostOpt_safety_wit_1 : OSQPostOpt_safety_wit_1.
Axiom proof_of_OSQPostOpt_safety_wit_2 : OSQPostOpt_safety_wit_2.
Axiom proof_of_OSQPostOpt_safety_wit_3 : OSQPostOpt_safety_wit_3.
Axiom proof_of_OSQPostOpt_safety_wit_4 : OSQPostOpt_safety_wit_4.
Axiom proof_of_OSQPostOpt_safety_wit_5 : OSQPostOpt_safety_wit_5.
Axiom proof_of_OSQPostOpt_safety_wit_6 : OSQPostOpt_safety_wit_6.
Axiom proof_of_OSQPostOpt_entail_wit_1 : OSQPostOpt_entail_wit_1.
Axiom proof_of_OSQPostOpt_entail_wit_2 : OSQPostOpt_entail_wit_2.
Axiom proof_of_OSQPostOpt_entail_wit_3 : OSQPostOpt_entail_wit_3.
Axiom proof_of_OSQPostOpt_entail_wit_4 : OSQPostOpt_entail_wit_4.
Axiom proof_of_OSQPostOpt_entail_wit_5 : OSQPostOpt_entail_wit_5.
Axiom proof_of_OSQPostOpt_entail_wit_6 : OSQPostOpt_entail_wit_6.
Axiom proof_of_OSQPostOpt_entail_wit_7 : OSQPostOpt_entail_wit_7.
Axiom proof_of_OSQPostOpt_entail_wit_8_1 : OSQPostOpt_entail_wit_8_1.
Axiom proof_of_OSQPostOpt_entail_wit_8_2 : OSQPostOpt_entail_wit_8_2.
Axiom proof_of_OSQPostOpt_entail_wit_9_1 : OSQPostOpt_entail_wit_9_1.
Axiom proof_of_OSQPostOpt_entail_wit_9_2 : OSQPostOpt_entail_wit_9_2.
Axiom proof_of_OSQPostOpt_entail_wit_9_3 : OSQPostOpt_entail_wit_9_3.
Axiom proof_of_OSQPostOpt_return_wit_1 : OSQPostOpt_return_wit_1.
Axiom proof_of_OSQPostOpt_return_wit_2 : OSQPostOpt_return_wit_2.
Axiom proof_of_OSQPostOpt_return_wit_3 : OSQPostOpt_return_wit_3.
Axiom proof_of_OSQPostOpt_return_wit_4 : OSQPostOpt_return_wit_4.
Axiom proof_of_OSQPostOpt_return_wit_5 : OSQPostOpt_return_wit_5.
Axiom proof_of_OSQPostOpt_return_wit_6 : OSQPostOpt_return_wit_6.
Axiom proof_of_OSQPostOpt_return_wit_7 : OSQPostOpt_return_wit_7.
Axiom proof_of_OSQPostOpt_return_wit_8 : OSQPostOpt_return_wit_8.
Axiom proof_of_OSQPostOpt_partial_solve_wit_1_pure : OSQPostOpt_partial_solve_wit_1_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_1 : OSQPostOpt_partial_solve_wit_1.
Axiom proof_of_OSQPostOpt_partial_solve_wit_2_pure : OSQPostOpt_partial_solve_wit_2_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_2 : OSQPostOpt_partial_solve_wit_2.
Axiom proof_of_OSQPostOpt_partial_solve_wit_3 : OSQPostOpt_partial_solve_wit_3.
Axiom proof_of_OSQPostOpt_partial_solve_wit_4_pure : OSQPostOpt_partial_solve_wit_4_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_4 : OSQPostOpt_partial_solve_wit_4.
Axiom proof_of_OSQPostOpt_partial_solve_wit_5_pure : OSQPostOpt_partial_solve_wit_5_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_5 : OSQPostOpt_partial_solve_wit_5.
Axiom proof_of_OSQPostOpt_partial_solve_wit_6_pure : OSQPostOpt_partial_solve_wit_6_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_6 : OSQPostOpt_partial_solve_wit_6.
Axiom proof_of_OSQPostOpt_partial_solve_wit_7_pure : OSQPostOpt_partial_solve_wit_7_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_7 : OSQPostOpt_partial_solve_wit_7.
Axiom proof_of_OSQPostOpt_partial_solve_wit_8_pure : OSQPostOpt_partial_solve_wit_8_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_8 : OSQPostOpt_partial_solve_wit_8.
Axiom proof_of_OSQPostOpt_partial_solve_wit_9_pure : OSQPostOpt_partial_solve_wit_9_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_9 : OSQPostOpt_partial_solve_wit_9.
Axiom proof_of_OSQPostOpt_partial_solve_wit_10_pure : OSQPostOpt_partial_solve_wit_10_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_10 : OSQPostOpt_partial_solve_wit_10.
Axiom proof_of_OSQPostOpt_partial_solve_wit_11_pure : OSQPostOpt_partial_solve_wit_11_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_11 : OSQPostOpt_partial_solve_wit_11.
Axiom proof_of_OSQPostOpt_partial_solve_wit_12_pure : OSQPostOpt_partial_solve_wit_12_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_12 : OSQPostOpt_partial_solve_wit_12.
Axiom proof_of_OSQPostOpt_partial_solve_wit_13_pure : OSQPostOpt_partial_solve_wit_13_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_13 : OSQPostOpt_partial_solve_wit_13.
Axiom proof_of_OSQPostOpt_partial_solve_wit_14_pure : OSQPostOpt_partial_solve_wit_14_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_14 : OSQPostOpt_partial_solve_wit_14.
Axiom proof_of_OSQPostOpt_partial_solve_wit_15_pure : OSQPostOpt_partial_solve_wit_15_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_15 : OSQPostOpt_partial_solve_wit_15.
Axiom proof_of_OSQPostOpt_partial_solve_wit_16_pure : OSQPostOpt_partial_solve_wit_16_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_16 : OSQPostOpt_partial_solve_wit_16.
Axiom proof_of_OSQPostOpt_partial_solve_wit_17_pure : OSQPostOpt_partial_solve_wit_17_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_17 : OSQPostOpt_partial_solve_wit_17.
Axiom proof_of_OSQPostOpt_partial_solve_wit_18_pure : OSQPostOpt_partial_solve_wit_18_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_18 : OSQPostOpt_partial_solve_wit_18.
Axiom proof_of_OSQPostOpt_partial_solve_wit_19_pure : OSQPostOpt_partial_solve_wit_19_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_19 : OSQPostOpt_partial_solve_wit_19.
Axiom proof_of_OSQPostOpt_partial_solve_wit_20_pure : OSQPostOpt_partial_solve_wit_20_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_20 : OSQPostOpt_partial_solve_wit_20.
Axiom proof_of_OSQPostOpt_partial_solve_wit_21_pure : OSQPostOpt_partial_solve_wit_21_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_21 : OSQPostOpt_partial_solve_wit_21.
Axiom proof_of_OSQPostOpt_partial_solve_wit_22_pure : OSQPostOpt_partial_solve_wit_22_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_22 : OSQPostOpt_partial_solve_wit_22.
Axiom proof_of_OSQPostOpt_partial_solve_wit_23_pure : OSQPostOpt_partial_solve_wit_23_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_23 : OSQPostOpt_partial_solve_wit_23.
Axiom proof_of_OSQPostOpt_partial_solve_wit_24_pure : OSQPostOpt_partial_solve_wit_24_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_24 : OSQPostOpt_partial_solve_wit_24.
Axiom proof_of_OSQPostOpt_partial_solve_wit_25_pure : OSQPostOpt_partial_solve_wit_25_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_25 : OSQPostOpt_partial_solve_wit_25.
Axiom proof_of_OSQPostOpt_partial_solve_wit_26_pure : OSQPostOpt_partial_solve_wit_26_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_26 : OSQPostOpt_partial_solve_wit_26.
Axiom proof_of_OSQPostOpt_partial_solve_wit_27_pure : OSQPostOpt_partial_solve_wit_27_pure.
Axiom proof_of_OSQPostOpt_partial_solve_wit_27 : OSQPostOpt_partial_solve_wit_27.
Axiom proof_of_OSQPostOpt_which_implies_wit_1 : OSQPostOpt_which_implies_wit_1.
Axiom proof_of_OSQPostOpt_which_implies_wit_2 : OSQPostOpt_which_implies_wit_2.
Axiom proof_of_OSQPostOpt_which_implies_wit_3 : OSQPostOpt_which_implies_wit_3.
Axiom proof_of_OSQPostOpt_which_implies_wit_4 : OSQPostOpt_which_implies_wit_4.
Axiom proof_of_OSQPostOpt_which_implies_wit_5 : OSQPostOpt_which_implies_wit_5.
Axiom proof_of_OSQPostOpt_which_implies_wit_6 : OSQPostOpt_which_implies_wit_6.
Axiom proof_of_OSQPostOpt_which_implies_wit_7 : OSQPostOpt_which_implies_wit_7.
Axiom proof_of_OSQPostOpt_which_implies_wit_8 : OSQPostOpt_which_implies_wit_8.
Axiom proof_of_OSQPostOpt_which_implies_wit_9 : OSQPostOpt_which_implies_wit_9.
Axiom proof_of_OSQPostOpt_which_implies_wit_10 : OSQPostOpt_which_implies_wit_10.
Axiom proof_of_OSQPostOpt_which_implies_wit_11 : OSQPostOpt_which_implies_wit_11.
Axiom proof_of_OSQPostOpt_which_implies_wit_12 : OSQPostOpt_which_implies_wit_12.
Axiom proof_of_OSQPostOpt_which_implies_wit_13 : OSQPostOpt_which_implies_wit_13.
Axiom proof_of_OSQPostOpt_which_implies_wit_14 : OSQPostOpt_which_implies_wit_14.
Axiom proof_of_OSQPostOpt_which_implies_wit_15 : OSQPostOpt_which_implies_wit_15.
Axiom proof_of_OSQPostOpt_which_implies_wit_16 : OSQPostOpt_which_implies_wit_16.
Axiom proof_of_OSQPostOpt_which_implies_wit_17 : OSQPostOpt_which_implies_wit_17.

End VC_Correct.
