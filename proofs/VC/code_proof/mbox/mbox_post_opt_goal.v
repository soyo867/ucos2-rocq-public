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
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_post_opt_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSMboxPostOpt -----*)

Definition OSMboxPostOpt_safety_wit_1 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= options)) (PreH2 : (options <= 255)) (PreH3 : (0 <= UINT_MAX)) (PreH4 : (0 >= 0)) (PreH5 : (pevent_pre = pe)) (PreH6 : (pmsg_pre = message)) (PreH7 : (opt_pre = options)) (PreH8 : (mbox_post_profile sg )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH11 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH12 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPostOpt_safety_wit_2 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (pmsg_pre = message)) (PreH8 : (opt_pre = options)) (PreH9 : (mbox_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH12 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH13 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPostOpt_safety_wit_3 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (message <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (mbox_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH16 : (pmsg_pre <> 0)) (PreH17 : (pevent_pre <> 0)) (PreH18 : (0 <= options)) (PreH19 : (options <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (opt_pre = options)) (PreH25 : (mbox_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH28 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH29 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_save_result environment critical saved_local sg caller mask retval before (event_addr (sg) (eid)) message eid )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPostOpt_safety_wit_4 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (0 <= options)) (PreH13 : (options <= 255)) (PreH14 : ((Z.land options 1) <> 0)) (PreH15 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH16 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 0 (mbox_post_opt_schedule_flag (options)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "opt" ) )) # UChar  |-> options)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPostOpt_safety_wit_5 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : ((Z.land options 1) = 0)) (PreH5 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH6 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (mbox_post_opt_schedule_flag (options)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "opt" ) )) # UChar  |-> options)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPostOpt_safety_wit_6 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (m: MboxFields) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (message <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH18 : (pmsg_pre <> 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (0 <= options)) (PreH21 : (options <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (pmsg_pre = message)) (PreH26 : (opt_pre = options)) (PreH27 : (mbox_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH30 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH31 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_message_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 m )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPostOpt_safety_wit_7 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (message <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH18 : (pmsg_pre <> 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (0 <= options)) (PreH21 : (options <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (pmsg_pre = message)) (PreH26 : (opt_pre = options)) (PreH27 : (mbox_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH30 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH31 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 20 0 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPostOpt_safety_wit_8 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (cpu_sr: Z) (PreH1 : ((mbox_message_ptr (m)) = 0)) (PreH2 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 0 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPostOpt_entail_wit_1 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = pe)) (PreH2 : (pmsg_pre = message)) (PreH3 : (opt_pre = options)) (PreH4 : (mbox_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH7 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
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
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (pmsg_pre = message)) (PreH5 : (opt_pre = options)) (PreH6 : (mbox_post_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH9 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ (opt_pre <= 255) ” 
  &&  “ (0 <= opt_pre) ”
  &&  emp
).

Definition OSMboxPostOpt_entail_wit_1_split_goal_1 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (pmsg_pre = message)) (PreH5 : (opt_pre = options)) (PreH6 : (mbox_post_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH9 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (opt_pre <= 255)
.

Definition OSMboxPostOpt_entail_wit_1_split_goal_2 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pevent_pre = pe)) (PreH4 : (pmsg_pre = message)) (PreH5 : (opt_pre = options)) (PreH6 : (mbox_post_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH9 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (0 <= opt_pre)
.

Definition OSMboxPostOpt_entail_wit_2 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH8 : (pmsg_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (0 <= options)) (PreH11 : (options <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (pmsg_pre = message)) (PreH16 : (opt_pre = options)) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH21 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH8 : (pmsg_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (0 <= options)) (PreH11 : (options <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (pmsg_pre = message)) (PreH16 : (opt_pre = options)) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH21 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ”
  &&  emp
).

Definition OSMboxPostOpt_entail_wit_2_split_goal_1 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH8 : (pmsg_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (0 <= options)) (PreH11 : (options <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (pmsg_pre = message)) (PreH16 : (opt_pre = options)) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH21 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((event_slot_type_value ((EventState (before))) (eid)) <= 255)
.

Definition OSMboxPostOpt_entail_wit_2_split_goal_2 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH8 : (pmsg_pre <> 0)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (0 <= options)) (PreH11 : (options <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pevent_pre = pe)) (PreH15 : (pmsg_pre = message)) (PreH16 : (opt_pre = options)) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH21 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (0 <= (event_slot_type_value ((EventState (before))) (eid)))
.

Definition OSMboxPostOpt_entail_wit_3 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (observed_2: OSEventAbstractState) (initial_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((Z.land opt_pre 1) <> 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (message <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH19 : (pmsg_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (mbox_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH31 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_post_opt_loop_context environment critical saved_local sg caller active_2 mask retval pe before acquired_3 eid observed_2 initial_2 message state_2 node_2 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state_2) (node_2)))
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask retval pe before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
.

Definition OSMboxPostOpt_entail_wit_4 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed_2: OSEventAbstractState) (initial_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : ((Z.land options 1) <> 0)) (PreH6 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH7 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_loop_context environment critical saved_local sg caller active_2 mask cpu_sr pe before acquired_2 eid observed_2 initial_2 message state_2 node_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state_2) (node_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
.

Definition OSMboxPostOpt_entail_wit_5 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed_2: OSEventAbstractState) (initial_2: OSEventAbstractState) (state_3: UCOS2_Verify_State) (node_3: OSEventAbstractState) (tid_2: Z) (old_2: TaskAbstractState) (retval: Z) (PreH1 : ((unsigned_last_nbits ((q_post_group (state_2) (node_2))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (0 <= options)) (PreH13 : (options <= 255)) (PreH14 : ((Z.land options 1) <> 0)) (PreH15 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH16 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (event_task_rdy_post sg (TskState (state_3)) eid node_3 tid_2 old_2 message 2 0 (q_post_sched_group (state_3)) (q_post_sched_rows (state_3)) retval )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active_2 mask cpu_sr pe before acquired_2 eid observed_2 initial_2 message state_3 node_3 tid_2 old_2 )
|--
  EX (priority: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old message 2 0 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
.

Definition OSMboxPostOpt_entail_wit_6 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed_2: OSEventAbstractState) (initial_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_post_opt_loop_context environment critical saved_local sg caller active_2 mask cpu_sr pe before acquired_2 eid observed_2 initial_2 message state_2 node_2 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state_2) (node_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
.

Definition OSMboxPostOpt_entail_wit_7 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (observed_2: OSEventAbstractState) (current_3: OSEventAbstractState) (tid_2: Z) (old_2: TaskAbstractState) (retval_2: Z) (PreH1 : ((Z.land opt_pre 1) = 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (message <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH18 : (pmsg_pre <> 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (0 <= options)) (PreH21 : (options <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (pmsg_pre = message)) (PreH26 : (opt_pre = options)) (PreH27 : (mbox_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH30 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH31 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (event_task_rdy_post sg (TskState (acquired_3)) eid current_3 tid_2 old_2 message 2 0 (q_post_sched_group (acquired_3)) (q_post_sched_rows (acquired_3)) retval_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_post_wake_context environment critical saved_local sg caller active_2 mask retval pe message before acquired_3 eid observed_2 current_3 tid_2 old_2 )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  EX (priority: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (current: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) = 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 2 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
.

Definition OSMboxPostOpt_entail_wit_8 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (observed_2: OSEventAbstractState) (current_3: OSEventAbstractState) (m_2: MboxFields) (PreH1 : ((mbox_message_ptr (m_2)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (message <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH19 : (pmsg_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (mbox_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH31 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_post_message_context environment critical saved_local sg caller active_2 mask retval pe message before acquired_3 eid observed_2 current_3 m_2 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m_2)))
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (current: OSEventAbstractState)  (m: MboxFields) ,
  “ ((mbox_message_ptr (m)) = 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  (mbox_post_message_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (current_2: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (observed_2: OSEventAbstractState) (current_3: OSEventAbstractState) (m_2: MboxFields) (PreH1 : ((mbox_message_ptr (m_2)) = 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired_2) (current_2))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (message <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH18 : (pmsg_pre <> 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (0 <= options)) (PreH21 : (options <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (pmsg_pre = message)) (PreH26 : (opt_pre = options)) (PreH27 : (mbox_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH30 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH31 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_message_context environment critical saved_local sg caller active_2 mask retval pe message before acquired_3 eid observed_2 current_3 m_2 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (current: OSEventAbstractState)  (m: MboxFields) ,
  “ (opt_pre = options) ” 
  &&  “ ((event_addr (sg) (eid)) = pe) ” 
  &&  “ ((mbox_message_ptr (m)) = 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ”
  &&  (mbox_post_message_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
).

Definition OSMboxPostOpt_return_wit_1 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) = 0)) (PreH2 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 0 )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) = 0)) (PreH2 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 0 )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
).

Definition OSMboxPostOpt_return_wit_1_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) = 0)) (PreH2 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 0 )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
.

Definition OSMboxPostOpt_return_wit_2 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (message <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH18 : (pmsg_pre <> 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (0 <= options)) (PreH21 : (options <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (pmsg_pre = message)) (PreH26 : (opt_pre = options)) (PreH27 : (mbox_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH30 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH31 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 20 0 )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 20 X )
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (message <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH18 : (pmsg_pre <> 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (0 <= options)) (PreH21 : (options <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (pmsg_pre = message)) (PreH26 : (opt_pre = options)) (PreH27 : (mbox_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH30 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH31 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 20 0 )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 20 X )
).

Definition OSMboxPostOpt_return_wit_2_split_goal_spatial := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (message <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH18 : (pmsg_pre <> 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (0 <= options)) (PreH21 : (options <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (pmsg_pre = message)) (PreH26 : (opt_pre = options)) (PreH27 : (mbox_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH30 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH31 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 20 0 )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 20 X )
.

Definition OSMboxPostOpt_return_wit_3 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
).

Definition OSMboxPostOpt_return_wit_3_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
.

Definition OSMboxPostOpt_return_wit_4 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) = 0)) (PreH7 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) = 0)) (PreH7 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
).

Definition OSMboxPostOpt_return_wit_4_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) = 0)) (PreH7 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
.

Definition OSMboxPostOpt_return_wit_5 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((Z.land options 4) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (0 <= options)) (PreH6 : (options <= 255)) (PreH7 : ((Z.land options 1) <> 0)) (PreH8 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH9 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : ((Z.land options 1) <> 0)) (PreH16 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH17 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 0 (mbox_post_opt_schedule_flag (options)) )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((Z.land options 4) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (0 <= options)) (PreH6 : (options <= 255)) (PreH7 : ((Z.land options 1) <> 0)) (PreH8 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH9 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : ((Z.land options 1) <> 0)) (PreH16 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH17 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 0 (mbox_post_opt_schedule_flag (options)) )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
).

Definition OSMboxPostOpt_return_wit_5_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((Z.land options 4) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (0 <= options)) (PreH6 : (options <= 255)) (PreH7 : ((Z.land options 1) <> 0)) (PreH8 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH9 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : ((Z.land options 1) <> 0)) (PreH16 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH17 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 0 (mbox_post_opt_schedule_flag (options)) )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
.

Definition OSMboxPostOpt_return_wit_6 := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((Z.land options 4) <> 0)) (PreH2 : (pe <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : ((Z.land options 1) = 0)) (PreH6 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH7 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (mbox_post_opt_schedule_flag (options)) )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((Z.land options 4) <> 0)) (PreH2 : (pe <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : ((Z.land options 1) = 0)) (PreH6 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH7 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (mbox_post_opt_schedule_flag (options)) )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
).

Definition OSMboxPostOpt_return_wit_6_split_goal_spatial := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((Z.land options 4) <> 0)) (PreH2 : (pe <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : ((Z.land options 1) = 0)) (PreH6 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH7 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (mbox_post_opt_schedule_flag (options)) )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 0 X )
.

Definition OSMboxPostOpt_return_wit_7 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH11 : (pmsg_pre <> 0)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (pmsg_pre = message)) (PreH19 : (opt_pre = options)) (PreH20 : (mbox_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH23 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH24 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 1 X )
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH11 : (pmsg_pre <> 0)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (pmsg_pre = message)) (PreH19 : (opt_pre = options)) (PreH20 : (mbox_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH23 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH24 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 1 X )
).

Definition OSMboxPostOpt_return_wit_7_split_goal_spatial := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH11 : (pmsg_pre <> 0)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (pmsg_pre = message)) (PreH19 : (opt_pre = options)) (PreH20 : (mbox_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH23 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH24 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 1 X )
.

Definition OSMboxPostOpt_return_wit_8 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pmsg_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pevent_pre = pe)) (PreH8 : (pmsg_pre = message)) (PreH9 : (opt_pre = options)) (PreH10 : (mbox_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH13 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH14 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 3 X )
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pmsg_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pevent_pre = pe)) (PreH8 : (pmsg_pre = message)) (PreH9 : (opt_pre = options)) (PreH10 : (mbox_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH13 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH14 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 3 X )
).

Definition OSMboxPostOpt_return_wit_8_split_goal_spatial := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pmsg_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pevent_pre = pe)) (PreH8 : (pmsg_pre = message)) (PreH9 : (opt_pre = options)) (PreH10 : (mbox_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH13 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH14 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 3 X )
.

Definition OSMboxPostOpt_return_wit_9 := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (pmsg_pre = message)) (PreH8 : (opt_pre = options)) (PreH9 : (mbox_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH12 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH13 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 4 X )
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (pmsg_pre = message)) (PreH8 : (opt_pre = options)) (PreH9 : (mbox_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH12 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH13 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 4 X )
).

Definition OSMboxPostOpt_return_wit_9_split_goal_spatial := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pevent_pre = pe)) (PreH7 : (pmsg_pre = message)) (PreH8 : (opt_pre = options)) (PreH9 : (mbox_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH12 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH13 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  (mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before 4 X )
.

Definition OSMboxPostOpt_partial_solve_wit_1_pure := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pmsg_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pevent_pre = pe)) (PreH8 : (pmsg_pre = message)) (PreH9 : (opt_pre = options)) (PreH10 : (mbox_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH13 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH14 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ”
.

Definition OSMboxPostOpt_partial_solve_wit_1_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pmsg_pre <> 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pevent_pre = pe)) (PreH8 : (pmsg_pre = message)) (PreH9 : (opt_pre = options)) (PreH10 : (mbox_post_profile sg )) (PreH11 : (UCOS2_state_inv sg before )) (PreH12 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH13 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH14 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
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
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  (q_post_closed environment critical saved_local sg caller mask before )
.

Definition OSMboxPostOpt_partial_solve_wit_1 := OSMboxPostOpt_partial_solve_wit_1_pure -> OSMboxPostOpt_partial_solve_wit_1_aux.

Definition OSMboxPostOpt_partial_solve_wit_2_pure := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH11 : (pmsg_pre <> 0)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (pmsg_pre = message)) (PreH19 : (opt_pre = options)) (PreH20 : (mbox_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH23 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH24 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
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

Definition OSMboxPostOpt_partial_solve_wit_2_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : (UCOS2_state_inv sg before )) (PreH10 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH11 : (pmsg_pre <> 0)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (pmsg_pre = message)) (PreH19 : (opt_pre = options)) (PreH20 : (mbox_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH23 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH24 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
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
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
.

Definition OSMboxPostOpt_partial_solve_wit_2 := OSMboxPostOpt_partial_solve_wit_2_pure -> OSMboxPostOpt_partial_solve_wit_2_aux.

Definition OSMboxPostOpt_partial_solve_wit_3 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (message <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (mbox_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH16 : (pmsg_pre <> 0)) (PreH17 : (pevent_pre <> 0)) (PreH18 : (0 <= options)) (PreH19 : (options <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (opt_pre = options)) (PreH25 : (mbox_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH28 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH29 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
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
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_save_pre environment critical saved_local sg caller mask before (event_addr (sg) (eid)) message eid )
.

Definition OSMboxPostOpt_partial_solve_wit_4_pure := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (message <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (mbox_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH16 : (pmsg_pre <> 0)) (PreH17 : (pevent_pre <> 0)) (PreH18 : (0 <= options)) (PreH19 : (options <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (opt_pre = options)) (PreH25 : (mbox_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH28 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH29 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_save_result environment critical saved_local sg caller mask retval before (event_addr (sg) (eid)) message eid )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ”
.

Definition OSMboxPostOpt_partial_solve_wit_4_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (message <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (mbox_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH16 : (pmsg_pre <> 0)) (PreH17 : (pevent_pre <> 0)) (PreH18 : (0 <= options)) (PreH19 : (options <= 255)) (PreH20 : (0 <= UINT_MAX)) (PreH21 : (0 >= 0)) (PreH22 : (pevent_pre = pe)) (PreH23 : (pmsg_pre = message)) (PreH24 : (opt_pre = options)) (PreH25 : (mbox_post_profile sg )) (PreH26 : (UCOS2_state_inv sg before )) (PreH27 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH28 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH29 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH30 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
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
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_post_save_result environment critical saved_local sg caller mask retval before pe message eid )
.

Definition OSMboxPostOpt_partial_solve_wit_4 := OSMboxPostOpt_partial_solve_wit_4_pure -> OSMboxPostOpt_partial_solve_wit_4_aux.

Definition OSMboxPostOpt_partial_solve_wit_5_pure := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : ((Z.land opt_pre 1) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH3 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (message <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH19 : (pmsg_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (mbox_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH31 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) <> 0) ”
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) <> 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (message <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (0 <= options)) (PreH23 : (options <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (pmsg_pre = message)) (PreH28 : (opt_pre = options)) (PreH29 : (mbox_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH32 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH33 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((q_post_group (acquired) (current)) <> 0) ”
).

Definition OSMboxPostOpt_partial_solve_wit_5_pure_split_goal_1 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) <> 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (message <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (0 <= options)) (PreH23 : (options <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (pmsg_pre = message)) (PreH28 : (opt_pre = options)) (PreH29 : (mbox_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH32 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH33 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((q_post_group (acquired) (current)) <> 0) ”
.

Definition OSMboxPostOpt_partial_solve_wit_5_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : ((Z.land opt_pre 1) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH3 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (message <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH19 : (pmsg_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (mbox_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH31 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) <> 0) ” 
  &&  “ ((Z.land opt_pre 1) <> 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
.

Definition OSMboxPostOpt_partial_solve_wit_5 := OSMboxPostOpt_partial_solve_wit_5_pure -> OSMboxPostOpt_partial_solve_wit_5_aux.

Definition OSMboxPostOpt_partial_solve_wit_6_pure := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (0 <= options)) (PreH13 : (options <= 255)) (PreH14 : ((Z.land options 1) <> 0)) (PreH15 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH16 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (state) (node)) <> 0) ”
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  “ ((q_post_group (state) (node)) <> 0) ”
).

Definition OSMboxPostOpt_partial_solve_wit_6_pure_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  “ ((q_post_group (state) (node)) <> 0) ”
.

Definition OSMboxPostOpt_partial_solve_wit_6_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (0 <= options)) (PreH13 : (options <= 255)) (PreH14 : ((Z.land options 1) <> 0)) (PreH15 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH16 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node )
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
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
.

Definition OSMboxPostOpt_partial_solve_wit_6 := OSMboxPostOpt_partial_solve_wit_6_pure -> OSMboxPostOpt_partial_solve_wit_6_aux.

Definition OSMboxPostOpt_partial_solve_wit_7_pure := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (0 <= options)) (PreH6 : (options <= 255)) (PreH7 : ((Z.land options 1) <> 0)) (PreH8 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH9 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : ((Z.land options 1) <> 0)) (PreH16 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH17 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state_2 node_2 tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state_2 node_2 tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
).

Definition OSMboxPostOpt_partial_solve_wit_7_pure_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state_2 node_2 tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
.

Definition OSMboxPostOpt_partial_solve_wit_7_pure_split_goal_2 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state_2 node_2 tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ”
.

Definition OSMboxPostOpt_partial_solve_wit_7_pure_split_goal_3 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state_2 node_2 tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
|--
  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
.

Definition OSMboxPostOpt_partial_solve_wit_7_pure_split_goal_4 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state_2 node_2 tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
|--
  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
.

Definition OSMboxPostOpt_partial_solve_wit_7_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (0 <= options)) (PreH6 : (options <= 255)) (PreH7 : ((Z.land options 1) <> 0)) (PreH8 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH9 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : ((Z.land options 1) <> 0)) (PreH16 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH17 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state_2 node_2 tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
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
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state_2 node_2 tid old )
.

Definition OSMboxPostOpt_partial_solve_wit_7 := OSMboxPostOpt_partial_solve_wit_7_pure -> OSMboxPostOpt_partial_solve_wit_7_aux.

Definition OSMboxPostOpt_partial_solve_wit_8_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (priority: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : ((Z.land options 1) <> 0)) (PreH6 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH7 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old message 2 0 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ”
.

Definition OSMboxPostOpt_partial_solve_wit_8_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (priority: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : ((Z.land options 1) <> 0)) (PreH6 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH7 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old message 2 0 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old message 2 0 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
.

Definition OSMboxPostOpt_partial_solve_wit_8 := OSMboxPostOpt_partial_solve_wit_8_pure -> OSMboxPostOpt_partial_solve_wit_8_aux.

Definition OSMboxPostOpt_partial_solve_wit_9_pure := 
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (0 <= options)) (PreH13 : (options <= 255)) (PreH14 : ((Z.land options 1) <> 0)) (PreH15 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH16 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ ((q_post_group (state) (node)) = 0) ”
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  “ ((q_post_group (state) (node)) = 0) ”
).

Definition OSMboxPostOpt_partial_solve_wit_9_pure_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  “ ((q_post_group (state) (node)) = 0) ”
.

Definition OSMboxPostOpt_partial_solve_wit_9_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (0 <= options)) (PreH13 : (options <= 255)) (PreH14 : ((Z.land options 1) <> 0)) (PreH15 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH16 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node )
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
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
.

Definition OSMboxPostOpt_partial_solve_wit_9 := OSMboxPostOpt_partial_solve_wit_9_pure -> OSMboxPostOpt_partial_solve_wit_9_aux.

Definition OSMboxPostOpt_partial_solve_wit_10_pure := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : ((Z.land opt_pre 1) = 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH3 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (message <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH19 : (pmsg_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (mbox_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH31 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) <> 0) ”
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) = 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (message <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (0 <= options)) (PreH23 : (options <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (pmsg_pre = message)) (PreH28 : (opt_pre = options)) (PreH29 : (mbox_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH32 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH33 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((q_post_group (acquired) (current)) <> 0) ”
).

Definition OSMboxPostOpt_partial_solve_wit_10_pure_split_goal_1 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) = 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (message <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (0 <= options)) (PreH23 : (options <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (pmsg_pre = message)) (PreH28 : (opt_pre = options)) (PreH29 : (mbox_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH32 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH33 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((q_post_group (acquired) (current)) <> 0) ”
.

Definition OSMboxPostOpt_partial_solve_wit_10_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : ((Z.land opt_pre 1) = 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH3 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (message <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH19 : (pmsg_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (mbox_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH31 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) <> 0) ” 
  &&  “ ((Z.land opt_pre 1) = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
.

Definition OSMboxPostOpt_partial_solve_wit_10 := OSMboxPostOpt_partial_solve_wit_10_pure -> OSMboxPostOpt_partial_solve_wit_10_aux.

Definition OSMboxPostOpt_partial_solve_wit_11_pure := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((Z.land opt_pre 1) = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (message <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH19 : (pmsg_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (mbox_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH31 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) = 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (message <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (0 <= options)) (PreH23 : (options <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (pmsg_pre = message)) (PreH28 : (opt_pre = options)) (PreH29 : (mbox_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH32 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH33 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
).

Definition OSMboxPostOpt_partial_solve_wit_11_pure_split_goal_1 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) = 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (message <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (0 <= options)) (PreH23 : (options <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (pmsg_pre = message)) (PreH28 : (opt_pre = options)) (PreH29 : (mbox_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH32 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH33 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
.

Definition OSMboxPostOpt_partial_solve_wit_11_pure_split_goal_2 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) = 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (message <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (0 <= options)) (PreH23 : (options <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (pmsg_pre = message)) (PreH28 : (opt_pre = options)) (PreH29 : (mbox_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH32 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH33 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ”
.

Definition OSMboxPostOpt_partial_solve_wit_11_pure_split_goal_3 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) = 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (message <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (0 <= options)) (PreH23 : (options <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (pmsg_pre = message)) (PreH28 : (opt_pre = options)) (PreH29 : (mbox_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH32 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH33 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
.

Definition OSMboxPostOpt_partial_solve_wit_11_pure_split_goal_4 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((Z.land opt_pre 1) = 0)) (PreH4 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (message <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_post_profile sg )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH11 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (message <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (mbox_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH20 : (pmsg_pre <> 0)) (PreH21 : (pevent_pre <> 0)) (PreH22 : (0 <= options)) (PreH23 : (options <= 255)) (PreH24 : (0 <= UINT_MAX)) (PreH25 : (0 >= 0)) (PreH26 : (pevent_pre = pe)) (PreH27 : (pmsg_pre = message)) (PreH28 : (opt_pre = options)) (PreH29 : (mbox_post_profile sg )) (PreH30 : (UCOS2_state_inv sg before )) (PreH31 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH32 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH33 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH34 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
.

Definition OSMboxPostOpt_partial_solve_wit_11_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((Z.land opt_pre 1) = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (message <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH19 : (pmsg_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (mbox_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH31 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
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
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (event_task_rdy_pre sg (TskState (acquired_2)) eid current_2 tid old 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 tid old )
.

Definition OSMboxPostOpt_partial_solve_wit_11 := OSMboxPostOpt_partial_solve_wit_11_pure -> OSMboxPostOpt_partial_solve_wit_11_aux.

Definition OSMboxPostOpt_partial_solve_wit_12_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (priority: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : ((Z.land options 1) = 0)) (PreH5 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH6 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_wake_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 2 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
|--
  “ (pe <> 0) ” 
  &&  “ ((Z.land options 1) = 0) ”
.

Definition OSMboxPostOpt_partial_solve_wit_12_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (priority: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : ((Z.land options 1) = 0)) (PreH5 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH6 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_wake_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 2 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
|--
  “ (pe <> 0) ” 
  &&  “ ((Z.land options 1) = 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) = 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_wake_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid current tid old message 2 0 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
.

Definition OSMboxPostOpt_partial_solve_wit_12 := OSMboxPostOpt_partial_solve_wit_12_pure -> OSMboxPostOpt_partial_solve_wit_12_aux.

Definition OSMboxPostOpt_partial_solve_wit_13_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (0 <= options)) (PreH13 : (options <= 255)) (PreH14 : ((Z.land options 1) <> 0)) (PreH15 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH16 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (mbox_post_opt_schedule_flag (options)) )
  **  ((( &( "opt" ) )) # UChar  |-> options)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSMboxPostOpt_partial_solve_wit_13_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) <> 0)) (PreH7 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (0 <= options)) (PreH13 : (options <= 255)) (PreH14 : ((Z.land options 1) <> 0)) (PreH15 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH16 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (mbox_post_opt_schedule_flag (options)) )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr (event_addr (sg) (eid)) eid message options before acquired released 0 (mbox_post_opt_schedule_flag (options)) )
.

Definition OSMboxPostOpt_partial_solve_wit_13 := OSMboxPostOpt_partial_solve_wit_13_pure -> OSMboxPostOpt_partial_solve_wit_13_aux.

Definition OSMboxPostOpt_partial_solve_wit_14_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : ((Z.land options 1) = 0)) (PreH5 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH6 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (mbox_post_opt_schedule_flag (options)) )
  **  ((( &( "opt" ) )) # UChar  |-> options)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSMboxPostOpt_partial_solve_wit_14_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : (pe <> 0)) (PreH2 : (0 <= options)) (PreH3 : (options <= 255)) (PreH4 : ((Z.land options 1) = 0)) (PreH5 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH6 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (mbox_post_opt_schedule_flag (options)) )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) = 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (mbox_post_opt_schedule_flag (options)) )
.

Definition OSMboxPostOpt_partial_solve_wit_14 := OSMboxPostOpt_partial_solve_wit_14_pure -> OSMboxPostOpt_partial_solve_wit_14_aux.

Definition OSMboxPostOpt_partial_solve_wit_15_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (PreH1 : ((Z.land options 4) = 0)) (PreH2 : (pe <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : ((Z.land options 1) = 0)) (PreH6 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH7 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (mbox_post_opt_schedule_flag (options)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "opt" ) )) # UChar  |-> options)
|--
  “ ((Z.land options 4) = 0) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ”
.

Definition OSMboxPostOpt_partial_solve_wit_15_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((Z.land options 4) = 0)) (PreH2 : (pe <> 0)) (PreH3 : (0 <= options)) (PreH4 : (options <= 255)) (PreH5 : ((Z.land options 1) = 0)) (PreH6 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH7 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (mbox_post_opt_schedule_flag (options)) )
|--
  “ ((Z.land options 4) = 0) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ ((Z.land options 4) = 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) = 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (mbox_post_opt_schedule_flag (options)) )
.

Definition OSMboxPostOpt_partial_solve_wit_15 := OSMboxPostOpt_partial_solve_wit_15_pure -> OSMboxPostOpt_partial_solve_wit_15_aux.

Definition OSMboxPostOpt_partial_solve_wit_16_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((Z.land options 4) = 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (0 <= options)) (PreH6 : (options <= 255)) (PreH7 : ((Z.land options 1) <> 0)) (PreH8 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH9 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : ((Z.land options 1) <> 0)) (PreH16 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH17 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 0 (mbox_post_opt_schedule_flag (options)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "opt" ) )) # UChar  |-> options)
|--
  “ ((Z.land options 4) = 0) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ”
.

Definition OSMboxPostOpt_partial_solve_wit_16_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (PreH1 : ((Z.land options 4) = 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (0 <= options)) (PreH6 : (options <= 255)) (PreH7 : ((Z.land options 1) <> 0)) (PreH8 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH9 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (0 <= options)) (PreH14 : (options <= 255)) (PreH15 : ((Z.land options 1) <> 0)) (PreH16 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH17 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid message options before 0 (mbox_post_opt_schedule_flag (options)) )
|--
  “ ((Z.land options 4) = 0) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ ((Z.land options 4) = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (mbox_post_opt_schedule_flag (options)) )
.

Definition OSMboxPostOpt_partial_solve_wit_16 := OSMboxPostOpt_partial_solve_wit_16_pure -> OSMboxPostOpt_partial_solve_wit_16_aux.

Definition OSMboxPostOpt_partial_solve_wit_17_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "opt" ) )) # UChar  |-> options)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSMboxPostOpt_partial_solve_wit_17_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (0 <= options)) (PreH7 : (options <= 255)) (PreH8 : ((Z.land options 1) <> 0)) (PreH9 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH10 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (0 <= options)) (PreH15 : (options <= 255)) (PreH16 : ((Z.land options 1) <> 0)) (PreH17 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH18 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored ) ” 
  &&  “ ((Z.land options 4) = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) <> 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
.

Definition OSMboxPostOpt_partial_solve_wit_17 := OSMboxPostOpt_partial_solve_wit_17_pure -> OSMboxPostOpt_partial_solve_wit_17_aux.

Definition OSMboxPostOpt_partial_solve_wit_18_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) = 0)) (PreH7 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "opt" ) )) # UChar  |-> options)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSMboxPostOpt_partial_solve_wit_18_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored )) (PreH2 : ((Z.land options 4) = 0)) (PreH3 : (pe <> 0)) (PreH4 : (0 <= options)) (PreH5 : (options <= 255)) (PreH6 : ((Z.land options 1) = 0)) (PreH7 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH8 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored ) ” 
  &&  “ ((Z.land options 4) = 0) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ ((Z.land options 1) = 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
.

Definition OSMboxPostOpt_partial_solve_wit_18 := OSMboxPostOpt_partial_solve_wit_18_pure -> OSMboxPostOpt_partial_solve_wit_18_aux.

Definition OSMboxPostOpt_partial_solve_wit_19_pure := 
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (message <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH18 : (pmsg_pre <> 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (0 <= options)) (PreH21 : (options <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (pmsg_pre = message)) (PreH26 : (opt_pre = options)) (PreH27 : (mbox_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH30 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH31 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (acquired) (current)) = 0) ”
) \/
(
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (message <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH19 : (pmsg_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (mbox_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH31 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((q_post_group (acquired) (current)) = 0) ”
).

Definition OSMboxPostOpt_partial_solve_wit_19_pure_split_goal_1 := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (message <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH19 : (pmsg_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (mbox_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH31 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((q_post_group (acquired) (current)) = 0) ”
.

Definition OSMboxPostOpt_partial_solve_wit_19_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (message <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH18 : (pmsg_pre <> 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (0 <= options)) (PreH21 : (options <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (pmsg_pre = message)) (PreH26 : (opt_pre = options)) (PreH27 : (mbox_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH30 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH31 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
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
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_group_context environment critical saved_local sg caller active mask retval pe message before acquired eid observed current )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (current)))
.

Definition OSMboxPostOpt_partial_solve_wit_19 := OSMboxPostOpt_partial_solve_wit_19_pure -> OSMboxPostOpt_partial_solve_wit_19_aux.

Definition OSMboxPostOpt_partial_solve_wit_20_pure := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (message <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH19 : (pmsg_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (mbox_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH31 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_message_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 m )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m)))
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ ((mbox_message_ptr (m)) <> 0) ”
.

Definition OSMboxPostOpt_partial_solve_wit_20_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (observed: OSEventAbstractState) (current_2: OSEventAbstractState) (m: MboxFields) (PreH1 : ((mbox_message_ptr (m)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (message <> 0)) (PreH7 : (valid_event_id sg eid )) (PreH8 : (mbox_post_profile sg )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (message <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH19 : (pmsg_pre <> 0)) (PreH20 : (pevent_pre <> 0)) (PreH21 : (0 <= options)) (PreH22 : (options <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pevent_pre = pe)) (PreH26 : (pmsg_pre = message)) (PreH27 : (opt_pre = options)) (PreH28 : (mbox_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH31 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH32 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH33 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
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
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mbox_post_message_context environment critical saved_local sg caller active mask retval pe message before acquired_2 eid observed current_2 m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m)))
.

Definition OSMboxPostOpt_partial_solve_wit_20 := OSMboxPostOpt_partial_solve_wit_20_pure -> OSMboxPostOpt_partial_solve_wit_20_aux.

Definition OSMboxPostOpt_partial_solve_wit_21_pure := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MboxFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (PreH1 : ((mbox_message_ptr (m)) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (message <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH18 : (pmsg_pre <> 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (0 <= options)) (PreH21 : (options <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (pmsg_pre = message)) (PreH26 : (opt_pre = options)) (PreH27 : (mbox_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH30 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH31 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask retval pe eid message options before acquired_2 acquired_2 20 0 )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
|--
  “ (retval = retval) ”
.

Definition OSMboxPostOpt_partial_solve_wit_21_aux := 
forall (opt_pre: Z) (pmsg_pre: Z) (pevent_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (current: OSEventAbstractState) (m: MboxFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (PreH1 : ((mbox_message_ptr (m)) <> 0)) (PreH2 : ((unsigned_last_nbits ((q_post_group (acquired) (current))) (32)) = 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (message <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (message <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH18 : (pmsg_pre <> 0)) (PreH19 : (pevent_pre <> 0)) (PreH20 : (0 <= options)) (PreH21 : (options <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (pmsg_pre = message)) (PreH26 : (opt_pre = options)) (PreH27 : (mbox_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH30 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) (PreH31 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask retval pe eid message options before acquired_2 acquired_2 20 0 )
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
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (message <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (pmsg_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (0 <= options) ” 
  &&  “ (options <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pmsg_pre = message) ” 
  &&  “ (opt_pre = options) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_post_call_input critical sg caller pe message before eid ) ” 
  &&  “ (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask retval (event_addr (sg) (eid)) eid message options before acquired_2 acquired_2 20 0 )
.

Definition OSMboxPostOpt_partial_solve_wit_21 := OSMboxPostOpt_partial_solve_wit_21_pure -> OSMboxPostOpt_partial_solve_wit_21_aux.

Definition OSMboxPostOpt_partial_solve_wit_22_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (m: MboxFields) (cpu_sr: Z) (PreH1 : ((mbox_message_ptr (m)) = 0)) (PreH2 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_message_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> message)
|--
  “ ((mbox_message_ptr (m)) = 0) ”
.

Definition OSMboxPostOpt_partial_solve_wit_22_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (observed: OSEventAbstractState) (current: OSEventAbstractState) (m: MboxFields) (cpu_sr: Z) (PreH1 : ((mbox_message_ptr (m)) = 0)) (PreH2 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  (mbox_post_message_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> message)
|--
  “ ((mbox_message_ptr (m)) = 0) ” 
  &&  “ ((mbox_message_ptr (m)) = 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ”
  &&  (mbox_post_message_context environment critical saved_local sg caller active mask cpu_sr pe message before acquired eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> message)
.

Definition OSMboxPostOpt_partial_solve_wit_22 := OSMboxPostOpt_partial_solve_wit_22_pure -> OSMboxPostOpt_partial_solve_wit_22_aux.

Definition OSMboxPostOpt_partial_solve_wit_23_pure := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : ((mbox_message_ptr (m)) = 0)) (PreH2 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pmsg" ) )) # Ptr  |-> message)
  **  ((( &( "opt" ) )) # UChar  |-> options)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 0 )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSMboxPostOpt_partial_solve_wit_23_aux := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (cpu_sr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (PreH1 : ((mbox_message_ptr (m)) = 0)) (PreH2 : (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X )) ,
  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 0 )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ ((mbox_message_ptr (m)) = 0) ” 
  &&  “ (mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ) ”
  &&  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 0 )
.

Definition OSMboxPostOpt_partial_solve_wit_23 := OSMboxPostOpt_partial_solve_wit_23_pure -> OSMboxPostOpt_partial_solve_wit_23_aux.

Definition OSMboxPostOpt_which_implies_wit_1 := 
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

Definition OSMboxPostOpt_which_implies_wit_1_split_goal_1 := 
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (message <> 0)) (PreH3 : (mbox_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (mbox_post_call_input critical sg caller pe message before eid )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (valid_event_id sg eid ) ”
.

Definition OSMboxPostOpt_which_implies_wit_1_split_goal_2 := 
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (message <> 0)) (PreH3 : (mbox_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (mbox_post_call_input critical sg caller pe message before eid )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMboxPostOpt_which_implies_wit_1_split_goal_spatial := 
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (message <> 0)) (PreH3 : (mbox_post_profile sg )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (mbox_post_call_input critical sg caller pe message before eid )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
.

Definition OSMboxPostOpt_which_implies_wit_2 := 
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

Definition OSMboxPostOpt_which_implies_wit_2_split_goal_spatial := 
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (message <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_post_call_input critical sg caller pe message before eid )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_post_type_context environment saved_local sg caller mask before eid )
|--
  (mbox_post_save_pre environment critical saved_local sg caller mask before pe message eid )
.

Definition OSMboxPostOpt_which_implies_wit_3 := 
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

Definition OSMboxPostOpt_which_implies_wit_4 := 
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial_2: OSEventAbstractState) (observed_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (acquired_2) (initial_2)) <> 0)) ,
  (mbox_post_group_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed_2 initial_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
) \/
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial_2: OSEventAbstractState) (observed_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (acquired_2) (initial_2)) <> 0)) ,
  (mbox_post_group_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed_2 initial_2 )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState) ,
  “ ((q_post_group (acquired_2) (initial_2)) = (q_post_group (state) (node))) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node )
).

Definition OSMboxPostOpt_which_implies_wit_5 := 
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (node_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (observed_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (state_2) (node_2)) <> 0)) ,
  (mbox_post_opt_loop_context environment critical saved_local sg caller active_2 mask cpu_sr pe before acquired_2 eid observed_2 initial_2 message state_2 node_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state_2) (node_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node tid old )
  **  (event_task_rdy_pre sg (TskState (state)) eid node tid old 2 0 (q_post_sched_group (state)) (q_post_sched_rows (state)) )
) \/
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (node_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (observed_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (state_2) (node_2)) <> 0)) ,
  (mbox_post_opt_loop_context environment critical saved_local sg caller active_2 mask cpu_sr pe before acquired_2 eid observed_2 initial_2 message state_2 node_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state_2) (node_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node tid old )
  **  (event_task_rdy_pre sg (TskState (state)) eid node tid old 2 0 (q_post_sched_group (state)) (q_post_sched_rows (state)) )
).

Definition OSMboxPostOpt_which_implies_wit_6 := 
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (node_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (observed_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) ,
  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active_2 mask cpu_sr pe before acquired_2 eid observed_2 initial_2 message state_2 node_2 tid old )
  **  (event_task_rdy_post sg (TskState (state_2)) eid node_2 tid old message 2 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
) \/
(
forall (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (node_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (observed_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) ,
  (mbox_post_opt_loop_wake_context environment critical saved_local sg caller active_2 mask cpu_sr pe before acquired_2 eid observed_2 initial_2 message state_2 node_2 tid old )
  **  (event_task_rdy_post sg (TskState (state_2)) eid node_2 tid old message 2 0 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (observed: OSEventAbstractState)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_post_opt_loop_context environment critical saved_local sg caller active mask cpu_sr pe before acquired eid observed initial message state node )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
).

Definition OSMboxPostOpt_which_implies_wit_7 := 
(
forall (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (node: OSEventAbstractState) (state: UCOS2_Verify_State) (initial: OSEventAbstractState) (observed: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : ((Z.land options 1) <> 0)) (PreH4 : ((q_post_group (state) (node)) = 0)) ,
  (mbox_post_opt_loop_context environment critical saved_local sg caller active_2 mask cpu_sr pe before acquired_2 eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (mbox_post_opt_schedule_flag (options)) )
) \/
(
forall (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (node: OSEventAbstractState) (state: UCOS2_Verify_State) (initial: OSEventAbstractState) (observed: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : ((Z.land options 1) <> 0)) (PreH4 : ((q_post_group (state) (node)) = 0)) ,
  (mbox_post_opt_loop_context environment critical saved_local sg caller active_2 mask cpu_sr pe before acquired_2 eid observed initial message state node )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (mbox_post_opt_schedule_flag (options)) )
).

Definition OSMboxPostOpt_which_implies_wit_8 := 
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

Definition OSMboxPostOpt_which_implies_wit_9 := 
(
forall (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (observed: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : ((Z.land options 1) = 0)) ,
  (mbox_post_wake_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired_2)) eid current tid old message 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (mbox_post_opt_schedule_flag (options)) )
) \/
(
forall (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (current: OSEventAbstractState) (observed: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : ((Z.land options 1) = 0)) ,
  (mbox_post_wake_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed current tid old )
  **  (event_task_rdy_post sg (TskState (acquired_2)) eid current tid old message 2 0 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 (mbox_post_opt_schedule_flag (options)) )
).

Definition OSMboxPostOpt_which_implies_wit_10 := 
(
forall (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((Z.land options 4) = 0)) (PreH2 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (mbox_post_opt_schedule_flag (options)) )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
) \/
(
forall (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((Z.land options 4) = 0)) (PreH2 : (mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before )) ,
  (mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before 0 (mbox_post_opt_schedule_flag (options)) )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before 0 1 returned restored ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
).

Definition OSMboxPostOpt_which_implies_wit_11 := 
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

Definition OSMboxPostOpt_which_implies_wit_12 := 
(
forall (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (current: OSEventAbstractState) (observed: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : ((mbox_message_ptr (m)) <> 0)) ,
  (mbox_post_message_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State) ,
  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired acquired 20 0 )
) \/
(
forall (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (current: OSEventAbstractState) (observed: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : ((mbox_message_ptr (m)) <> 0)) ,
  (mbox_post_message_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (mbox_message_ptr (m)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State) ,
  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired acquired 20 0 )
).

Definition OSMboxPostOpt_which_implies_wit_13 := 
(
forall (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (current: OSEventAbstractState) (observed: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : ((mbox_message_ptr (m)) = 0)) ,
  (mbox_post_message_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> message)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 0 )
) \/
(
forall (options: Z) (message: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (m: MboxFields) (current: OSEventAbstractState) (observed: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : ((mbox_message_ptr (m)) = 0)) ,
  (mbox_post_message_context environment critical saved_local sg caller active_2 mask cpu_sr pe message before acquired_2 eid observed current m )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> message)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (mbox_post_opt_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid message options before acquired released 0 0 )
).

Module Type VC_Correct.


Axiom proof_of_OSMboxPostOpt_safety_wit_1 : OSMboxPostOpt_safety_wit_1.
Axiom proof_of_OSMboxPostOpt_safety_wit_2 : OSMboxPostOpt_safety_wit_2.
Axiom proof_of_OSMboxPostOpt_safety_wit_3 : OSMboxPostOpt_safety_wit_3.
Axiom proof_of_OSMboxPostOpt_safety_wit_4 : OSMboxPostOpt_safety_wit_4.
Axiom proof_of_OSMboxPostOpt_safety_wit_5 : OSMboxPostOpt_safety_wit_5.
Axiom proof_of_OSMboxPostOpt_safety_wit_6 : OSMboxPostOpt_safety_wit_6.
Axiom proof_of_OSMboxPostOpt_safety_wit_7 : OSMboxPostOpt_safety_wit_7.
Axiom proof_of_OSMboxPostOpt_safety_wit_8 : OSMboxPostOpt_safety_wit_8.
Axiom proof_of_OSMboxPostOpt_entail_wit_1 : OSMboxPostOpt_entail_wit_1.
Axiom proof_of_OSMboxPostOpt_entail_wit_2 : OSMboxPostOpt_entail_wit_2.
Axiom proof_of_OSMboxPostOpt_entail_wit_3 : OSMboxPostOpt_entail_wit_3.
Axiom proof_of_OSMboxPostOpt_entail_wit_4 : OSMboxPostOpt_entail_wit_4.
Axiom proof_of_OSMboxPostOpt_entail_wit_5 : OSMboxPostOpt_entail_wit_5.
Axiom proof_of_OSMboxPostOpt_entail_wit_6 : OSMboxPostOpt_entail_wit_6.
Axiom proof_of_OSMboxPostOpt_entail_wit_7 : OSMboxPostOpt_entail_wit_7.
Axiom proof_of_OSMboxPostOpt_entail_wit_8 : OSMboxPostOpt_entail_wit_8.
Axiom proof_of_OSMboxPostOpt_return_wit_1 : OSMboxPostOpt_return_wit_1.
Axiom proof_of_OSMboxPostOpt_return_wit_2 : OSMboxPostOpt_return_wit_2.
Axiom proof_of_OSMboxPostOpt_return_wit_3 : OSMboxPostOpt_return_wit_3.
Axiom proof_of_OSMboxPostOpt_return_wit_4 : OSMboxPostOpt_return_wit_4.
Axiom proof_of_OSMboxPostOpt_return_wit_5 : OSMboxPostOpt_return_wit_5.
Axiom proof_of_OSMboxPostOpt_return_wit_6 : OSMboxPostOpt_return_wit_6.
Axiom proof_of_OSMboxPostOpt_return_wit_7 : OSMboxPostOpt_return_wit_7.
Axiom proof_of_OSMboxPostOpt_return_wit_8 : OSMboxPostOpt_return_wit_8.
Axiom proof_of_OSMboxPostOpt_return_wit_9 : OSMboxPostOpt_return_wit_9.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_1_pure : OSMboxPostOpt_partial_solve_wit_1_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_1 : OSMboxPostOpt_partial_solve_wit_1.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_2_pure : OSMboxPostOpt_partial_solve_wit_2_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_2 : OSMboxPostOpt_partial_solve_wit_2.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_3 : OSMboxPostOpt_partial_solve_wit_3.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_4_pure : OSMboxPostOpt_partial_solve_wit_4_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_4 : OSMboxPostOpt_partial_solve_wit_4.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_5_pure : OSMboxPostOpt_partial_solve_wit_5_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_5 : OSMboxPostOpt_partial_solve_wit_5.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_6_pure : OSMboxPostOpt_partial_solve_wit_6_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_6 : OSMboxPostOpt_partial_solve_wit_6.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_7_pure : OSMboxPostOpt_partial_solve_wit_7_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_7 : OSMboxPostOpt_partial_solve_wit_7.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_8_pure : OSMboxPostOpt_partial_solve_wit_8_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_8 : OSMboxPostOpt_partial_solve_wit_8.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_9_pure : OSMboxPostOpt_partial_solve_wit_9_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_9 : OSMboxPostOpt_partial_solve_wit_9.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_10_pure : OSMboxPostOpt_partial_solve_wit_10_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_10 : OSMboxPostOpt_partial_solve_wit_10.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_11_pure : OSMboxPostOpt_partial_solve_wit_11_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_11 : OSMboxPostOpt_partial_solve_wit_11.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_12_pure : OSMboxPostOpt_partial_solve_wit_12_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_12 : OSMboxPostOpt_partial_solve_wit_12.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_13_pure : OSMboxPostOpt_partial_solve_wit_13_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_13 : OSMboxPostOpt_partial_solve_wit_13.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_14_pure : OSMboxPostOpt_partial_solve_wit_14_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_14 : OSMboxPostOpt_partial_solve_wit_14.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_15_pure : OSMboxPostOpt_partial_solve_wit_15_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_15 : OSMboxPostOpt_partial_solve_wit_15.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_16_pure : OSMboxPostOpt_partial_solve_wit_16_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_16 : OSMboxPostOpt_partial_solve_wit_16.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_17_pure : OSMboxPostOpt_partial_solve_wit_17_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_17 : OSMboxPostOpt_partial_solve_wit_17.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_18_pure : OSMboxPostOpt_partial_solve_wit_18_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_18 : OSMboxPostOpt_partial_solve_wit_18.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_19_pure : OSMboxPostOpt_partial_solve_wit_19_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_19 : OSMboxPostOpt_partial_solve_wit_19.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_20_pure : OSMboxPostOpt_partial_solve_wit_20_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_20 : OSMboxPostOpt_partial_solve_wit_20.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_21_pure : OSMboxPostOpt_partial_solve_wit_21_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_21 : OSMboxPostOpt_partial_solve_wit_21.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_22_pure : OSMboxPostOpt_partial_solve_wit_22_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_22 : OSMboxPostOpt_partial_solve_wit_22.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_23_pure : OSMboxPostOpt_partial_solve_wit_23_pure.
Axiom proof_of_OSMboxPostOpt_partial_solve_wit_23 : OSMboxPostOpt_partial_solve_wit_23.
Axiom proof_of_OSMboxPostOpt_which_implies_wit_1 : OSMboxPostOpt_which_implies_wit_1.
Axiom proof_of_OSMboxPostOpt_which_implies_wit_2 : OSMboxPostOpt_which_implies_wit_2.
Axiom proof_of_OSMboxPostOpt_which_implies_wit_3 : OSMboxPostOpt_which_implies_wit_3.
Axiom proof_of_OSMboxPostOpt_which_implies_wit_4 : OSMboxPostOpt_which_implies_wit_4.
Axiom proof_of_OSMboxPostOpt_which_implies_wit_5 : OSMboxPostOpt_which_implies_wit_5.
Axiom proof_of_OSMboxPostOpt_which_implies_wit_6 : OSMboxPostOpt_which_implies_wit_6.
Axiom proof_of_OSMboxPostOpt_which_implies_wit_7 : OSMboxPostOpt_which_implies_wit_7.
Axiom proof_of_OSMboxPostOpt_which_implies_wit_8 : OSMboxPostOpt_which_implies_wit_8.
Axiom proof_of_OSMboxPostOpt_which_implies_wit_9 : OSMboxPostOpt_which_implies_wit_9.
Axiom proof_of_OSMboxPostOpt_which_implies_wit_10 : OSMboxPostOpt_which_implies_wit_10.
Axiom proof_of_OSMboxPostOpt_which_implies_wit_11 : OSMboxPostOpt_which_implies_wit_11.
Axiom proof_of_OSMboxPostOpt_which_implies_wit_12 : OSMboxPostOpt_which_implies_wit_12.
Axiom proof_of_OSMboxPostOpt_which_implies_wit_13 : OSMboxPostOpt_which_implies_wit_13.

End VC_Correct.
